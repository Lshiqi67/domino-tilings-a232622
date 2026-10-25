"""核对 M1–M6 审阅包；--lean 执行固定模块构建及类型/公理探针。"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone, timedelta

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[1]
LEAN = ROOT / 'lean'


def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def verify():
    manifest = read(PACK / 'source-manifest.json')
    catalog = read(LEAN / 'docs/m6-declarations.json')
    history = read(LEAN / 'evidence/m6-2026-10-25/verification-02/report.json')
    mapping = read(PACK / 'mapping.json')
    assert history['status'] == 'm6_passed'
    assert len(catalog['modules']) == 32 and len(catalog['declarations']) == 413
    for rel, expected in manifest['source_files'].items():
        assert digest(ROOT / rel) == expected, ('source changed', rel)
    declarations = {d['name']: d for d in catalog['declarations']}
    selected = set()
    for row in mapping['rows']:
        assert row['external_review'] == 'pending', row['id']
        for name in row['declarations']:
            d = declarations[name]
            line = (LEAN / d['file']).read_text(encoding='utf-8-sig').splitlines()[d['line'] - 1]
            assert re.search(r'\b' + re.escape(name.removeprefix('Domino.')) + r'\b', line), name
            assert name in history['axiom_dependencies'], name
            selected.add(name)
    modules = {rel[:-5].replace('/', '.'): rel for rel in catalog['modules']}
    graph = {}
    for name, rel in modules.items():
        assert digest(LEAN / rel) == history['source_sha256'][rel], rel
        imports = re.findall(r'^(?:public )?import (Domino(?:\.[A-Za-z0-9_]+)*)\s*$',
                             (LEAN / rel).read_text(encoding='utf-8-sig'), re.M)
        assert set(imports) <= set(modules), (name, imports)
        graph[name] = imports
    for filename in ['Probe.lean', 'Axioms.lean']:
        imports = re.findall(r'^import (Domino(?:\.[A-Za-z0-9_]+)*)\s*$',
                             (PACK / filename).read_text(encoding='utf-8'), re.M)
        assert set(imports) == set(modules), filename
    actual_axioms = re.findall(r'^#print axioms (\S+)', (PACK / 'Axioms.lean').read_text(encoding='utf-8'), re.M)
    assert set(actual_axioms) == set(declarations) and len(actual_axioms) == 413
    checks = re.findall(r'^#check (\S+)', (PACK / 'Probe.lean').read_text(encoding='utf-8'), re.M)
    assert set(checks) == selected
    return {'scope': 'M1-M6', 'static_checks_passed': True,
            'semantic_items': len(mapping['rows']), 'mapped_declarations': len(selected),
            'mathematical_modules': 32, 'audit_declarations': 413,
            'source_manifest_sha256': digest(PACK / 'source-manifest.json'),
            'import_graph': graph,
            'external_semantic_review': 'pending'}, list(modules)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', action='store_true')
    ap.add_argument('--output', help='New output directory, relative to repository root')
    args = ap.parse_args()
    report, modules = verify()
    report['date_beijing'] = datetime.now(timezone(timedelta(hours=8))).isoformat()
    report['python'] = sys.version.split()[0]
    report['random_seed'] = None
    report['lean_executed'] = False
    report['commands'] = []
    out = (ROOT / args.output).resolve() if args.output else None
    if args.lean:
        if out is None:
            stamp = datetime.now(timezone(timedelta(hours=8))).strftime('%Y%m%d-%H%M%S')
            out = PACK / 'checks' / ('run-' + stamp)
        out.mkdir(parents=True, exist_ok=False)
        report['lean_executed'] = True
        commands = [
            ('lean-version', ['lake', 'env', 'lean', '--version']),
            ('mathlib-revision', ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']),
            ('build', ['lake', '--wfail', 'build', *modules]),
            ('types', ['lake', 'env', 'lean', '-DwarningAsError=true', '../review/m1-m6/Probe.lean']),
            ('axioms', ['lake', 'env', 'lean', '-DwarningAsError=true', '../review/m1-m6/Axioms.lean']),
        ]
        try:
            for label, argv in commands:
                proc = subprocess.run(argv, cwd=LEAN, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                      encoding='utf-8', errors='replace')
                (out / (label + '.txt')).write_text(proc.stdout, encoding='utf-8')
                report['commands'].append({'name': label, 'argv': argv, 'cwd': 'lean', 'exit_code': proc.returncode})
                if proc.returncode:
                    raise RuntimeError(f'{label} failed: see {out / (label + ".txt")}')
                if label == 'lean-version':
                    assert '4.35.0' in proc.stdout, proc.stdout
                if label == 'mathlib-revision':
                    assert proc.stdout.strip() == '56a005855ea17e0b0958f73ec801ae140b0a1679'
            content = (out / 'axioms.txt').read_text(encoding='utf-8')
            entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", content)
            catalog = read(LEAN / 'docs/m6-declarations.json')
            assert {name for name, _ in entries} == {d['name'] for d in catalog['declarations']}
            allowed = {'propext', 'Classical.choice', 'Quot.sound'}
            dependencies = {name: [v.strip() for v in names.split(',') if v.strip()] for name, names in entries}
            assert all(set(v) <= allowed for v in dependencies.values())
            history = read(LEAN / 'evidence/m6-2026-10-25/verification-02/report.json')
            assert {k: set(v) for k, v in dependencies.items()} == {k: set(v) for k, v in history['axiom_dependencies'].items()}
            report['axiom_dependencies_match_M6'] = True
            report['allowed_axioms'] = sorted(allowed)
            report['status'] = 'passed'
        except Exception as exc:
            report['status'] = 'failed'
            report['failure'] = str(exc)
            raise
        finally:
            report['limits'] = '固定 M1–M6 模块增量构建、声明类型和公理输出；不是新的独立干净重建、有限铺法穷举或外部人工语义审阅。'
            report['probe_sha256'] = {n: digest(PACK / n) for n in ['Probe.lean', 'Axioms.lean', 'mapping.json', 'check_pack.py']}
            (out / 'report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    elif out:
        out.mkdir(parents=True, exist_ok=False)
        (out / 'report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'import_graph' and k != 'commands'}, ensure_ascii=False))


if __name__ == '__main__':
    main()
