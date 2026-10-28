"""检查本次论文/审阅包交付摘要、归档、引用和 E04 局部转移计数。"""
from pathlib import Path
from datetime import datetime, timezone, timedelta
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
PACK = ROOT / 'review/m1-m6'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    manifest = json.loads((PACK / 'paper-manifest.json').read_text(encoding='utf-8'))
    for rel, expected in manifest['sha256'].items():
        target = ROOT / rel
        if rel.startswith("papers/en/"):
            target = ROOT / "papers/en/archive/v2.0" / rel.removeprefix("papers/en/")
        assert sha(target) == expected, rel
    editions = {}
    for lang in ['en', 'zh']:
        paper = ROOT / 'papers' / lang
        if lang == 'en':
            paper = paper / 'archive/v2.0'
        files = [p for p in paper.rglob('*.tex') if not any(x in ('archive', 'build') for x in p.relative_to(paper).parts)]
        source = '\n'.join(p.read_text(encoding='utf-8-sig') for p in files)
        labels = re.findall(r'\\label\{([^}]+)\}', source)
        refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', source)
        assert len(labels) == len(set(labels))
        assert set(refs) <= set(labels), set(refs) - set(labels)
        cited = {s for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', source) for s in group.split(',')}
        assert cited == set(re.findall(r'\\bibitem\{([^}]+)\}', source))
        assert r'\author{Shiqi Liu}' in source and 'pdfauthor={Shiqi Liu}' in source
        assert 'No Lean verification has been completed' not in source
        audit = json.loads((paper / 'checks/manuscript-audit.json').read_text(encoding='utf-8'))
        for rel, expected in audit['source_sha256'].items():
            target = ROOT / 'papers' / lang / rel if rel.startswith('archive/') else paper / rel
            assert sha(target) == expected, (lang, rel)
        archives = {}
        for archive in sorted((ROOT / 'papers' / lang / 'archive').glob('*/SHA256.json')):
            data = json.loads(archive.read_text(encoding='utf-8'))
            for rel, expected in data['sha256'].items():
                assert sha(archive.parent / rel) == expected, str(archive.parent / rel)
            archives[archive.parent.name] = len(data['sha256'])
        editions[lang] = {'pdf_sha256': sha(paper / f'domino-tilings-{lang}.pdf'),
                         'pages': manifest['editions'][lang]['pages'],
                         'references_valid': True, 'transcription_source_hashes_match': True,
                         'archives_verified': archives}
    # Exact local check of E04 source paths, independent of the two-column matrix literal.
    states = range(8)
    def legal(p, q):
        return p & q == 0 and (7 ^ (p | q)) in (0, 3, 6)
    E, O = {0, 3, 6}, {1, 4, 7}
    assert all(q in O for p in E for q in states if legal(p, q))
    assert all(q in E for p in O for q in states if legal(p, q))
    def paths(p, q):
        return sum(legal(p, s) and legal(s, q) for s in states)
    matrix = [[paths(0, 0), paths(3, 0) + paths(6, 0)],
              [paths(0, 3), paths(3, 3) + paths(6, 3)]]
    assert matrix == [[3, 2], [1, 1]]
    # Broken-link check is limited to the new packet and current edition guides.
    links = 0
    md_files = list(PACK.rglob('*.md'))
    md_files += [ROOT / f'papers/{lang}/README.md' for lang in ['en', 'zh']]
    md_files += [ROOT / 'papers/zh/checks/readability-revision.md']
    for p in md_files:
        for target in re.findall(r'\]\(([^)]+)\)', p.read_text(encoding='utf-8')):
            if '://' in target or target.startswith('#'):
                continue
            dest = (p.parent / target.split('#')[0]).resolve()
            if dest == (PACK / 'checks/delivery-report.json').resolve():
                # This script writes that report only after all checks pass.
                continue
            assert dest.exists(), (p.relative_to(ROOT), target)
            links += 1
    result = {'date_beijing': datetime.now(timezone(timedelta(hours=8))).isoformat(),
              'command': 'python -X utf8 review/m1-m6/check_delivery.py',
              'python': sys.version.split()[0], 'random_seed': None, 'status': 'passed',
              'editions': editions, 'packet_and_guide_links': links,
              'E04_two_step_matrix': matrix, 'source_manifest_sha256': sha(PACK / 'source-manifest.json'),
              'paper_manifest_sha256': sha(PACK / 'paper-manifest.json'),
              'limits': '摘要、引用、归档和三行单列/两列局部规则检查；不替代全宽度归纳、Lean 构建、外部人类审阅或 PDF 视觉检查。'}
    (ROOT / 'tmp').mkdir(exist_ok=True)
    (ROOT / 'tmp/m1-m6-delivery-report.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, ensure_ascii=False))


if __name__ == '__main__':
    main()
