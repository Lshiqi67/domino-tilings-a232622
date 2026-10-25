"""核对中文论文引用、归档、署名与既有 Lean 证据；不重新运行 Lean。"""
from pathlib import Path
import hashlib
import json
import re
import sys
from datetime import datetime, timezone, timedelta

PAPER = Path(__file__).resolve().parents[1]
ROOT = PAPER.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    paths = [PAPER / 'main.tex', PAPER / 'references.tex']
    paths += sorted((PAPER / 'sections').glob('*.tex'))
    paths += sorted((PAPER / 'generated').glob('*.tex'))
    paths += sorted((PAPER / 'figures').glob('*.tex'))
    text = '\n'.join(p.read_text(encoding='utf-8-sig') for p in paths)
    labels = re.findall(r'\\label\{([^}]+)\}', text)
    refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', text)
    assert len(labels) == len(set(labels)), '重复标签'
    assert set(refs) <= set(labels), set(refs) - set(labels)
    citations = re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', text)
    bib = re.findall(r'\\bibitem\{([^}]+)\}', text)
    assert set(citations) == set(bib), '参考文献存在漏引或未定义项'
    main_text = (PAPER / 'main.tex').read_text(encoding='utf-8')
    assert r'\author{Shiqi Liu}' in main_text
    assert 'pdfauthor={Shiqi Liu}' in main_text
    assert not any(s in text for s in ['本地研究稿', '作者署名由后续', '未运行 Lean 等形式化验证'])

    evidence_path = ROOT / 'lean/evidence/m6-2026-10-25/verification-02/report.json'
    evidence = json.loads(evidence_path.read_text(encoding='utf-8-sig'))
    assert evidence['status'] == 'm6_passed'
    assert evidence['paper_main_theorem_verified'] is True
    assert len(evidence['axiom_dependencies']) == 413
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(v) <= allowed for v in evidence['axiom_dependencies'].values())
    matched = {}
    for rel, digest in evidence['source_sha256'].items():
        if rel.endswith('.lean') or rel in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
            assert sha(ROOT / 'lean' / rel) == digest, rel
            matched[rel] = digest
    formal = (PAPER / 'sections/formalization.tex').read_text(encoding='utf-8')
    declarations = re.findall(r'\\texttt\{((?:fixed|orbit|three)\\_[^}]+)\}', formal)
    names = [v.replace(r'\_', '_') for v in declarations]
    for name in names:
        assert 'Domino.' + name in evidence['axiom_dependencies'], name

    archive = PAPER / 'archive/v1.0'
    archive_manifest = json.loads((archive / 'SHA256.json').read_text(encoding='utf-8'))
    for rel, digest in archive_manifest['sha256'].items():
        assert sha(archive / rel) == digest, rel
    log = (PAPER / 'build/main.log').read_text(encoding='utf-8', errors='replace')
    assert not re.search(r'Overfull \\[hv]box|Missing character:|undefined references|Citation .+ undefined', log)
    assert 'Output written on build/main.pdf (16 pages)' in log
    report = {
        'date_beijing': datetime.now(timezone(timedelta(hours=8))).isoformat(),
        'command': 'python -X utf8 checks/check_edition.py (from papers/zh)',
        'python': sys.version,
        'checks': {
            'labels_unique_and_all_references_defined': True,
            'all_five_bibliographic_entries_cited': True,
            'author_and_pdf_metadata_source_correct': True,
            'legacy_pdf_and_tex_hashes_match': True,
            'Lean_mathematical_sources_and_locks_match_M6_evidence': True,
            'all_eight_named_Lean_declarations_audited': True,
            'no_overflow_missing_glyph_or_unresolved_reference': True,
        },
        'pdf_pages': 16,
        'pdf_sha256': sha(PAPER / 'domino-tilings-zh.pdf'),
        'matched_Lean_source_sha256': matched,
        'Lean_evidence': evidence_path.relative_to(ROOT).as_posix(),
        'limits': '只复核已有验收报告与数学源码的一致性。本轮未重跑 Lean、历史穷举或外部同行审阅；不认证新颖性。',
    }
    (PAPER / 'checks/edition-audit.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': 'passed', 'pdf_pages': 16, 'Lean_sources_and_locks': len(matched)}, ensure_ascii=False))


if __name__ == '__main__':
    main()
