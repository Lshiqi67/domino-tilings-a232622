# Public-copy reproduction / 公开副本复现

Date: 2026-10-25. These are new publication-preparation runs, separate from the sanitized historical reports. The six historical Python source files are unchanged. The commands were run from a temporary copy of the research directory, with Python 3.13.0 and SymPy 1.13.1 on Windows. All calculations were deterministic; no random seed applies.

**Research remains unfinished. These runs do not establish a solution of the conjecture or Lean verification.**

| Program | Actual scope | Result | Elapsed seconds |
| --- | --- | --- | --- |
| verify_blocks.py | All 40,545 three-row tilings, n=0–8; blocks and symmetries | Passed | 17.044 |
| derive_functions.py | Exact three/five-row expressions; coefficient/matrix comparison n=0–100 | Passed | 2.345 |
| verify_geometry.py | 57,468 tilings at the four stated odd-height ranges | Passed | 2.549 |
| five_row_certificate.py | Exact reduced five-row certificate and full-matrix agreement | Passed | 1.433 |

The exact reproduction commands and required order appear in [research/README.md](research/README.md). Detailed new outputs stay in the ignored temporary working copy because they contain local invocation metadata. The public historical reports were not overwritten. Formula transcription checks and the English PDF build also passed.

本轮确实在公开材料的临时副本中重新运行了上述程序；不是把旧报告改日期。结果只支持所列范围，不替代一般证明、Lean 形式化或独立数学审阅。数学研究仍未完成，论文仍需修订。
