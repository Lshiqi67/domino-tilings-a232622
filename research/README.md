# Computation and reproduction / 计算与复现

**Research unfinished; conjecture not claimed solved; Lean verification pending.**

The original relative layout is retained so the historical programs can locate their dependencies. The six selected Python sources are unchanged. Numerical reports are sanitized historical copies, not new runs. Working-directory, invocation and platform fields were removed; numerical values and original source hashes were preserved.

Python 3.13.0 and SymPy 1.13.1 were used for the recorded runs. These deterministic checks use exact arithmetic, not random sampling or floating-point fitting.

## Recorded scopes

| Check | Scope | What it supports |
| --- | --- | --- |
| Screening | Three rows, n=0–8 | Fixed-point and canonical-orbit counts using one enumerator |
| Block route | Three rows, n=0–8, 40,545 tilings | Block reconstruction, four symmetry actions, exact rational identities |
| Half-rectangle route | Heights 1,3 through n=8; height 5 through n=4; height 7 through n=2; 57,468 tilings | Geometric fixed counts, reconstruction and specified stabilizers |
| Symbolic transfer | Heights 3,5; exact resolvents and coefficients n=0–100 | Model algebra and expression agreement |
| Five-row certificate | Reduced six-dimensional matrices and exact polynomial identity | Finite algebra for the stated model |

The n≤100 comparison is **not** enumeration of every tiling at those sizes. None of these checks validates the infinite-parameter combinatorial reasoning in Lean. The programs were developed with AI assistance.

## Programs

- [Historical enumerator](01_topics/checks/a232622-screening/check_tilings.py)
- [Block verification](02_problems/P002-domino-orbit-counting/attempts/A001-irreducible-blocks/checks/verify_blocks.py)
- [General transfer model](02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/transfer_core.py)
- [Exact generating functions](02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/derive_functions.py)
- [Separate geometric enumerator](02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/verify_geometry.py)
- [Reduced five-row certificate](02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/five_row_certificate.py)

## Reproduction

**Run in a temporary copy.** Some unchanged historical programs write their report beside the source and include the local invocation/working directory. Do not publish those generated files without removing private metadata.

From the repository root in PowerShell:

~~~powershell
New-Item -ItemType Directory -Force tmp | Out-Null
Copy-Item -LiteralPath research -Destination tmp/repro -Recurse
Set-Location tmp/repro
python 02_problems/P002-domino-orbit-counting/attempts/A001-irreducible-blocks/checks/verify_blocks.py --max-n 8 --output 02_problems/P002-domino-orbit-counting/attempts/A001-irreducible-blocks/checks/new-report.json
python 02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/derive_functions.py
python 02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/verify_geometry.py
python 02_problems/P002-domino-orbit-counting/attempts/A002-half-board-transfer/checks/five_row_certificate.py
~~~

Use a fresh tmp/repro directory for each independent rerun. The symbolic script should precede the reduced-certificate script, which reads its report. A001's original sanitized report remains the reference for A002's historical comparison.

## 说明

这些程序及输出是辅助检查，不是 Lean 证明。有限枚举只能支持明确列出的尺寸；符号恒等式只能验证输入模型的代数关系。原始代码中的中文注释说明了这一范围。公开 JSON 明确标注隐私字段清理，未把旧运行伪装成新实验。

复现时务必使用临时副本，避免覆盖公开的历史报告。若另行上传新结果，应再次检查其中的本机路径与身份信息。当前所有一般性证明仍为待进一步验证的草稿。
