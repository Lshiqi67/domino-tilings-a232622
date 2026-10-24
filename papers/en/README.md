# English working draft

**Shiqi Liu**

**Unfinished research. No solution of the A232622 conjecture is claimed. The manuscript needs further refinement, and correctness still requires Lean formalization and verification. No Lean verification has been completed.**

- [Read the PDF](domino-tilings-en.pdf).
- [Edit the LaTeX source](main.tex).
- [Current scientific status](../../STATUS.md).
- [Selected research notes](../../docs/en/statement.md).
- [Programs and scope](../../research/README.md).

This public version adds a draft notice and revised abstract. Existing mathematical statements remain proposed arguments for examination. It includes an AI-use disclosure and makes no priority claim.

Build with Python, SymPy and TeX Live (or another installation providing amsart, Latin Modern, microtype, mathtools, booktabs, enumitem and TikZ):

~~~powershell
./build.ps1
~~~

The script audits transcribed formulas against the preserved numerical certificates, runs pdfLaTeX twice and checks for unresolved references, missing glyphs and overflow. These checks are not Lean verification.

For a portable command-line build, run python checks/prepare_and_audit.py, create build/, then invoke pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex twice. Copy build/main.pdf to domino-tilings-en.pdf.
