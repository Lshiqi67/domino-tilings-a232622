# Lean verification pending / Lean 验证待完成

**No Lean formalization or successful verification is supplied.** This directory is a plan, not a proof certificate. The work and manuscripts remain unfinished, and the repository does not claim that the conjecture is solved.

Proposed sequence:

1. Fix and record Lean and mathlib versions. Define a finite rectangular cell set, adjacency, dominoes and tilings as exact covers or perfect matchings.
2. Define the four symmetries and their action on tilings, including the separately specified empty object. Relate the definition to the original unlabelled problem.
3. Prove the local column-profile correspondence and completeness of the transition rule.
4. Formalize one global route first: either first-return blocks/unique decomposition or half-rectangle completion and its inverse.
5. Connect fixed-point counts to finite orbit counting and formal power series.
6. Verify the target rational expression and recurrence, then separately formalize the refinements and extensions.
7. Record successful build commands, dependency versions, theorem coverage and any remaining assumptions or unformalized sections.

The five-row polynomial certificate is finite algebra, but formalizing only that identity would not validate the combinatorial model or the original conjecture. A completed build must not hide gaps behind sorry, admitted declarations or unjustified axioms.

本目录不含声称通过的 Lean 文件，不以计划或占位文件充当验证。首先需要把原题的计数对象和量词准确形式化，再核查双射、群作用和代数推导。精确数值与符号计算不能替代这些步骤。即使完成某个有限代数引理，也必须明确尚未覆盖的组合论证。
