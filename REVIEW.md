# Review guide / 审阅说明

**本轮入口：[M1–M6 外部语义审阅包](review/m1-m6/README.md)**。包含 25 项论文—代码对应、固定源码摘要、152 个声明定位、413 项公理探针和待外部填写的审阅表。英文 v2.0、中文 v2.1 已展开 E04；旧版保留在论文 archive 目录。本文以下通用审阅问题继续适用，外部审阅尚未完成。

The three-row half-board route now has Lean M1–M6 evidence under explicit tiling and coordinate-symmetry definitions; see the [verified scope](lean/docs/m6-main-theorem.md). Historical manuscript arguments and unformalized extensions still require review. **The whole paper, the block-route second proof and novelty claims are not certified.**

Review the original three-row problem before its extensions. Check the exact unlabelled tiling model, the four-element group, empty and small boards, exhaustive block classification, decomposition uniqueness, actions on blocks of unequal width, and possible central blocks. For half-rectangle constructions, check necessity, sufficiency, injectivity and surjectivity, including dominoes crossing the symmetry axis.

Then check exact stabilizers, the probability space used for asymptotics, all odd-height assumptions and the meaning of reduced five-row variables and terminal weights. A reduced variable counts one state, not a whole reversal orbit. Check the full polynomial identity, not merely many coefficients.

Report each objection with a precise file/statement/equation, its reason and a counterexample or repair where possible. Distinguish a mathematical error, missing justification, presentation problem and a step actually verified. If you run code, record command, environment, scope and actual results. Do not infer a general proof from a finite pass.

Formalization should begin from the definitions, not from the desired formula as an axiom. No use of sorry, admitted, or untracked assumptions may be presented as completed verification. Record remaining gaps and the exact Lean/mathlib versions.

请先审查三行原题，再审查推广，分别判断逻辑正确性、形式化覆盖范围与文献新颖性。若未发现问题，应说明实际审阅范围及仍未确定之处，不能写成“论文已认证”。其他研究者的结果应准确引用，不能仅据 OEIS 的猜想标签或一次未检索到证明便主张首次解决。

Earlier AI-assisted checks suggested clarifying the horizontal-reflection term in the source-variable substitution, avoiding reuse of b_n for two sequences, and citing DeFord's general symmetry-recurrence work. The English public draft incorporates those editorial points; they do not establish a completed proof or novelty.
