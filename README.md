# Domino tilings · OEIS A232622

**Shiqi Liu**

> **Work in progress. This research is unfinished. No claim is made that the A232622 conjecture has been solved. The manuscripts need further refinement, and correctness still requires Lean formalization and verification, together with mathematical review. No Lean verification has been completed.**
>
> **研究尚未完成，不宣称已经解决 A232622 猜想。论文仍需打磨，证明准确性还需 Lean 形式化验证及数学审阅；目前尚未完成 Lean 验证。**

## The problem / 研究问题

[OEIS A232622](https://oeis.org/A232622) counts incongruent domino tilings of a **3 × 2n rectangle**, identifying tilings under horizontal reflection, vertical reflection and a half-turn. Dominoes are unlabelled and may have either orientation; there is no tatami restriction. The empty tiling counts once.

本项目研究三行、偶数列矩形铺法在完整矩形对称群下的轨道数。材料探索不可竖切基本块、Burnside 引理、半棋盘边界状态和转移矩阵，也记录奇数高度及五行情形的候选推广。

The repository contains proposed arguments, finite computations and exact algebraic checks. A formula agreeing with tested values is not a proof for all board sizes. Statements headed “Theorem” or “Proof” in the drafts remain claims under review, not Lean-certified results. An OEIS conjecture label does not establish global open status or originality.

## Read the drafts / 阅读材料

| Material | English | 中文 |
| --- | --- | --- |
| Manuscript PDF | [Working draft](papers/en/domino-tilings-en.pdf) | [原中文论文，未修改](papers/zh/domino-tilings-zh.pdf) |
| Source and edition notes | [LaTeX and build](papers/en/README.md) | [源码与版本说明](papers/zh/README.md) |
| Exact problem | [Statement](docs/en/statement.md) | [题面](docs/zh/statement.md) |
| Approaches | [Routes](docs/en/approaches.md) | [思路](docs/zh/approaches.md) |
| Source notes | [References](docs/en/references.md) | [文献](docs/zh/references.md) |
| Lemma register | [Draft lemmas](docs/en/lemmas.md) | [引理记录](docs/zh/lemmas.md) |
| Block route | [Draft argument](docs/en/blocks-proof.md) | [基本块草稿](docs/zh/blocks-proof.md) |
| Half-rectangle route | [Draft argument](docs/en/half-board-proof.md) | [半棋盘草稿](docs/zh/half-board-proof.md) |

The Chinese manuscript and its TeX sources are preserved unchanged. They retain the wording of their earlier draft. **The current research status is the unfinished status stated above and in [STATUS.md](STATUS.md); the historical wording is not an announcement that the conjecture is solved.**

中文论文保留原文件内容，不回写历史版本。其“完整推导”等措辞应理解为待审草稿中的论证主张，不能视为研究完成、猜想已解决或形式化验证通过。

## Reproduce and review / 复现与审阅

- [Programs, computational scope and commands / 程序、范围与命令](research/README.md)
- [New reproduction runs / 本轮复现结果](REPRODUCTION.md)
- [Lean verification plan / Lean 验证计划](lean/README.md)
- [Review questions / 审阅重点](REVIEW.md)
- [Publication selection and privacy / 公开材料与隐私处理](PUBLICATION.md)

The mathematical drafts and verification programs were developed with substantial AI assistance. Numerical and algebraic checks have limited scopes and do not substitute for formal verification or independent mathematical review. The bibliographic novelty of the specific arguments and formulas is not established.

Public visibility gives visitors read and fork access. It does not grant write access to this repository. No collaborator write permissions are intended; proposed corrections must be reviewed before the owner incorporates them.

Keywords: domino tilings, A232622, three-row rectangle, incongruent tilings, symmetry classes, Burnside lemma, generating functions, transfer matrices, odd height, Lean verification pending.
