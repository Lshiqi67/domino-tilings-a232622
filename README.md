# Domino tilings · OEIS A232622

**Shiqi Liu**

> **Lean M1 through M6 now verify the three-row main counting theorem locally: the generating function for actual tiling orbits, the seventh-order recurrence for every index, and all seven initial values. The project has also undergone a clean rebuild of its own sources. Extensions, the second block-based proof and external mathematical review remain unfinished; no priority or novelty claim is made.**
>
> **Lean M1–M6 已本地验证三行主计数定理：实际铺法轨道的主生成函数、全部指标七阶递推及七项初值，并完成项目源码的独立干净重建。全文扩展、基本块第二证明和外部人工审阅仍待完成，不主张文献首次性。**

## The problem / 研究问题

[OEIS A232622](https://oeis.org/A232622) counts incongruent domino tilings of a **3 × 2n rectangle**, identifying tilings under horizontal reflection, vertical reflection and a half-turn. Dominoes are unlabelled and may have either orientation; there is no tatami restriction. The empty tiling counts once.

本项目研究三行、偶数列矩形铺法在指定四种坐标对称下的轨道数。材料探索不可竖切基本块、Burnside 引理、半棋盘边界状态和转移矩阵，也记录奇数高度及五行情形的候选推广。

The repository contains proposed arguments, finite computations, exact algebraic checks and the explicitly listed Lean M1–M6 results. A formula agreeing with tested values is not a proof for all board sizes. Headings such as “Theorem” or “Proof” in the drafts do not by themselves establish formal verification; the verified scope is tracked separately in the Lean project. An OEIS conjecture label does not establish global open status or originality.

## Read the drafts / 阅读材料

| Material | English | 中文 |
| --- | --- | --- |
| Manuscript PDF | [English v2.0 (15 pages)](papers/en/domino-tilings-en.pdf) | [中文论文 v2.1（17 页）](papers/zh/domino-tilings-zh.pdf) |
| Illustrated block-proof guide (10 pages) | [English PDF](guides/block-proof/domino-block-proof-guide-en.pdf) | [中文图解讲义](guides/block-proof/domino-block-proof-guide-zh.pdf) |
| Source and edition notes | [LaTeX and build](papers/en/README.md) | [源码与版本说明](papers/zh/README.md) |
| Exact problem | [Statement](docs/en/statement.md) | [题面](docs/zh/statement.md) |
| Approaches | [Routes](docs/en/approaches.md) | [思路](docs/zh/approaches.md) |
| Source notes | [References](docs/en/references.md) | [文献](docs/zh/references.md) |
| Lemma register | [Draft lemmas](docs/en/lemmas.md) | [引理记录](docs/zh/lemmas.md) |
| Block route | [Draft argument](docs/en/blocks-proof.md) | [基本块草稿](docs/zh/blocks-proof.md) |
| Half-rectangle route | [Draft argument](docs/en/half-board-proof.md) | [半棋盘草稿](docs/zh/half-board-proof.md) |

The Chinese manuscript v2.1 incorporates the verified scope of Lean M1–M6, improves notation and bibliographic context, and supplies reproducible build instructions. The unchanged v1.0 PDF and TeX sources remain in [the archive](papers/zh/archive/v1.0/). See [edition notes](papers/zh/README.md).

中文论文 v2.1 署名 Shiqi Liu，纳入三行主定理的形式化成果，补充相关前作并修订数学表述。旧版原字节归档。全文扩展的形式化、外部数学审阅及文献优先权核查仍待完成。

**2026-10-25 可读性修订：**中英文稿均展开 E04 的状态支持归纳、来源求和及矩阵系数解释。英文 v1.0、中文 v2.0 的 PDF/TeX/原检查保存在各自 archive 目录，中文 v1.0 继续保留。新增 [M1–M6 外部语义审阅包](review/m1-m6/README.md)：25 项逐项对应、固定源码与可执行探针，外部审阅仍待完成。

## Reproduce and review / 复现与审阅

- [Programs, computational scope and commands / 程序、范围与命令](research/README.md)
- [New reproduction runs / 本轮复现结果](REPRODUCTION.md)
- [Lean project and half-rectangle formalization plan / 固定版本项目与半棋盘形式化方案](lean/README.md)（M1–M6 三行主计数定理已通过本地构建、公理审计与干净项目重建）
- [Lean progress and roadmap / 已取得成果与 M7–M11 待办](lean/docs/progress.md)
- [M6 main theorem and evidence / M6 三行主定理与证据](lean/docs/m6-main-theorem.md)
- [M4/M5 historical scope / M4/M5 历史范围](lean/docs/m4-m5-counting.md)
- [M3 historical scope / M3 历史范围](lean/docs/m3-completion.md)
- [M2 historical scope / M2 历史范围](lean/docs/m2-paths.md)
- [Review questions / 审阅重点](REVIEW.md)
- [Publication selection and privacy / 公开材料与隐私处理](PUBLICATION.md)

The mathematical drafts and verification programs were developed with substantial AI assistance. Numerical and algebraic checks have limited scopes and do not substitute for formal verification or independent mathematical review. The bibliographic novelty of the specific arguments and formulas is not established.

Public visibility gives visitors read and fork access. It does not grant write access to this repository. No collaborator write permissions are intended; proposed corrections must be reviewed before the owner incorporates them.

Keywords: domino tilings, A232622, three-row rectangle, incongruent tilings, symmetry classes, Burnside lemma, generating functions, transfer matrices, odd height, Lean verified three-row counting theorem.
