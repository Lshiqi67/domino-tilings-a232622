# Domino Tilings of Odd-Height Rectangles up to Symmetry

**Shiqi Liu** · [GitHub](https://github.com/Lshiqi67)

Domino tilings, symmetry classes, generating functions, and Lean formalization, starting from the three-row counting problem associated with **[OEIS A232622](https://oeis.org/A232622)**.

[English manuscript](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/papers/en/domino-tilings-en.pdf) · [Archived release](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.0) · [Lean project](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/lean) · [Citation](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/CITATION.cff)

**English** · [完整中文版](#中文版)

## Overview

This repository contains manuscripts, two combinatorial proof routes, reproducible computations, and Lean proofs for counting domino tilings modulo rectangle symmetries.

The starting problem counts tilings of a $3\times 2n$ rectangle up to horizontal reflection, vertical reflection, and a half-turn. The project also studies exact symmetry types, asymptotic behavior, arbitrary fixed positive odd heights, and an explicit five-row case.

**Current status — October 26, 2026:** Lean milestones **M1–M11** have passed the recorded local cumulative verification, including declaration audits and a clean rebuild of the project sources. The repository contains **83 mathematical modules and 1,078 audited declarations**, including 699 theorems and auxiliary lemmas.

The English manuscript is **v2.0**, and the Chinese manuscript is **v2.1**. Their formalization summaries cover **M1–M6**; the repository includes the subsequent **M7–M11** developments.

## Mathematical problem and main result

Let $a(n)$ denote the number of equivalence classes of domino tilings of a $3\times 2n$ rectangle under the four coordinate symmetries

$$
G=\{e,h,v,hv\}\cong C_2\times C_2,
$$

where $h$ reverses the rows and $v$ reverses the columns.

Dominoes are unlabelled, both orientations are allowed, and every cell is covered exactly once. There is no tatami restriction. The empty board contributes $a(0)=1$.

The three-row generating function is

$$
\sum_{n\ge 0}a(n)x^n
=
\frac{1-3x-4x^2+10x^3-4x^5+x^6}
{(1-x)(1-4x+x^2)(1-4x^2+x^4)}.
$$

Here $n$ is the **half-width** of the board, and the identity is interpreted in the formal power-series ring $\mathbb{Q}[[x]]$.

Equivalently, for every $n\ge 0$,

$$
\begin{aligned}
a(n+7)={}&5a(n+6)-a(n+5)-19a(n+4)\\
&+19a(n+3)+a(n+2)-5a(n+1)+a(n),
\end{aligned}
$$

with initial values

$$
a(0),\ldots,a(6)=1,\ 2,\ 5,\ 14,\ 46,\ 156,\ 561.
$$

The next value is $a(7)=2037$. These statements are derived in Lean from the defined tiling and orbit counts.

### Two proof routes

- **Half-rectangle transfer:** encode geometric tilings by boundary-state paths, prove symmetry-preserving completion and restriction correspondences, and apply Burnside’s lemma.
- **Indecomposable blocks:** classify blocks separated by vertical cuts, prove unique decomposition, translate geometric symmetries into operations on block words, and count the corresponding palindromes.

The routes share foundational definitions, parts of the geometric path theory, Burnside’s lemma, and algebraic tools. Their distinct combinatorial arguments provide a cross-check within the project.

## Formalized results

| Milestone | Scope | Documentation |
| --- | --- | --- |
| M1–M6 | Tiling definitions, geometric path equivalences, symmetry completion, Burnside counting, the three-row generating function, seventh-order recurrence, and initial values | [Three-row main theorem](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m6-main-theorem.md) |
| M7 | Exact three-row stabilizers, orbit sizes, and counts by symmetry type | [Stabilizers and odd heights](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m7-m8-stabilizers-odd-height.md) |
| M8 | Counting formulas, rational generating functions, and eventual linear recurrences for every fixed positive odd height | [Stabilizers and odd heights](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m7-m8-stabilizers-odd-height.md) |
| M9 | Explicit five-row generating function, a reduced algebraic certificate, a fourteenth-order recurrence, and initial values | [Five-row certificate](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m9-five-row-certificate.md) |
| M10 | Three-row closed forms, orbit asymptotics, symmetry probabilities under uniform tiling and uniform orbit sampling, and exponential error bounds | [Asymptotics and probability](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m10-asymptotics-probability.md) |
| M11 | Complete block classification, unique decomposition, word symmetries, palindrome counting, and a second proof of the main generating function | [Block proof](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m11-block-route.md) |

See the [progress summary](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/progress.md) for precise scope and theorem entry points.

## Manuscripts and reading guide

| Resource | English | Chinese |
| --- | --- | --- |
| Manuscript | [v2.0 · 15 pages](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/papers/en/domino-tilings-en.pdf) | [v2.1 · 17 pages](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/papers/zh/domino-tilings-zh.pdf) |
| LaTeX sources and build instructions | [English edition](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/papers/en) | [Chinese edition](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/papers/zh) |
| Illustrated block-proof guide | [English PDF](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/guides/block-proof/domino-block-proof-guide-en.pdf) | [Chinese PDF](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/guides/block-proof/domino-block-proof-guide-zh.pdf) |

For an introduction, start with the manuscript or illustrated guide. For verification, continue with the [Lean project](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/lean), its milestone documentation, and the [M1–M6 manuscript-to-code review package](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/review/m1-m6).

Earlier manuscripts and research notes retain their historical scope statements. For the current formalization status, use [STATUS.md](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/STATUS.md) and the Lean progress summary.

## Reproducing the verification

### Lean

Requirements: Git, Lean/Lake managed through elan, and Python 3. The project pins:

- **Lean:** `leanprover/lean4:v4.35.0`
- **mathlib:** `56a005855ea17e0b0958f73ec801ae140b0a1679`
- Other dependencies through `lean/lake-manifest.json`.

```bash
git clone -c core.longpaths=true https://github.com/Lshiqi67/domino-tilings-a232622.git
cd domino-tilings-a232622/lean

lake exe cache get
lake --wfail build
python -X utf8 scripts/check_m11.py --report-dir checks/m11-first-run
```

Use `python3` if required by your system. The report directory must not already exist. A successful run exits with code `0` and reports **`m11_passed`**.

The cumulative check runs earlier milestone checks, audits the declarations, and rebuilds the project in a fresh directory using the verified dependency cache. It does not rebuild all of mathlib from source. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

See the [full setup instructions](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/README.md), [recorded verification report](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/evidence/m11-rerun-20261025-232056/report.json), and [GitHub Actions](https://github.com/Lshiqi67/domino-tilings-a232622/actions/workflows/lean.yml).

### Computational checks

The repository also provides finite tiling enumerators, exact transfer-matrix calculations, and polynomial certificates. Recorded runs used **Python 3.13.0** and **SymPy 1.13.1**.

Follow the [computational reproduction instructions](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/research/README.md). Run historical scripts in a temporary copy because some write reports beside their source files. Enumeration supports only the stated finite ranges; it is separate from the general Lean proofs.

## Repository layout

```text
papers/                  English and Chinese manuscripts, sources, and archives
guides/                  Illustrated explanation of the block proof
lean/                    Formal proofs, pinned dependencies, checks, and evidence
docs/                    Earlier proof drafts, statements, and reference notes
research/                Computational programs and recorded outputs
review/                  Manuscript-to-code review materials
releases/                Versioned release notes
STATUS.md                Current scope and outstanding work
REPRODUCTION.md          Recorded computational reproduction
ARCHIVING.md             Backup and restoration instructions
CITATION.cff              Structured citation metadata
CITATION.bib              BibTeX citation
MANIFEST-SHA256.json      Published file checksums
```

## Review and remaining work

The next priorities are external human review of the correspondence between the manuscripts and formal definitions, and an update of the manuscripts’ formalization summaries.

Further work includes asymptotics beyond three rows and minimal recurrence orders; the five-row fourteenth-order recurrence is provided without a minimality claim. The formal model uses the specified coordinate symmetries and does not separately formalize a classification of all Euclidean isometries.

The manuscripts, programs, and formalization were developed with substantial AI assistance. Recorded Lean checks establish results within their formal definitions and assumptions. External review and bibliographic novelty assessment remain outstanding; this repository makes no claim of first discovery or first proof.

Corrections are welcome through [GitHub Issues](https://github.com/Lshiqi67/domino-tilings-a232622/issues). Please identify the relevant manuscript section, theorem, or file and include a reproducible example where applicable.

## Citation and versioned archive

To cite the English manuscript, use **Shiqi Liu, _Domino tilings of odd-height rectangles up to symmetry_, version 2.0, 2026**.

```bibtex
@unpublished{liu2026domino,
  author = {Liu, Shiqi},
  title = {Domino tilings of odd-height rectangles up to symmetry},
  year = {2026},
  version = {2.0},
  note = {Preprint, manuscript dated October 25, 2026;
          GitHub release dated October 26, 2026},
  url = {https://github.com/Lshiqi67/domino-tilings-a232622/releases/download/paper-en-v2.0/domino-tilings-en-v2.0.pdf}
}
```

The [archived release `paper-en-v2.0`](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.0) includes the English PDF, a public source snapshot, a Git history bundle, and checksums. When referring to formalization results, also identify the relevant repository tag or commit.

---

# 中文版

## 奇数高度矩形的多米诺铺法：对称计数与形式化证明

**Shiqi Liu** · [GitHub](https://github.com/Lshiqi67)

本项目从 **[OEIS A232622](https://oeis.org/A232622)** 对应的三行矩形计数问题出发，研究多米诺铺法的对称分类、生成函数及 Lean 形式化证明。

[中文论文](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/papers/zh/domino-tilings-zh.pdf) · [英文论文归档](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.0) · [Lean 项目](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/lean) · [引用信息](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/CITATION.cff)

## 项目概述

本仓库提供论文、两条组合证明路线、可复现计算程序和 Lean 证明，用于研究矩形多米诺铺法在对称作用下的轨道计数。

起点是 $3\times 2n$ 矩形：将上下反射、左右反射及半周旋转所得铺法视为等价。研究进一步涉及精确对称类型、渐近行为、任意固定正奇数高度，以及五行情形的显式公式。

**当前状态——2026 年 10 月 26 日：** Lean **M1–M11** 已通过已记录的本地累计验收，包括声明公理审计和项目源码干净重建。仓库包含 **83 个数学模块、1078 项受审计声明**，其中有 699 个定理及辅助引理。

当前英文论文为 **v2.0**，中文论文为 **v2.1**。这两个版本中的形式化说明覆盖 **M1–M6**；仓库另已收录后续 **M7–M11** 的成果。

## 数学问题与主要结果

记 $a(n)$ 为 $3\times 2n$ 矩形的多米诺铺法在以下四种坐标对称下的等价类数：

$$
G=\{e,h,v,hv\}\cong C_2\times C_2,
$$

其中 $h$ 表示上下反射，$v$ 表示左右反射。

多米诺不带标签，允许横放和竖放，每个格子恰好被覆盖一次，不施加 tatami 限制。空棋盘约定为 $a(0)=1$。

三行轨道数的生成函数为

$$
\sum_{n\ge 0}a(n)x^n
=
\frac{1-3x-4x^2+10x^3-4x^5+x^6}
{(1-x)(1-4x+x^2)(1-4x^2+x^4)}.
$$

这里 $n$ 表示棋盘的**半宽**；等式在形式幂级数环 $\mathbb{Q}[[x]]$ 中解释。

等价地，对所有 $n\ge 0$，

$$
\begin{aligned}
a(n+7)={}&5a(n+6)-a(n+5)-19a(n+4)\\
&+19a(n+3)+a(n+2)-5a(n+1)+a(n),
\end{aligned}
$$

初值为

$$
a(0),\ldots,a(6)=1,\ 2,\ 5,\ 14,\ 46,\ 156,\ 561.
$$

下一项为 $a(7)=2037$。这些结论在 Lean 中从所定义的实际铺法及轨道计数推导得到。

### 两条证明路线

- **半棋盘转移路线：** 将几何铺法编码为边界状态路径，证明对称补全与限制的对应关系，再应用 Burnside 引理。
- **不可分基本块路线：** 分类由竖直断口分隔的基本块，证明唯一分解，将几何对称转化为块字上的操作，再进行回文计数。

两条路线共享基础定义、部分几何路径理论、Burnside 引理和代数工具；不同的组合论证构成项目内部的方法交叉核验。

## 已形式化的结果

| 阶段 | 验证范围 | 详细说明 |
| --- | --- | --- |
| M1–M6 | 铺法定义、几何路径双射、对称补全、Burnside 计数、三行主生成函数、七阶递推及初值 | [三行主定理](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m6-main-theorem.md) |
| M7 | 三行精确稳定子、轨道大小及按对称类型分类的计数 | [稳定子与奇数高度](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m7-m8-stabilizers-odd-height.md) |
| M8 | 任意固定正奇数高度的计数公式、生成函数有理性及最终线性递推 | [稳定子与奇数高度](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m7-m8-stabilizers-odd-height.md) |
| M9 | 五行显式生成函数、压缩代数证书、十四阶递推及完整初值 | [五行证书](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m9-five-row-certificate.md) |
| M10 | 三行闭式、轨道渐近、均匀铺法与均匀轨道抽样下的对称概率、指数误差界 | [渐近与概率](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m10-asymptotics-probability.md) |
| M11 | 基本块完整分类、唯一分解、字对称、回文计数及主生成函数的第二条证明 | [基本块证明](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/m11-block-route.md) |

精确范围及主要定理入口见[阶段成果汇总](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/docs/progress.md)。

## 论文与阅读指南

| 材料 | 英文版 | 中文版 |
| --- | --- | --- |
| 论文 | [v2.0 · 15 页](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/papers/en/domino-tilings-en.pdf) | [v2.1 · 17 页](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/papers/zh/domino-tilings-zh.pdf) |
| LaTeX 源码及构建说明 | [英文目录](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/papers/en) | [中文目录](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/papers/zh) |
| 基本块证明图解 | [英文 PDF](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/guides/block-proof/domino-block-proof-guide-en.pdf) | [中文 PDF](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/guides/block-proof/domino-block-proof-guide-zh.pdf) |

初次阅读可从论文或图解讲义开始。希望核验结果的读者，可继续阅读 [Lean 项目](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/lean)、各阶段说明及 [M1–M6 论文—代码语义审阅包](https://github.com/Lshiqi67/domino-tilings-a232622/tree/main/review/m1-m6)。

旧论文与研究笔记保留其形成时的状态说明。当前形式化进展以 [STATUS.md](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/STATUS.md) 和 Lean 阶段成果汇总为准。

## 复现验证

### Lean 验证

需要 Git、通过 elan 管理的 Lean/Lake，以及 Python 3。项目固定以下版本：

- **Lean：** `leanprover/lean4:v4.35.0`
- **mathlib：** `56a005855ea17e0b0958f73ec801ae140b0a1679`
- 其他依赖由 `lean/lake-manifest.json` 锁定。

```bash
git clone -c core.longpaths=true https://github.com/Lshiqi67/domino-tilings-a232622.git
cd domino-tilings-a232622/lean

lake exe cache get
lake --wfail build
python -X utf8 scripts/check_m11.py --report-dir checks/m11-first-run
```

部分系统需将 `python` 改为 `python3`。报告目录必须尚不存在。成功验收时，程序退出码为 `0`，并输出 **`m11_passed`**。

累计验收会运行先前阶段检查、审计声明，并在新目录中使用已核对的依赖缓存重新构建项目。这不包括从源码重新编译整个 mathlib。允许的公理为 `propext`、`Classical.choice` 和 `Quot.sound`。

完整说明见[运行指南](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/README.md)、[已保存的验收报告](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/lean/evidence/m11-rerun-20261025-232056/report.json)及 [GitHub Actions](https://github.com/Lshiqi67/domino-tilings-a232622/actions/workflows/lean.yml)。

### 计算检查

仓库另提供有限铺法枚举、精确转移矩阵计算及多项式证书。已记录运行使用 **Python 3.13.0** 和 **SymPy 1.13.1**。

操作步骤见[计算复现说明](https://github.com/Lshiqi67/domino-tilings-a232622/blob/main/research/README.md)。部分历史程序会在源码旁写入报告，应在临时副本中运行。枚举结果仅支持明确列出的有限范围，与一般性的 Lean 证明分别记录。

## 仓库结构

```text
papers/                  中英文论文、源码及历史版本
guides/                  基本块证明图解
lean/                    形式化证明、固定依赖、验收脚本及证据
docs/                    早期证明草稿、题面及文献笔记
research/                计算程序和历史输出
review/                  论文与代码对应的审阅材料
releases/                版本发布说明
STATUS.md                当前验证范围及待办
REPRODUCTION.md          已记录的计算复现
ARCHIVING.md             备份与恢复说明
CITATION.cff              结构化引用信息
CITATION.bib              BibTeX 引用
MANIFEST-SHA256.json      公开文件校验清单
```

## 审阅与后续工作

下一步重点是取得外部人工语义审阅，核对论文陈述与形式化定义的对应关系，并更新论文中的形式化覆盖说明。

后续研究包括三行以外的渐近行为和最小递推阶数；目前提供五行十四阶递推，不主张其阶数最小。形式化模型采用指定的坐标对称，尚未另行形式化全部欧氏等距变换的分类。

论文、程序和形式化工作使用了大量 AI 辅助。已记录的 Lean 检查在相应形式化定义与假设下验证结果。外部审阅及文献新颖性核查仍待完成，本仓库不主张首次发现或首次证明。

欢迎通过 [GitHub Issues](https://github.com/Lshiqi67/domino-tilings-a232622/issues) 提交勘误。请指出对应的论文章节、定理或文件；涉及程序时，请尽可能提供可复现示例。

## 引用与版本归档

引用英文论文时，请使用：

**Shiqi Liu. _Domino tilings of odd-height rectangles up to symmetry_. Version 2.0, 2026.**

```bibtex
@unpublished{liu2026domino,
  author = {Liu, Shiqi},
  title = {Domino tilings of odd-height rectangles up to symmetry},
  year = {2026},
  version = {2.0},
  note = {Preprint, manuscript dated October 25, 2026;
          GitHub release dated October 26, 2026},
  url = {https://github.com/Lshiqi67/domino-tilings-a232622/releases/download/paper-en-v2.0/domino-tilings-en-v2.0.pdf}
}
```

[固定版本 `paper-en-v2.0`](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.0) 包含英文 PDF、公开源码快照、Git 历史备份及校验文件。引用形式化结果时，请同时注明使用的仓库标签或提交编号。
