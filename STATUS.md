# Research status / 研究状态

Date / 日期: 2026-10-25  
Author / 署名: **Shiqi Liu**

## Current position

**This work is unfinished. This repository does not claim to have solved the conjecture recorded as OEIS A232622. The manuscripts need further refinement. The correctness of the proposed proofs still requires Lean formalization and verification, as well as mathematical review.**

No Lean formalization has been completed, no Lean build has verified these claims, and no theorem in this repository is presented as Lean-certified. There is no formalization project or placeholder theorem purporting to certify the result.

The available material consists of two proposed derivations, refinements and extensions, finite exhaustive computations, and exact symbolic identities for specified models. These may be useful research evidence; they do not settle the validity of every definition, bijection and infinite-parameter inference.

## 当前立场

**研究尚未完成。本仓库不宣称已经解决 OEIS A232622 猜想。论文仍需打磨，所提出证明的准确性还需要 Lean 形式化验证以及数学审阅。**

目前未完成 Lean 形式化，未有 Lean 构建验证这些主张，也没有把占位形式化文件当作证明。两个推导草稿、有限枚举和精确代数恒等式均按实际覆盖范围展示。

中文论文是保持原样的历史草稿。英文公开稿增加了当前未完成声明。草稿中的“定理”“证明”“完整推导”等文字均不改变本页的研究状态。

## What remains / 尚待完成

1. Check the exact counting objects, all boundary cases and group action against the original problem.
2. Formalize the tiling/state correspondence, block classification and unique decomposition in Lean.
3. Formalize the two directions of each half-rectangle completion map, including crossing dominoes.
4. Verify the fixed-point counting, Burnside averaging and rational-function coefficient arguments.
5. Separately verify stabilizers, asymptotics, odd-height scope and the five-row compression/certificate.
6. Refine the exposition and compare related literature systematically; no priority or global-open-status claim is established.

下一项可执行工作是先确定 Lean 与 mathlib 版本，精确定义有限棋盘铺法及对称作用，再逐步实现并检查核心双射。只有实际构建通过且记录了覆盖范围、依赖和剩余未形式化部分，才能报告相应的验证结果。Lean 中形式化的命题也必须与原始题意相符。
