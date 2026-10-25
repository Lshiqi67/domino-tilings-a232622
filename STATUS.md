# Research status / 研究状态

Date / 日期: 2026-10-25  
Author / 署名: **Shiqi Liu**

## Current position

**The three-row main counting theorem is now locally verified in Lean under the stated tiling and four-coordinate-symmetry definitions. The project as a whole remains unfinished: extensions, the block-route second proof and external mathematical review are still pending. No novelty or priority claim is made.**

Lean M1 through M6 have passed local builds and cumulative axiom audits. M6 proves the formal generating function with coefficients equal to actual orbit cardinalities, the original signed rational expression, the seventh-order recurrence for every natural index and all seven initial values. A fresh project directory rebuilds all project sources using the verified pinned dependency cache. See the [precise M6 scope](lean/docs/m6-main-theorem.md).

The available material consists of two proposed derivations, refinements and extensions, finite exhaustive computations, and exact symbolic identities for specified models. These may be useful research evidence; they do not settle the validity of every definition, bijection and infinite-parameter inference.

## 当前立场

**三行主计数定理现已按明确的铺法与四种坐标对称定义完成本地 Lean 验证。研究整体仍有全文扩展、基本块第二证明和外部数学审阅待办，不主张文献优先权。**

目前已完成 Lean M1–M6：累计 32 数学模块、413 项显式声明公理审计及干净项目重建。M6 新增四类固定点生成函数、主分母恒等式与单位逆、题面原式、全部自然数指标七阶递推及七项初值 1,2,5,14,46,156,561；递推起点 a(7)=2037。C00/B08/C03/T02/T03 已完成，全文其他部分不自动升级。

中文论文是保持原样的历史草稿。英文公开稿增加了当前未完成声明。草稿中的“定理”“证明”“完整推导”等文字均不改变本页的研究状态。

## What remains / 尚待完成

1. Formalize exact stabilizers and the corresponding orbit counts (M7).
2. Formalize arbitrary odd heights, five-row certificates, asymptotics and the block-route second proof (M8–M11).
3. Refine the exposition and compare related literature systematically; priority and global open status are not established.

Lean 4.35.0、mathlib 精确提交和原 M1–M5 的 27 数学源文件保持不变。方案与覆盖表见 [Lean 项目](lean/README.md)，实际证据见 [M6 记录](lean/evidence/m6-2026-10-25/README.md)。下一项 M7；T04 的基本块 k=1 未完成。未另行形式化欧氏全部等距变换分类；非空三行偶宽棋盘按题面四种坐标映射取商。代码、固定版本配置、阶段说明、公开验证证据及 CI 工作流现一并提供。远端验收状态以 [GitHub Actions](https://github.com/Lshiqi67/domino-tilings-a232622/actions/workflows/lean.yml) 对应提交为准。阶段顺序见[成果及后续工作](lean/docs/progress.md)。