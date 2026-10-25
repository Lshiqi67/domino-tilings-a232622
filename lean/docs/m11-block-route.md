# M11：基本块路线的第二条形式化证明

> 2026-10-26 发布说明：本阶段代码和公开证据已纳入 M7–M11 发布；下文“本轮”和“下一步”保留 2026-10-25 阶段记录的时间含义。当前完成范围见 [进度表](progress.md)。

日期：2026-10-25。署名：Shiqi Liu。对应既有 A001 基本块路线，与 A002 半棋盘路线共享定义、逐列路径双射、Burnside 和纯代数。

状态：**M11 已通过完整本地验收，`m11_passed`，退出码 0。** 新增 11 模块、190 声明（122 定理）；累计 83 数学模块、1078 声明（699 定理），M1–M10 回归、累计公理审计、干净重建及源码/类型/公理比较全部通过。见 [实际报告](../evidence/m11-2026-10-25/verification-01/report.json)。

## 对象、量词和独立性

对象仍是无标签多米诺完整铺法 `Tiling 3 (2*n)`，`n : ℕ` 为棋盘半宽，包括空棋盘。对称采用原有上下反射、左右反射及半周旋转的坐标作用。没有增加 tatami 或可切分条件。

基本块是非空、没有内部断口的铺法。`BasicTiling` 要求实际路径的所有内部切口非空；`empty_cut_iff_no_crossing` 证明空切口恰好表示没有水平砖跨越该竖直格线。该定义的几何意义另有定理，并非仅给一种抽象字模型起名为铺法。

M11 的生产模块只导入 `Board`、`Transfer`、`Symmetry`、`Series` 及纯代数模块 `ThreeRows/Algebra`。不导入 `HalfBoard`、三行普通/固定点计数递推、T02、稳定子、一般高度、五行或渐近模块。验收脚本记录 `Blocks/Main` 的项目导入闭包并拒绝其他计数路线；这是组合依赖的独立性，不是两套完全不共享基础或独立作者的证明。

## 分类、分解和真实几何

`Letter.c` 表示 C；`Letter.arm false k`、`Letter.arm true k` 分别表示论文的 A_(k+1)、B_(k+1)。代码参数 k 从 0 开始，论文参数从 1 开始。字母权重为 1 或 k+1，始终为正；字重 `mass` 是总半宽，字长是块的个数，两者不混淆。

`core` 列出一个块的内部切口，`trace` 在每个块后加空切口。实际完整路径以空状态开头、以空状态结尾。局部八状态规则使用已有 `Legal3`；新 `transition_table` 仅作有限单步核对，分类与分解对任意路径长度进行归纳。

`valid_complete_aux` 穷尽从空状态和两种成对行状态出发的合法路径。`decode_trace` 与 `valid_decode` 给出可执行编码/解码的两个逆式；`unique_decomposition` 保证分解唯一。`irreducible_iff_letter` 证明首次回空路径恰好对应一个字母，`letterEquivBasic` 进一步把固定半宽字母与真实基本块建立等价。

`all_cuts_are_block_boundaries` 给出全部断口的精确刻画：切口 k 为空，当且仅当字能分为前缀 U 和后缀 V，且 k=2·mass(U)。因而每个空切口都被分解使用，每个块分界都为空切口。

`wordEquivTiling n` 是固定总半宽字与原始几何铺法的双向等价，有两个 roundtrip 定理。`Word n` 的有限性由该等价和真实棋盘有限性推出，允许无限字母表，不使用无穷基数的形式相减或未证的系数有限性。

## 对称和回文中心

`flip` 固定 C，交换同宽的 A、B；保持字母权重且为对合。每个基本块内部切口序列都是回文，行反射则逐状态交换 A/B。

`word_horizontal`、`word_vertical`、`word_halfTurn` 证明真实坐标作用在字上分别为逐字母 flip、倒序、倒序后 flip。证明通过完整切口序列进行，覆盖不同块宽，并未把块序号误作几何列号。

对于 b=false，`mirror` 是普通倒序；b=true 时是倒序再 flip。每个固定字都唯一写成

$$W=U\,c\,\operatorname{mirror}_b(U),$$

其中 c 为空或单个字母，并满足 `CenterOK b c`。`palindrome_unique` 同时给出存在和唯一性，`palindromeEquiv` 是有权约束的实际等价。普通回文允许任意中心字母；带对合回文的非空中心只能是 C。中心块可以跨越几何中线。

## 四类固定点及 T01

令 F 为实际基本块字母按权重计数的形式幂级数，D 为全部字的级数。`graded_product` 从固定权重的有限纤维等价证明 Cauchy 乘积，`wordHeadEquiv` 按空字或首字母加尾字分解得到

$$F=\frac{3X-X^2}{1-X},\qquad D=1+FD=\frac{1-X}{1-4X+X^2}.$$

上下反射固定字恰为 C 的重复；回文半字权重加倍，通过偶次系数和奇次零系数另证 `double_mass_series`。四类实际固定点级数因此为

$$H=\frac1{1-X},\qquad V=(1+F)D(X^2),\qquad R=(1+X)D(X^2).$$

这里 D、H、V、R 都通过等价连接原有真实铺法基数；不把它们定义成希望得到的有理式。全部运算在 `PowerSeries ℚ` 中，不涉及解析收敛。

用同一实际群作用的 Burnside 定理及已独立证明的纯代数通分，得到

$$\sum_{n\ge0}a(n)X^n=\frac{1-3X-4X^2+10X^3-4X^5+X^6}{(1-X)(1-4X+X^2)(1-4X^2+X^4)}.$$

主出口是 `Domino.Blocks.orbit_series_via_blocks`；`orbit_series_paper_via_blocks` 给出题面原符号分式。先证明分母乘法恒等式，再利用非零常数项取逆；没有把 X 或 X² 当作单位。`three_row_block_main` 汇总分类、真实双射、回文唯一性和主式。

## 边界与覆盖

`blocks_parameter_one` 核对 C、A₁、B₁ 的切口序列及权重 1 的字母恰有三个。空字的唯一性由正权重证明。既有零宽、3×2 计数和递推起点记录保留；本阶段补全原 T04 的基本块 k=1 项。

覆盖节点为 A02–A08、T01 及 T04 剩余项；共享前提 C00/C01/A01/C02/C03 沿用此前已证结果。规划中的占位出口名已由 [覆盖表](coverage.json) 映射到实际声明，不把未实现的接口名列为已证。

## 本地文件和复现

所有新数学文件位于 `Domino/Blocks/`，命名空间统一为 `Domino.Blocks`：

| 文件 | 内容 |
| --- | --- |
| [Letters](../Domino/Blocks/Letters.lean) | 字母、正权重、编码、解码逆式及单块对称 |
| [Decomposition](../Domino/Blocks/Decomposition.lean) | 路径完备性、唯一分解、首次回空分类 |
| [Geometry](../Domino/Blocks/Geometry.lean) | 固定半宽字与真实几何铺法的等价和有限性 |
| [Symmetry](../Domino/Blocks/Symmetry.lean) | 真实群作用与三种字变换的相容性 |
| [Palindromes](../Domino/Blocks/Palindromes.lean) | 半字/中心唯一分解及有权等价 |
| [Graded](../Domino/Blocks/Graded.lean) | 有限纤维的乘积和可选对象计数 |
| [WordSeries](../Domino/Blocks/WordSeries.lean) | 字母级数、首字母分解和普通级数 |
| [FixedSeries](../Domino/Blocks/FixedSeries.lean) | 半字加倍、中心分类、V/R 级数 |
| [Horizontal](../Domino/Blocks/Horizontal.lean) | C 的重复与 H 级数 |
| [Boundary](../Domino/Blocks/Boundary.lean) | 几何基本块、全部断口和 k=1/空字 |
| [Main](../Domino/Blocks/Main.lean) | 四类固定点合并、主式和汇总出口 |

在现有 `lean` 目录运行：

```powershell
lake --wfail build
python -X utf8 scripts/check_m11.py --report-dir ("checks/m11-rerun-" + (Get-Date -Format "yyyyMMdd-HHmmss"))
```

累计声明清单见 [m11-declarations.json](m11-declarations.json)，类型审查入口见 [M11Statement.lean](../Domino/Audit/M11Statement.lean)。实际命令、退出码、失败日志和最终报告见 [本轮检查目录](../evidence/m11-2026-10-25/README.md)。成功标记为 `m11_passed` 且进程退出码 0。

固定 Lean 4.35.0、mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679` 及九个依赖不变。验收核对旧 72 数学文件与三份版本配置哈希，递归运行 M1–M10 回归，对全部生产声明审计传递公理依赖，并在没有项目自身产物的新目录重新构建。第三方固定缓存共享，不是从零重编译 mathlib。允许公理仅为 `propext`、`Classical.choice`、`Quot.sound`；确定性过程，无随机种子。

本轮没有重跑历史 Python 枚举，没有上传 GitHub、运行远端 CI 或修改论文 PDF/TeX。文献优先权、全部欧氏等距变换分类、一般高度渐近、最小递推阶及外部人工语义审阅仍是独立工作，不能由 M1–M11 阶段完成自动推出。
