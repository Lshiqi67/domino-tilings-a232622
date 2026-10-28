# M7、M8：精确稳定子与任意奇数高度

> 本文保留所标日期的阶段记录与当时待办；当前 M1–M11 已完成，英文 v2.1 已对应这些结果，见 [当前进度](progress.md)。

> 2026-10-26 发布说明：本阶段代码和公开证据已纳入 M7–M11 发布；下文“本轮”和“下一步”保留 2026-10-25 阶段记录的时间含义。当前完成范围见 [进度表](progress.md)。

日期：2026-10-25。署名：Shiqi Liu。路线：A002 半棋盘。本文记录本地新增工作；未发布到 GitHub。

**验收状态：`m7_m8_passed`，进程退出码 0。** 完整构建、M1–M6 回归、696 项公理审计及干净重建后的输出一致性全部通过。 最终状态以[本轮报告](../evidence/m7-m8-2026-10-25/verification-01/report.json)为准。历史 M1–M6 报告保持原样。

## 对象、量词与适用范围

沿用 M1 的 `Tiling m w`：有限矩形上由无序相邻两格砖构成的精确覆盖；砖无标签，没有 tatami 限制。`ordinaryCount m n`、`fixedCount m n g` 和 `orbitCount m n` 的棋盘宽度都是 `2*n`。`RectangleSymmetry` 仍为恒等、上下反射 h、左右反射 v、半转 rho 构成的四元群；轨道是实际群作用的商类型。

M7 对所有自然数 n 研究三行。M8 的列规则、部分铺法路径与 v/rho 半棋盘双射对所有自然数高度 m 成立；h 双射及最终通用公式的范围为 `m=2*k+1`、所有自然数 k,n。零宽和一行包括在内。偶数高度也有列路径和两种轴向补全，但不能把奇数高度 h 公式或四元群计数解释为正方形全部八种对称的计数。

原 32 个 M1–M6 数学文件、Lean 4.35.0、mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679` 及九个依赖锁保持不变。一般高度代码另置 `Domino/OddHeight/`，命名空间为 `Domino.General`，复用原来的真实几何对象。

## M7 的结论

记 d、v、r 分别为真实普通铺法数、v 固定数和 rho 固定数。分类先构造实际铺法子类型，再给它限制群作用并取商，分别定义 `symmetryTilingCount`、`symmetryOrbitCount`。

| 类型编号 | 精确稳定子 | 铺法数 | 每个轨道大小 | 轨道数 |
| --- | --- | --- | --- | --- |
| 0 | 全四元群 | 1 | 1 | 1 |
| 1 | 只有 h 与恒等 | 0 | 2（该类为空） | 0 |
| 2 | 只有 v 与恒等 | v−1 | 2 | (v−1)/2 |
| 3 | 只有 rho 与恒等 | r−1 | 2 | (r−1)/2 |
| 4 | 只有恒等 | d+1−(v+r) | 4 | (d+1−(v+r))/4 |

证明顺序：唯一 h 固定铺法在群交换性下被所有元素固定；任意两个不同非恒等元素的固定集交为该单元素；得到每个铺法的精确稳定子，并证明它沿轨道不变。`orbit_size_exact` 用轨道—稳定子等价证明真实轨道的大小；`symmetryOrbitCount_mul_size` 对分类子类型用 Burnside 得到乘法等式。随后推出整除性和上表公式，未用自然数整除的截断掩盖余数。

自然数版本先证明无减法的分拆等式，再写成 `d+1-(v+r)`；不能直接把数学整数式 `d-v-r+1` 按 Lean 自然数左结合截断减法转录。零宽只有全对称轨道一个。n=8 的五类轨道为 **1、0、132、76、7316**，总数 7525，由全部指标定理及已有普通数递推推出。

出口见 [Classification](../Domino/Stabilizers/Classification.lean)、[Counts](../Domino/Stabilizers/Counts.lean)、[Examples](../Domino/Stabilizers/Examples.lean)：`exact_stabilizer`、`orbit_size_exact`、`symmetryOrbitCount_formulas`、`symmetry_type_divisibility`、`three_row_stabilizer_counting`。

## M8 的几何证明链

1. **任意高度的列规则。** `RowValid` 表示剩余行上的相邻、对称、无遗漏且唯一的配对。`row_cover_unique` 对行号强归纳，证明配对唯一；没有固定高度穷举。`Legal p q` 要求左右水平占用集合不交且剩余行可配对。
2. **偶长段的独立判据。** `EvenRuns` 从空区间、跳过占用行、消去两相邻空行三个构造描述连续空行段的偶长条件。`evenRunScan` 用一个布尔量记录当前空行段长度的奇偶；遇占用行或末端要求偶数。`legal_iff_even_run_scan` 证明这项纯行扫描判据与列可铺性等价，另有 `legal_iff_even_runs`。它不把“存在铺法”再次作为扫描条件。
3. **几何与路径。** 由实际无序砖转为对称配对关系，再转为按列的横切口与竖配对，利用唯一性删除竖配对数据，得到 `partialTilingEquivPath` 及两个逆等式。宽度为任意 w、终端为任意 S，零宽仍有原来的空终端守卫。取基数得到 `profile_count_matrix` 和 `tiling_count_matrix`。
4. **v/rho 补全。** `reflectionFixedEquivPartial` 允许任意终端；`halfTurnFixedEquivPartial` 的终端恰满足 `reverseState S=S`。四条限制/补全逆等式、终端条件充要性，以及左内部砖、跨中线砖、右侧对称像均有定理。没有要求左半棋盘自身对称。
5. **奇数高度 h 双射。** 转置把 h 变为奇数宽矩形的 v。中部两个切口相同，局部不交性强迫二者为空；中列只有高度 `2*n` 的唯一竖配对。限制到左 k 列、镜像补全互逆，再转置回来得到 `horizontalFixedEquivTop k n`。`horizontal_restrict_top_bonds`、`horizontal_complete_top_bonds` 明确证明对应的是顶端 k 行中的实际砖，而非任意等势集合。

完整构造见 [OddHeight 入口](../Domino/OddHeight/Boundary.lean)的导入链；主要中间文件为 [EvenRuns](../Domino/OddHeight/EvenRuns.lean)、[PathEquiv](../Domino/OddHeight/PathEquiv.lean)、[Geometry](../Domino/OddHeight/Geometry.lean)、[OddReflection](../Domino/OddHeight/OddReflection.lean)、[TopGeometry](../Domino/OddHeight/TopGeometry.lean)。

## 通用计数、生成函数与递推

令 `T_m` 为全部 `State m = Finset (Fin m)` 上的 0/1 转移矩阵，0 表示空状态，J 表示行反转。对全部 k,n，`odd_height_four_counts` 证明

$$4a_{2k+1}(n)=(T_{2k+1}^{2n})_{0,0}+(T_k^{2n})_{0,0}
+\sum_S(T_{2k+1}^{n})_{0,S}+\sum_{J(S)=S}(T_{2k+1}^{n})_{0,S}.$$

最后两项分别对应论文的终端权重 1 和 chi；这是论文向量写法的两项求和展开。左端就是 M1 商类型的基数。`odd_height_divisible` 单独给出右端可被 4 整除。

对任意有限有理数矩阵 M，定义 `matrixSeries M` 的第 n 个系数矩阵为 M^n，`matrixPencil M=I-XM`。`matrix_geometric_left/right` 逐系数证明左右逆，`matrix_geometric_constant` 证明常数矩阵为 I，`matrix_geometric_unique` 证明逆的唯一性。

令 S(M)=sum M^n X^n，把 T_m 转为有理矩阵，则 `orbit_matrix_series` 给出真实轨道级数

$$A_{2k+1}(X)=\frac14\left[S(T_{2k+1}^2)_{0,0}+S(T_k^2)_{0,0}
+\sum_S S(T_{2k+1})_{0,S}+\sum_{J(S)=S}S(T_{2k+1})_{0,S}\right].$$

伴随矩阵恒等式推出 `det(I-XM) * S(M) = adj(I-XM)`；行列式常数项为 1 已单独证明。`RationalSeries F` 的定义正是存在多项式 P,Q，满足 Q 的常数项非零且 QF=P。对有限和及有理常数倍封闭，得到 `odd_height_rational_witness`，没有解析收敛假设。

`odd_height_eventual_recurrence` 进一步给出存在 d、起点 N 和与 n 无关的有理系数 c，c(0) 非零，且对所有 n>=N：

$$a_{2k+1}(n+d)=-c(0)^{-1}\sum_{i=0}^{d-1}c(i+1)a_{2k+1}(n+d-i-1).$$

证明直接取 QF=P 的高次系数；可取 d=deg(Q)、N=deg(P)+1。不声称这个阶最小，也不把 M9 的五行压缩分母或十四阶递推视为已经完成。

边界包括 `zero_height_transfer`（T_0 为一阶单位矩阵）、`ordinary_one_row`、`fixed_one_row`、`orbit_one_row`（全部 n 都为 1）和 `odd_height_empty`。

## 本地复现与验收设计

在现有项目目录运行：

```powershell
cd domino-tilings-a232622/lean
lake --wfail build
python -X utf8 scripts/check_m7_m8.py --report-dir ("checks/m7-m8-rerun-" + (Get-Date -Format "yyyyMMdd-HHmmss"))
```

成功标志是进程退出码 0 和最后一行 `m7_m8_passed`。脚本递归回归 M6 至 M1 及固定环境，比较原 32 数学文件和版本锁，审计全部 696 项显式声明。M7 新增 3 模块、43 项声明（33 定理），M8 新增 22 模块、240 项声明（144 定理）；累计 57 数学模块、445 个定理。辅助定义及定理也计入这些数量，不能当作论文定理数量。

M6 回归会将当前全部新旧源码复制到新的 `clean-project` 并完整重建；本脚本在同一新建目录继续审计 M1–M8，逐字比较两次公理输出和主定理类型输出，避免重复做相同重建。允许公理只有 `propext`、`Classical.choice`、`Quot.sound`。共享已核对的第三方依赖缓存，不宣称从零编译全部 mathlib。检查是确定性的，无随机种子；本轮未重新运行历史铺法枚举器。

入口、清单与日志分别位于 [Audit/M7M8](../Domino/Audit/M7M8.lean)、[主定理类型](../Domino/Audit/M7M8Statement.lean)、[声明清单](m7-m8-declarations.json)、[运行目录](../evidence/m7-m8-2026-10-25/README.md)。开发失败记录保留，主要为有限基数实例、隐式高度、自然数减法、矩阵同态化简及警告处理；它们不构成数学反例。

## 后续可执行工作

下一阶段为 M9：从一般状态路径证明五行可达支持与反转压缩，连接论文六维矩阵，验证分子分母证书、十四阶递推及全部初值。随后 M10 处理渐近与两种抽样概率，M11 处理基本块分类、唯一分解及第二证明。外部人工语义审阅和文献定位继续独立进行；本轮不修改论文 PDF，不确认新颖性，也没有提交或推送 GitHub。
