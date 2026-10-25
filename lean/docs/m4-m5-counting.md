# M4、M5：三行递推、固定点奇偶式与实际轨道计数

> 本文保留该阶段形成时的范围与后续计划；当前 M1–M6 均已完成本地验收，发布说明见 [进度表](progress.md)。

日期：2026-10-25。继续 P002 的 A002 半棋盘路线。M4、M5 已通过本地 Lean 构建；累计公理与旧阶段回归的完整证据见[验收报告](../evidence/m4-m5-2026-10-25/verification-01/report.json)。三行主生成函数、七阶递推和完整七项初值仍属 M6，尚未完成。

## 对象、范围与下标

沿用 M1 的真实无序多米诺精确覆盖定义，不改变 `ordinaryCount`、`fixedCount`、`orbitCount` 或 `a`。令 `q_w(S) = profileCount w S`，它是实际 `PartialTiling 3 w S` 的基数；w 是半棋盘的列数。令 `d_n = ordinaryCount 3 n`，它计数完整 3×2n 棋盘，`a n = orbitCount 3 n` 是四种坐标对称下的实际商集基数。h、v、r 分别为上下反射、左右反射、半周旋转的固定点数。

下列公式对全部自然数 j、n 成立，包括零宽。j 是奇偶拆分指标；例如 v_(2j) 对应完整 3×4j 棋盘，其左半棋盘为 3×2j。宽零部分对象仍有 M1 的守卫，只有空终端产生空铺法。

## M4 已证明内容

偶数列的计数函数在空集合处为 α_j，在 `{0,1}`、`{1,2}` 处为 β_j，其他五个终端为零。奇数列在 `{0}`、`{2}` 处为 α_j+β_j，在全三行集合处为 α_j，其他五个终端为零。这是支持包含关系，不声称列出的状态总有正计数，尤其 β_0=0。

辅助数列满足

$$\alpha_0=1,\quad\beta_0=0,\qquad
\alpha_{j+1}=3\alpha_j+2\beta_j,\quad\beta_{j+1}=\alpha_j+\beta_j.$$

`profile_even_odd` 从 M2 的实际 `profile_count_zero`、`profile_count_succ` 在 j 上归纳，同时证明上述两种计数函数。八状态穷尽和单步运算只处理有限局部规则；一般 j 的结论没有用有限数值实验代替。`alpha_eq_profile`、`beta_eq_profile` 与 `ordinary_eq_alpha` 将辅助数列接回实际部分及完整铺法。

因此对全部 j，

$$d_0=1,\quad d_1=3,\qquad d_{j+2}+d_j=4d_{j+1}.$$

同时证明自然数减法下界、自然数减法版本、整数版本、逐步单调性和正性。二维矩阵采用**列向量**约定：

$$\binom{\alpha_{j+1}}{\beta_{j+1}}=
M\binom{\alpha_j}{\beta_j},\qquad
M=\begin{pmatrix}3&2\\1&1\end{pmatrix},\qquad M^2+I=4M.$$

这与 M2 八状态转移使用行向量的约定分开陈述。矩阵恒等式是额外的已核验出口，真实 d 的二阶递推直接从已连接的 α、β 递推消元得到。

对 M3 的实际终端求和公式分别求和；J 不变的四个终端恰为 `∅`、`{1}`、`{0,2}`、全三行集合。得到

$$v_{2j}+2d_j=d_{j+1},\quad v_{2j+1}=d_{j+1},\qquad
r_{2j}=r_{2j+1}=d_j,\quad h_n=1.$$

h_n=1 复用 M3；`fixed_counts_parity` 汇总 v、r 的四个分支。`reflection_even_bound` 给出 2d_j≤d_(j+1)，所以自然数式 v_(2j)=d_(j+1)−2d_j 没有截断歧义。

## M5 已证明内容

对任意自然数 m、n，将 mathlib 的有限群作用 Burnside 定理应用于 M1 的真实铺法作用：

$$4\operatorname{orbitCount}(m,n)=\operatorname{ordinaryCount}(m,n)
+\operatorname{fixedCount}(m,n,h)+\operatorname{fixedCount}(m,n,v)
+\operatorname{fixedCount}(m,n,\rho).$$

不要求作用忠实，m=0 或 n=0 也包括。这里的一般 m 结论仅关于指定的四种坐标对称；不能把正方形的四元群轨道解释为完整八种几何对称的轨道，也没有在本轮证明一般高度的半棋盘公式。mathlib 与项目的有限实例通过恒等等价下的基数相等显式衔接。

先证明自然数乘法式，再证明四项和被 4 整除，推出自然数平均式及有理数平均式。结合 M4 得

$$4a(2j)+d_j=d_{2j}+1+d_{j+1},$$
$$4a(2j+1)=d_{2j+1}+1+d_{j+1}+d_j.$$

偶数分子的减法下界和两个分子的整除性均另有定理，随后得到自然数除法和有理数版本：

$$a(2j)=\frac{d_{2j}+1+d_{j+1}-d_j}{4},\qquad
a(2j+1)=\frac{d_{2j+1}+1+d_{j+1}+d_j}{4}.$$

有理数版本先转换无减法等式再作域运算，不把自然数截断减法直接当作域减法。a 一直保持实际轨道基数定义，未用目标公式重定义。

边界出口证明 a(0)=1、a(1)=2、a(2)=5，且 3×2 的 `(d,h,v,r,a)=(3,1,3,1,2)`。这三个初值不替代 M6 规定的完整七项初值。

## 模块和可复用出口

| 阶段与文件 | 主要出口 |
| --- | --- |
| M4 [ProfileRecurrence.lean](../Domino/ThreeRows/ProfileRecurrence.lean) | `profile_even_odd`、`profile_even`、`profile_odd`、两个支持包含定理、`alpha_succ`、`beta_succ` |
| M4 [Ordinary.lean](../Domino/ThreeRows/Ordinary.lean) | `ordinary_eq_alpha`、`ordinary_recurrence_add`、`ordinary_recurrence_int`、`ordinary_initial_values`、两个矩阵定理 |
| M4 [FixedCounts.lean](../Domino/ThreeRows/FixedCounts.lean) | `reflection_even_add`、`reflection_even_bound`、`fixed_counts_parity` |
| M5 [Burnside.lean](../Domino/Symmetry/Burnside.lean) | `four_mul_orbitCount`、`fixed_sum_divisible_four`、`orbitCount_eq_average`、`orbitCount_average_rat` |
| M5 [OrbitCounts.lean](../Domino/ThreeRows/OrbitCounts.lean) | `four_mul_a`、`orbit_even_add`、`orbit_odd_mul`、两个整除定理、`orbit_even_rat`、`orbit_odd_rat` |
| M5 [Boundary.lean](../Domino/ThreeRows/Boundary.lean) | `three_row_small_orbit_counts`、`width_two_counts` |

新增六个模块、65 项显式声明，其中 M4 为 38 个定理和 6 个定义，M5 为 21 个定理。累计 M1–M5 共 27 个数学模块、362 项显式声明，其中 230 个定理。声明数包括辅助定义、实例等，不等于论文定理数；完整清单见 [m4-m5-declarations.json](m4-m5-declarations.json)。

## 核验与信任范围

固定 Lean 4.35.0、mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。完整 `lake --wfail build` 通过 3177 个含依赖构建任务。累计逐声明公理审计仅允许 `propext`、`Classical.choice`、`Quot.sound`；没有占位证明、自设公理或 `native_decide`。归纳、等价、Burnside 以及算术推导提供一般参数结论，内核 `decide` 用于有限状态、四元素群与 2×2 矩阵恒等式。

从 lean 目录运行 `python -X utf8 scripts/check_m4_m5.py --report-dir checks/m4-m5-rerun-new`，报告目录必须不存在。脚本递归运行原 M3/M2/M1 验收，检查固定环境、九个依赖实际提交、完整构建、总入口、覆盖 DAG、源码筛查、累计公理，以及 M3 最终报告中原 21 个数学源文件和三个版本配置文件的哈希不变。最终报告记录全部命令、退出码、声明公理及源码 SHA-256；[核验目录](../evidence/m4-m5-2026-10-25/README.md)保留开发失败与修正。

本轮是 Windows PowerShell 下的确定性验证，无随机种子；未重跑历史 Python 铺法枚举，使用已有锁定依赖及缓存，未另做干净目录全量安装。定义语义由同一助手核对，外部人工审阅仍待完成。CI 配置已本地更新，未推送或运行远端 CI；原论文、证明草稿和历史阶段报告保留。

## 覆盖与 M6 交接

B05、B06、B07、C02 已完成。L006 获得完整证据；L009 的二维计数、普通数递推、固定点与轨道奇偶式已完成，其原映射包含的 B08 生成函数部分仍待 M6。L007/L008 仍只在三行范围完成。T04 的零宽及 n=1 轨道边界已覆盖，基本块 k=1 仍待 M11，故整个节点保持 partial。C00 的形式幂级数部分也保持待办。

下一项依次实现：系数级数工具 → 普通数及固定点生成函数 B08 → 分母通分恒等式 C03 → 真实轨道主生成函数 T02 → 七阶递推、完整七项初值 T03。优先复用 `ordinary_recurrence_add`、`four_mul_a` 和固定点奇偶式；涉及负项时先映入 ℤ 或 ℚ。完成 M6 全部出口与审计后再升级三行主定理状态。
