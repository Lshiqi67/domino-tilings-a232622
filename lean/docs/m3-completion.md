# M3：对称半棋盘补全、几何对应与固定点计数

> 本文保留所标日期的阶段记录与当时待办；当前 M1–M11 已完成，英文 v2.1 已对应这些结果，见 [当前进度](progress.md)。

> 本文保留该阶段形成时的范围与后续计划；当前 M1–M6 均已完成本地验收，发布说明见 [进度表](progress.md)。

日期：2026-10-25。路线：P002 / A002。**M3 已完成本地 Lean 验证，覆盖三行证明链 B02、B03、B04；主轨道生成函数与七阶递推尚未形式化完成。**

## 精确命题与范围

高度固定为 3，半宽 n 为任意自然数，完整棋盘实际宽度为 2*n。铺法、末列洞的部分铺法、上下反射 h、左右反射 v、半周旋转 rho 全部复用 M1 的定义；M1/M2 的 14 个数学源文件及工具链/依赖锁未改。

已建立实际对象之间的等价：

$$\operatorname{Fix}(v)\simeq\sum_{S\subseteq\{0,1,2\}}\texttt{PartialTiling}\;3\;n\;S,$$
$$\operatorname{Fix}(\rho)\simeq\sum_{S:J(S)=S}\texttt{PartialTiling}\;3\;n\;S,$$

其中 J=`reverseState`。定义域只要求终端 S 上下不变，**不要求左半铺法本身上下对称**。两个等价均有补全后限制、限制后补全的恒等式；`halfTurn_extension_iff` 另证明对给定实际部分铺法，具有相同左半切口信息的半周固定扩展存在当且仅当 J(S)=S。

上下反射固定铺法不含竖砖，并且等于构造出的三行全水平铺法。由真实固定点子类型取基数，得到全部 n 的

$$v_n=\sum_Sq_n(S),\qquad r_n=\sum_{J(S)=S}q_n(S),\qquad h_n=1.$$

这里 q_n 是 M2 中真实部分铺法的基数；还没有完成 M4 的二维压缩及 v、r 的奇偶闭式，也没有使用或证明 Burnside 平均。

## 模块与出口

| 文件 | 作用与主要出口 |
| --- | --- |
| [Symmetry/PathAction.lean](../Domino/Symmetry/PathAction.lean) | `coverBonds_action`、三种 `tilingPath_*`、`axial_fixed_iff_path`：实际坐标作用与提取路径相容 |
| [HalfBoard/PathCompletion.lean](../Domino/HalfBoard/PathCompletion.lean) | 半路径折回补全、限制、两向互逆；统一的 `axialFixedEquivPartial` |
| [HalfBoard/Geometry.lean](../Domino/HalfBoard/Geometry.lean) | `axial_restrict_internal`、`axial_complete_internal`、`axial_complete_crossing`、`axial_complete_right`；实际内部砖与跨线砖对应 |
| [HalfBoard/Reflection.lean](../Domino/HalfBoard/Reflection.lean) | `reflectionFixedEquivPartial`、两条 reflection 逆等式、`reflection_fixed_count` |
| [HalfBoard/HalfTurn.lean](../Domino/HalfBoard/HalfTurn.lean) | `halfTurnFixedEquivPartial`、两条 halfTurn 逆等式、`halfTurn_terminal_necessary`、`halfTurn_extension_iff`、`halfTurn_fixed_count` |
| [HalfBoard/Horizontal.lean](../Domino/HalfBoard/Horizontal.lean) | `horizontal_fixed_no_vertical`、`horizontal_fixed_unique`、`horizontal_fixed_card_three` |
| [HalfBoard/Examples.lean](../Domino/HalfBoard/Examples.lean) | 零半宽终端限制、零宽固定点、3×2 的普通数及三类固定点数 |

新增七个模块、75 项显式声明，其中 49 个定理；累计 M1–M3 为 21 个数学模块、297 项显式声明，其中 171 个定理。类型、定义、实例也在清单中，声明数不是论文定理数。见 [累计清单及源码行号](m3-declarations.json)、[阶段核验记录](../evidence/m3-2026-10-25/README.md)和[最终报告](../evidence/m3-2026-10-25/verification-01/report.json)。

## 证明结构及定义语义

### 坐标作用先与路径对应

没有将路径上的对称直接当作铺法的对称。先从 M1 无序砖的坐标像证明 `coverBonds_action`，再证明每个内部切口的路径状态恰为跨越该切口的实际水平砖集合。对宽度 w 的完整铺法 T，逐切口证明：

- h 的路径状态是原状态的 J 像；
- v 在第 k 个切口的状态是原路径第 w-k 个状态；
- rho 在第 k 个切口的状态是原路径第 w-k 个状态的 J 像。

端点切口为空、棋盘外状态为空的情形分别处理。借 M2 等价的单射性，以上关系给出实际固定铺法的充分必要条件。

### 补全和限制

沿用 M2 已验证的纯状态路径。左半路径 P 在 k≤n 保持原状态；右侧用第 2*n-k 个左半状态，半周情形再施加 J。中线两段一致的条件恰为 J(S)=S；左右反射的行变换是恒等，任意 S 均可用。对称性和逐步合法性先证明，再用 M2 逆等价恢复实际砖集合。

限制取前 n 步，保留中线状态，并将 k>n 的延拓置空。`restrict_complete_halfPath` 与 `complete_restrict_axialPath` 对所有 n 成立；复合已验证的等价后给出实际铺法上的四条逆等式。

本轮对原方案的实现调整：通过 M2 的等价实现补全，避免再写一套无序砖并集覆盖证明；同时增加实际砖的几何证书，保留原计划的语义要求。没有用基数相等、选择某个抽象双射或假设补全正确来代替构造。

### 几何证书

`leftCell` 把左半格子按原坐标嵌入完整棋盘。`grid_left_agreement` 由相同切口和唯一竖直填充证明左半内部配对完全一致，因此限制确实保留两端都在左半边的原砖，补全也不会改变这些砖。

对 n>0，每个 r，跨中线格子对 `(r,n-1),(r,n)` 属于补全铺法当且仅当 r∈S。`crossing_bond_same_row` 从共边邻接证明任何跨中线砖必须是这种同行相邻列配对。右侧配对恰为左侧在 v 或 rho 下的坐标像，由已证明的实际固定性和坐标配对引理推出。对应的是无序砖，不引入端点标号的重计。

### 上下反射与唯一性

`horizontal_fixed_no_vertical` 直接使用实际配对关系：三行任何竖砖碰到中行，反射后的另一块砖会与它共用中行格；唯一邻格性质产生矛盾。该结论没有假设每块砖逐块固定。

唯一性随后通过有限列规则和宽度归纳证明：从空状态开始，行反转不变的可行路径只能在空集合与全三行集合之间交替。偶数宽的交替路径给出存在性；M2 单射性给出实际铺法唯一性。此处没有新增任意一行宽度的独立库定理，B04 的三行结论已完整覆盖；一般奇数高度的 L008 留在 M8。

## 边界、信任范围与验证

n=0 不构造 `Fin 0` 中不存在的末列，路径补全和限制仍然有效；实际部分对象由 M1 守卫强制 S=∅。普通数及三个固定点数在 n=1 为 `(3,1,3,1)`，在 n=0 为 1；轨道数 n=1 的 2 尚未在本阶段证明。

Lean 固定为 `leanprover/lean4:v4.35.0`，mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。完整 `lake --wfail build` 通过 3171 个含依赖的构建任务；累计 297 项声明公理审计只含 `propext`、`Classical.choice`、`Quot.sound`。一般 n 的结论来自等价、算术证明及归纳；有限 `decide` 用于三行列规则的反转性质、局部强制性与小边界，未使用 `native_decide`、自设公理或占位证明。

一键验收 `scripts/check_m3.py` 复用 M2/M1 检查，记录实际工具版本、九个依赖提交、完整构建、入口、覆盖 DAG、累计公理及源码 SHA-256，并对照 M2 最终报告核对原 14 模块和版本锁未变。开发失败输出保留，原因及修正见核验记录。确定性检查，无随机种子；未重跑历史 Python 枚举。未重新做无缓存全量依赖安装；最终独立验收仍按完整方案安排。

定义与原题对应由同一助手核对，外部人工审阅待办。原论文、证明草稿和历史报告不变；仅本地保存，没有推送或运行远端 CI。

## 覆盖与下一步

B02/B03/B04 为 checked；L007 只三行版本、L008 只三行 h_n=1 的特例获得本轮证据，不升级一般高度。B04 的实际唯一性证明复用 C01/B01，覆盖表记录这一替代依赖。T04 增加 n=1 四类铺法计数，仍因轨道数和基本块 k=1 边界保留 partial。

下一项执行 M4：证明全部步数的状态支持及偶/奇计数，压成二维递推，再推出普通数二阶递推和三类固定点的奇偶闭式，覆盖 B05/B06/B07。可直接使用 `profile_count_succ`、`reflection_fixed_count`、`halfTurn_fixed_count`、`horizontal_fixed_card_three`。Burnside 为 M5，主生成函数、七阶递推和完整初值为 M6。
