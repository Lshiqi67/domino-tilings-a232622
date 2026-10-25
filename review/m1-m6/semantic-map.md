# 论文对象与 Lean 的逐项语义对应

日期：2026-10-25。来源：本轮实际阅读论文 TeX、M1–M6 源码和已保存验收记录后的 AI 辅助核对。下面的“已核对”是准备者判断，所有项目的外部人类审阅状态均为 **待审**。

英文 v2.0 与中文 v2.1 使用同名 TeX 标签。为避免分页变化，以文件、标签和声明名定位。M1–M6 不覆盖全文所有同名引理的全部高度范围。

[返回入口](README.md) · [复核问题与依赖](checkpoints.md) · [审阅表](review-form.md) · [机器可读映射](mapping.json)

## S01 · M1 · introduction.tex：计数对象

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

任意 n≥0；非空棋盘 3×2n；纸面一基坐标对应 Fin 3 × Fin (2*n) 的零基坐标。


**Lean 入口：**
- [`Domino.Cell`](../../lean/Domino/Board/Basic.lean#L14)（abbrev，第 14 行）
- [`Domino.Adjacent`](../../lean/Domino/Board/Basic.lean#L16)（def，第 16 行）
- [`Domino.three_ne_even_width`](../../lean/Domino/Symmetry/Counting.lean#L45)（theorem，第 45 行）

已核对：邻接使用同行/同列及相差 1 的析取，允许两个方向；未加入 tatami 限制。

**外部审阅问题：**请逐项核对坐标平移；纸面 r=1,2,3 对应代码 0,1,2。三行永不等于正偶数宽度，但这不是全部欧氏等距分类定理。

外部判断：待审。

## S02 · M1 · introduction.tex：铺法定义

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

砖为无序相邻两格集合；铺法为这些砖的有限集合，每格恰覆盖一次。


**Lean 入口：**
- [`Domino.IsEdge`](../../lean/Domino/Board/Tiling.lean#L11)（def，第 11 行）
- [`Domino.Edge`](../../lean/Domino/Board/Tiling.lean#L14)（abbrev，第 14 行）
- [`Domino.edgeOfAdjacent_swap`](../../lean/Domino/Board/Tiling.lean#L23)（theorem，第 23 行）
- [`Domino.edge_card_two`](../../lean/Domino/Board/Tiling.lean#L28)（theorem，第 28 行）
- [`Domino.IsCover`](../../lean/Domino/Board/Tiling.lean#L46)（def，第 46 行）
- [`Domino.Cover`](../../lean/Domino/Board/Tiling.lean#L50)（abbrev，第 50 行）
- [`Domino.Tiling`](../../lean/Domino/Board/Tiling.lean#L53)（abbrev，第 53 行）
- [`Domino.isCover_empty_iff`](../../lean/Domino/Board/Tiling.lean#L74)（theorem，第 74 行）
- [`Domino.cover_exactly_one`](../../lean/Domino/Board/Tiling.lean#L60)（theorem，第 60 行）

已核对：IsEdge 保证相邻与两格；IsCover 的覆盖充要条件加交叠唯一性刻画精确覆盖。Subtype 的证明不产生额外标签。

**外部审阅问题：**请检查没有砖编号、端点方向、重叠或漏格；Bonds 中临时有序配对只是中间表示，不能直接当作计数对象。

外部判断：待审。

## S03 · M1 · introduction.tex：h,v,rho 与 G

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

行反转是 h，列反转是 v，复合是半周旋转；指定四元群作用在实际砖集合上。


**Lean 入口：**
- [`Domino.RectangleSymmetry`](../../lean/Domino/Symmetry/Action.lean#L12)（structure，第 12 行）
- [`Domino.horizontal`](../../lean/Domino/Symmetry/Action.lean#L32)（def，第 32 行）
- [`Domino.vertical`](../../lean/Domino/Symmetry/Action.lean#L33)（def，第 33 行）
- [`Domino.halfTurn`](../../lean/Domino/Symmetry/Action.lean#L34)（def，第 34 行）
- [`Domino.cellAction`](../../lean/Domino/Symmetry/Action.lean#L44)（def，第 44 行）
- [`Domino.cellAction_horizontal`](../../lean/Domino/Symmetry/Action.lean#L62)（theorem，第 62 行）
- [`Domino.cellAction_vertical`](../../lean/Domino/Symmetry/Action.lean#L65)（theorem，第 65 行）
- [`Domino.cellAction_halfTurn`](../../lean/Domino/Symmetry/Action.lean#L68)（theorem，第 68 行）
- [`Domino.edgeAction`](../../lean/Domino/Symmetry/Action.lean#L87)（def，第 87 行）
- [`Domino.symmetry_card_four`](../../lean/Domino/Symmetry/Action.lean#L36)（theorem，第 36 行）

已核对：两个布尔位以 xor 相乘，反射用 Fin.rev；edgeAction 对无序格集合取像。

**外部审阅问题：**不要按 horizontal/vertical 的英文名称猜旋转方向；要看实际坐标公式。完整几何对称群与四坐标作用的对应仍需人工判断。

外部判断：待审。

## S04 · M1 · introduction.tex：a(n) 与四固定数

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

a(n) 是真实群作用商集的基数，d/h/v/r 为完整棋盘的普通数和固定集基数。


**Lean 入口：**
- [`Domino.TilingOrbit`](../../lean/Domino/Symmetry/Counting.lean#L12)（abbrev，第 12 行）
- [`Domino.ordinaryCount`](../../lean/Domino/Symmetry/Counting.lean#L16)（def，第 16 行）
- [`Domino.fixedCount`](../../lean/Domino/Symmetry/Counting.lean#L20)（def，第 20 行）
- [`Domino.orbitCount`](../../lean/Domino/Symmetry/Counting.lean#L18)（def，第 18 行）
- [`Domino.a`](../../lean/Domino/Symmetry/Counting.lean#L24)（def，第 24 行）
- [`Domino.orbitRel_iff_four`](../../lean/Domino/Symmetry/Counting.lean#L26)（theorem，第 26 行）

已核对：TilingOrbit 的参数 w 是实际宽度，三个 Count 的参数 n 是半宽；a=orbitCount 3，不由目标递推定义。

**外部审阅问题：**检查等价关系恰为四种像，固定条件为整个铺法 g • T=T，不要求每块砖逐块固定。

外部判断：待审。

## S05 · M1 · introduction.tex 与 half-board.tex：零尺寸

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

零宽只有空铺法；部分铺法在宽零时只能有空终端。


**Lean 入口：**
- [`Domino.empty_tiling_unique`](../../lean/Domino/Board/Tiling.lean#L120)（theorem，第 120 行）
- [`Domino.a_zero`](../../lean/Domino/Symmetry/Counting.lean#L60)（theorem，第 60 行）
- [`Domino.fixedCount_zero`](../../lean/Domino/Symmetry/Counting.lean#L62)（theorem，第 62 行）
- [`Domino.terminalHoles`](../../lean/Domino/Board/Partial.lean#L25)（def，第 25 行）
- [`Domino.PartialTiling`](../../lean/Domino/Board/Partial.lean#L42)（abbrev，第 42 行）
- [`Domino.partial_width_zero_nonempty_iff`](../../lean/Domino/Board/Partial.lean#L61)（theorem，第 61 行）
- [`Domino.partial_width_zero_card`](../../lean/Domino/Board/Partial.lean#L77)（theorem，第 77 行）

已核对：terminalHoles 在零宽总为空，额外守卫 w=0 → S=∅ 排除伪终端；不能省略。

**外部审阅问题：**检查空棋盘是抽象四元群的平凡作用；无需把空区域的几何等距群误认成四元群。

外部判断：待审。

## S06 · M1 · half-board.tex §3.1：部分铺法

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

末列的 S 行留空，其余格精确覆盖；S 是将来伸向右侧的横砖行集合。


**Lean 入口：**
- [`Domino.State`](../../lean/Domino/Board/Partial.lean#L11)（abbrev，第 11 行）
- [`Domino.reverseState`](../../lean/Domino/Board/Partial.lean#L13)（def，第 13 行）
- [`Domino.terminalHoles`](../../lean/Domino/Board/Partial.lean#L25)（def，第 25 行）
- [`Domino.mem_terminalHoles`](../../lean/Domino/Board/Partial.lean#L28)（theorem，第 28 行）
- [`Domino.PartialTiling`](../../lean/Domino/Board/Partial.lean#L42)（abbrev，第 42 行）
- [`Domino.partialEmptyEquivTiling`](../../lean/Domino/Board/Partial.lean#L52)（def，第 52 行）

已核对：洞条件 c.2.val+1=w 对应纸面末列；部分对象只含内部完整砖，不含半砖标签。空 S 与完整铺法等价。

**外部审阅问题：**请核对全体 S 的不交并不会重计，也没有误将半棋盘右边界要求为空。

外部判断：待审。

## S07 · M2 · half-board.tex 式 eq:Tm，三行特例

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

输入输出不交且剩余行可唯一竖直配对；T[p,q]∈{0,1}。


**Lean 入口：**
- [`Domino.ColumnRule`](../../lean/Domino/Transfer/ThreeRows.lean#L12)（def，第 12 行）
- [`Domino.Legal3`](../../lean/Domino/Transfer/ThreeRows.lean#L21)（def，第 21 行）
- [`Domino.legal3_iff_column_cover`](../../lean/Domino/Transfer/ThreeRows.lean#L34)（theorem，第 34 行）
- [`Domino.column_cover_unique`](../../lean/Domino/Transfer/ThreeRows.lean#L39)（theorem，第 39 行）
- [`Domino.transfer3`](../../lean/Domino/Transfer/ThreeRows.lean#L50)（def，第 50 行）
- [`Domino.columnCover_card`](../../lean/Domino/Transfer/ThreeRows.lean#L52)（theorem，第 52 行）

已核对：只验证三行，余集为 ∅、{0,1}、{1,2}；两个有限 decide 证明合法性充要和填法唯一。

**外部审阅问题：**不要把三行有限规则解释成任意高度扫描定理；它未枚举任意宽度的全部铺法。

外部判断：待审。

## S08 · M2 · half-board.tex §3.1：几何—路径双射

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

对全部实际宽度 w 与终端 S，部分铺法与起点空、终点 S 的合法路径互逆。


**Lean 入口：**
- [`Domino.StatePath`](../../lean/Domino/Transfer/PathEquiv.lean#L11)（structure，第 11 行）
- [`Domino.partialTilingEquivPath`](../../lean/Domino/Transfer/PathEquiv.lean#L76)（def，第 76 行）
- [`Domino.tilingEquivClosedPath`](../../lean/Domino/Transfer/PathEquiv.lean#L80)（def，第 80 行）
- [`Domino.partial_path_roundtrip`](../../lean/Domino/Transfer/PathEquiv.lean#L83)（theorem，第 83 行）
- [`Domino.path_partial_roundtrip`](../../lean/Domino/Transfer/PathEquiv.lean#L87)（theorem，第 87 行）
- [`Domino.partial_path_state`](../../lean/Domino/Transfer/PathEquiv.lean#L91)（theorem，第 91 行）

已核对：StatePath 使用 ℕ 索引，但 w 之后强制为空；逆构造依赖局部填法唯一性，不依赖预期计数。

**外部审阅问题：**沿 Bonds→Grid→Frame→PathEquiv 检查双向构造；仅有 card 相等不足以核对几何语义。

外部判断：待审。

## S09 · M2 · half-board.tex 式 eq:profile

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

q_w(S) 为实际部分铺法基数；按输入状态求和得到单列递推和矩阵表达。


**Lean 入口：**
- [`Domino.profileCount`](../../lean/Domino/Transfer/Count.lean#L81)（def，第 81 行）
- [`Domino.profile_count_path`](../../lean/Domino/Transfer/Count.lean#L83)（theorem，第 83 行）
- [`Domino.profile_count_zero`](../../lean/Domino/Transfer/Count.lean#L87)（theorem，第 87 行）
- [`Domino.profile_count_succ`](../../lean/Domino/Transfer/Count.lean#L90)（theorem，第 90 行）
- [`Domino.ordinary_count_profile`](../../lean/Domino/Transfer/Count.lean#L108)（theorem，第 108 行）

已核对：pathSuccEquiv 分拆最后一步后才取基数；T 的行是输入、列是输出，q 是行向量。

**外部审阅问题：**检查完整普通数使用宽度 2*n，而反射求和的半棋盘只使用宽度 n。

外部判断：待审。

## S10 · M3 · half-board.tex 引理 lem:half：实际对称

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

坐标反射作用转换为路径倒序，半周再加行反转。


**Lean 入口：**
- [`Domino.coverBonds_action`](../../lean/Domino/Symmetry/PathAction.lean#L22)（theorem，第 22 行）
- [`Domino.tilingPath_cut`](../../lean/Domino/Symmetry/PathAction.lean#L42)（theorem，第 42 行）
- [`Domino.tilingPath_horizontal`](../../lean/Domino/Symmetry/PathAction.lean#L56)（theorem，第 56 行）
- [`Domino.tilingPath_vertical`](../../lean/Domino/Symmetry/PathAction.lean#L72)（theorem，第 72 行）
- [`Domino.tilingPath_halfTurn`](../../lean/Domino/Symmetry/PathAction.lean#L102)（theorem，第 102 行）
- [`Domino.axial_fixed_iff_path`](../../lean/Domino/Symmetry/PathAction.lean#L127)（theorem，第 127 行）

已核对：先由实际坐标作用证明路径相容，再借几何—路径单射性刻画固定铺法，未把路径对称直接定义成几何对称。

**外部审阅问题：**核对切口下标 w-k 及边界；中线砖不能在限制中丢失。

外部判断：待审。

## S11 · M3 · half-board.tex 引理 lem:half：左右反射

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

Fix(v) 与所有终端部分铺法的不交并等价，补全与限制两向互逆。


**Lean 入口：**
- [`Domino.reflectionFixedEquivPartial`](../../lean/Domino/HalfBoard/Reflection.lean#L17)（def，第 17 行）
- [`Domino.completeReflection`](../../lean/Domino/HalfBoard/Reflection.lean#L21)（def，第 21 行）
- [`Domino.restrictReflection`](../../lean/Domino/HalfBoard/Reflection.lean#L24)（def，第 24 行）
- [`Domino.restrict_complete_reflection`](../../lean/Domino/HalfBoard/Reflection.lean#L27)（theorem，第 27 行）
- [`Domino.complete_restrict_reflection`](../../lean/Domino/HalfBoard/Reflection.lean#L31)（theorem，第 31 行）
- [`Domino.reflection_fixed_count`](../../lean/Domino/HalfBoard/Reflection.lean#L35)（theorem，第 35 行）

已核对：对所有 n，包括零宽；定义域没有额外终端对称条件。

**外部审阅问题：**请看等价类型和两条逆等式；不要把几何限制描述误读为必须没有跨中线砖。

外部判断：待审。

## S12 · M3 · half-board.tex 引理 lem:half：半周旋转

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

Fix(rho) 对应且仅对应 J(S)=S 的终端，不要求左半铺法自身对称。


**Lean 入口：**
- [`Domino.SymmetricTerminal`](../../lean/Domino/HalfBoard/HalfTurn.lean#L11)（abbrev，第 11 行）
- [`Domino.halfTurnFixedEquivPartial`](../../lean/Domino/HalfBoard/HalfTurn.lean#L13)（def，第 13 行）
- [`Domino.restrict_complete_halfTurn`](../../lean/Domino/HalfBoard/HalfTurn.lean#L23)（theorem，第 23 行）
- [`Domino.complete_restrict_halfTurn`](../../lean/Domino/HalfBoard/HalfTurn.lean#L27)（theorem，第 27 行）
- [`Domino.halfTurn_terminal_necessary`](../../lean/Domino/HalfBoard/HalfTurn.lean#L31)（theorem，第 31 行）
- [`Domino.halfTurn_extension_iff`](../../lean/Domino/HalfBoard/HalfTurn.lean#L35)（theorem，第 35 行）
- [`Domino.halfTurn_fixed_count`](../../lean/Domino/HalfBoard/HalfTurn.lean#L53)（theorem，第 53 行）

已核对：终端约束在 SymmetricTerminal 子类型；extension_iff 另证存在相同左半路径扩展的充要性。

**外部审阅问题：**核查必要性和充分性各自方向；不得把约束错误增强为左半对象固定于 h。

外部判断：待审。

## S13 · M3 · half-board.tex 引理 lem:half：补全的几何含义

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

左内部砖保持；跨中线砖恰对应 S；右内部砖为左侧的指定对称像。


**Lean 入口：**
- [`Domino.axial_restrict_internal`](../../lean/Domino/HalfBoard/Geometry.lean#L44)（theorem，第 44 行）
- [`Domino.axial_complete_internal`](../../lean/Domino/HalfBoard/Geometry.lean#L57)（theorem，第 57 行）
- [`Domino.axial_complete_terminal`](../../lean/Domino/HalfBoard/Geometry.lean#L64)（theorem，第 64 行）
- [`Domino.axial_complete_crossing`](../../lean/Domino/HalfBoard/Geometry.lean#L70)（theorem，第 70 行）
- [`Domino.axial_complete_right`](../../lean/Domino/HalfBoard/Geometry.lean#L76)（theorem，第 76 行）
- [`Domino.crossing_bond_same_row`](../../lean/Domino/HalfBoard/Geometry.lean#L84)（theorem，第 84 行）

已核对：Geometry 以 coverBonds 证明实际格对对应；跨线定理有 n>0 前提，零宽由 S05/S11/S12 单独覆盖。

**外部审阅问题：**这些定理是排除任意抽象等势双射的重要接口；核对 n-1,n 的零基中线坐标。

外部判断：待审。

## S14 · M3 · half-board.tex 引理 lem:h-odd 的 m=3 特例

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

三行 h 固定铺法唯一，因此 h_n=1。


**Lean 入口：**
- [`Domino.horizontal_fixed_no_vertical`](../../lean/Domino/HalfBoard/Horizontal.lean#L11)（theorem，第 11 行）
- [`Domino.horizontal_fixed_unique`](../../lean/Domino/HalfBoard/Horizontal.lean#L99)（theorem，第 99 行）
- [`Domino.horizontal_fixed_card_three`](../../lean/Domino/HalfBoard/Horizontal.lean#L110)（theorem，第 110 行）

已核对：竖砖的反射像共享中行格而冲突；再用路径唯一性证明全水平铺法唯一。

**外部审阅问题：**M1–M6 不覆盖该引理的一般奇数高度陈述；不能因正文写 m=2k+1 而把全引理标为已覆盖。

外部判断：待审。

## S15 · M4 · half-board.tex §3.3，E04：支持与基例

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

所有 j≥0 的偶/奇支持及各状态计数同时归纳，β₀=0。


**Lean 入口：**
- [`Domino.evenProfile`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L24)（def，第 24 行）
- [`Domino.oddProfile`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L27)（def，第 27 行）
- [`Domino.profilePair`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L45)（def，第 45 行）
- [`Domino.alpha`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L50)（def，第 50 行）
- [`Domino.beta`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L51)（def，第 51 行）
- [`Domino.profile_even_odd`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L58)（theorem，第 58 行）
- [`Domino.profile_even_support`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L86)（theorem，第 86 行）
- [`Domino.profile_odd_support`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L92)（theorem，第 92 行）

已核对：Lean 先递归定义 profilePair，再从 profile_count_zero/succ 归纳证明与实际基数一致；支持只是包含。

**外部审阅问题：**关键不是 alpha_succ 的 rfl，而是 profile_even_odd 的全指标桥接。请检查两个非空状态计数相等也在归纳中维持。

外部判断：待审。

## S16 · M4 · half-board.tex 式 eq:two-dimensional，E04：3,2,1,1

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

第一步来源求和给 α+β,α+β,α；第二步给 3α+2β,α+β。


**Lean 入口：**
- [`Domino.even_profile_step`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L30)（theorem，第 30 行）
- [`Domino.odd_profile_step`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L37)（theorem，第 37 行）
- [`Domino.alpha_succ`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L55)（theorem，第 55 行）
- [`Domino.beta_succ`](../../lean/Domino/ThreeRows/ProfileRecurrence.lean#L56)（theorem，第 56 行）
- [`Domino.alpha_eq_profile`](../../lean/Domino/ThreeRows/Ordinary.lean#L15)（theorem，第 15 行）
- [`Domino.beta_eq_profile`](../../lean/Domino/ThreeRows/Ordinary.lean#L18)（theorem，第 18 行）
- [`Domino.profile_matrix_recurrence`](../../lean/Domino/ThreeRows/Ordinary.lean#L57)（theorem，第 57 行）

已核对：纸面 {1,2} 对应代码 {0,1}，β 是单状态计数；二维矩阵使用列向量。

**外部审阅问题：**系数 2 来自两类各 β 个对象，不是某一非空状态有两条回空路径。新稿展开与这两个 step 定理逐项对应。

外部判断：待审。

## S17 · M4 · half-board.tex 式 eq:d-rec

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

d_j=α_j；d₀=1,d₁=3，d_(j+2)=4d_(j+1)-d_j。


**Lean 入口：**
- [`Domino.ordinary_eq_alpha`](../../lean/Domino/ThreeRows/Ordinary.lean#L11)（theorem，第 11 行）
- [`Domino.ordinary_recurrence_add`](../../lean/Domino/ThreeRows/Ordinary.lean#L25)（theorem，第 25 行）
- [`Domino.ordinary_recurrence_bound`](../../lean/Domino/ThreeRows/Ordinary.lean#L29)（theorem，第 29 行）
- [`Domino.ordinary_recurrence_int`](../../lean/Domino/ThreeRows/Ordinary.lean#L38)（theorem，第 38 行）
- [`Domino.ordinary_initial_values`](../../lean/Domino/ThreeRows/Ordinary.lean#L43)（theorem，第 43 行）
- [`Domino.profile_matrix_characteristic`](../../lean/Domino/ThreeRows/Ordinary.lean#L62)（theorem，第 62 行）

已核对：先证自然数加法式及下界，再给整数/减法式；不是从有限数值拟合递推。

**外部审阅问题：**纸面以矩阵特征式消元，代码亦有矩阵证书，但计数递推通过已桥接 α、β 直接消元；两种证明组织不必逐行相同。

外部判断：待审。

## S18 · M4 · half-board.tex 式 eq:parity-fixed

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

v_(2j)=d_(j+1)-2d_j，v_(2j+1)=d_(j+1)，r_(2j)=r_(2j+1)=d_j。


**Lean 入口：**
- [`Domino.reflection_even_add`](../../lean/Domino/ThreeRows/FixedCounts.lean#L42)（theorem，第 42 行）
- [`Domino.reflection_even_bound`](../../lean/Domino/ThreeRows/FixedCounts.lean#L47)（theorem，第 47 行）
- [`Domino.fixed_counts_parity`](../../lean/Domino/ThreeRows/FixedCounts.lean#L65)（theorem，第 65 行）

已核对：从真实终端求和并用支持归纳得到；先证明减法下界。

**外部审阅问题：**纸面只说可达的 J 固定状态；全部八状态中还有不可达的 J 固定状态，不能误删一般终端条件。

外部判断：待审。

## S19 · M5 · introduction.tex 引理 lem:burnside

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

实际群作用满足 4a=d+h+v+r，且和可被 4 整除，无忠实性要求。


**Lean 入口：**
- [`Domino.four_mul_orbitCount`](../../lean/Domino/Symmetry/Burnside.lean#L23)（theorem，第 23 行）
- [`Domino.fixed_sum_divisible_four`](../../lean/Domino/Symmetry/Burnside.lean#L35)（theorem，第 35 行）
- [`Domino.orbitCount_eq_average`](../../lean/Domino/Symmetry/Burnside.lean#L39)（theorem，第 39 行）
- [`Domino.orbitCount_average_rat`](../../lean/Domino/Symmetry/Burnside.lean#L45)（theorem，第 45 行）

已核对：调用 mathlib 的有限群作用 Burnside，商集与固定集都显式接回 M1 基数；先乘法后除法。

**外部审阅问题：**一般高度参数仅说明指定四元群的作用；不能据此将正方形解释为完整 D4 轨道。

外部判断：待审。

## S20 · M5 · half-board.tex 式 eq:parity-orbits 与边界

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

轨道奇偶式；空棋盘计一次，3×2 的 (d,h,v,r,a)=(3,1,3,1,2)。


**Lean 入口：**
- [`Domino.four_mul_a`](../../lean/Domino/ThreeRows/OrbitCounts.lean#L12)（theorem，第 12 行）
- [`Domino.orbit_even_add`](../../lean/Domino/ThreeRows/OrbitCounts.lean#L16)（theorem，第 16 行）
- [`Domino.orbit_odd_mul`](../../lean/Domino/ThreeRows/OrbitCounts.lean#L23)（theorem，第 23 行）
- [`Domino.orbit_even_rat`](../../lean/Domino/ThreeRows/OrbitCounts.lean#L56)（theorem，第 56 行）
- [`Domino.orbit_odd_rat`](../../lean/Domino/ThreeRows/OrbitCounts.lean#L62)（theorem，第 62 行）
- [`Domino.width_two_counts`](../../lean/Domino/ThreeRows/Boundary.lean#L24)（theorem，第 24 行）
- [`Domino.three_row_small_orbit_counts`](../../lean/Domino/ThreeRows/Boundary.lean#L22)（theorem，第 22 行）

已核对：从 Burnside 和固定数推出，低维作用可以不忠实；n=1 的轨道数不是普通铺法数 3。

**外部审阅问题：**请将 q 的宽度、d 的半宽、a 的半宽分开核对，尤其 v_(2j) 对应完整 3×4j。

外部判断：待审。

## S21 · M6 · introduction.tex 形式幂级数约定

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

A 的系数为真实 a(n)；D/H/V/R 也由真实普通/固定基数构造。


**Lean 入口：**
- [`Domino.countSeries`](../../lean/Domino/Series/Basic.lean#L15)（def，第 15 行）
- [`Domino.coeff_countSeries`](../../lean/Domino/Series/Basic.lean#L17)（theorem，第 17 行）
- [`Domino.orbitSeries`](../../lean/Domino/ThreeRows/Series.lean#L19)（def，第 19 行）
- [`Domino.coeff_orbitSeries`](../../lean/Domino/ThreeRows/Series.lean#L21)（theorem，第 21 行）
- [`Domino.ordinarySeries`](../../lean/Domino/ThreeRows/Series.lean#L14)（def，第 14 行）
- [`Domino.horizontalSeries`](../../lean/Domino/ThreeRows/Series.lean#L16)（def，第 16 行）
- [`Domino.verticalSeries`](../../lean/Domino/ThreeRows/Series.lean#L17)（def，第 17 行）
- [`Domino.halfTurnSeries`](../../lean/Domino/ThreeRows/Series.lean#L18)（def，第 18 行）

已核对：PowerSeries ℚ，系数为自然数基数的有理数像；不需要解析收敛。

**外部审阅问题：**检查目标有理函数不是序列定义，也没有先假设目标递推。

外部判断：待审。

## S22 · M6 · half-board.tex 第二证明：移位与奇偶插零

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

D(X²) 用 expand 2；(D(X²)-1)/X² 是系数移位，不是 X 的单位逆。


**Lean 入口：**
- [`Domino.doubleSeries`](../../lean/Domino/Series/Basic.lean#L46)（def，第 46 行）
- [`Domino.coeff_doubleSeries_even`](../../lean/Domino/Series/Basic.lean#L49)（theorem，第 49 行）
- [`Domino.coeff_doubleSeries_odd`](../../lean/Domino/Series/Basic.lean#L53)（theorem，第 53 行）
- [`Domino.ordinary_shift_identity`](../../lean/Domino/ThreeRows/Series.lean#L30)（theorem，第 30 行）
- [`Domino.even_shift_identity`](../../lean/Domino/ThreeRows/Series.lean#L54)（theorem，第 54 行）
- [`Domino.vertical_series_parity_add`](../../lean/Domino/ThreeRows/Series.lean#L70)（theorem，第 70 行）
- [`Domino.halfTurn_series_parity`](../../lean/Domino/ThreeRows/Series.lean#L64)（theorem，第 64 行）

已核对：先证 X E=D-1 和 X² E(X²)=D(X²)-1，再得到固定点恒等式。

**外部审阅问题：**请核对所有移位零次项；非零形式幂级数不一定可逆，X 的常数项为零。

外部判断：待审。

## S23 · M6 · half-board.tex 第二证明与 formalization.tex：四固定级数

论文位置：[中文源码](../../papers/zh/sections/half-board.tex) · [英文源码](../../papers/en/sections/half-board.tex)

四类固定点级数满足各自的分母乘法式，Burnside 逐系数提升为 4A=D+H+V+R。


**Lean 入口：**
- [`Domino.ordinary_series_identity`](../../lean/Domino/ThreeRows/Series.lean#L23)（theorem，第 23 行）
- [`Domino.fixed_series_identities`](../../lean/Domino/ThreeRows/Series.lean#L95)（theorem，第 95 行）
- [`Domino.burnside_series_identity`](../../lean/Domino/ThreeRows/Main.lean#L13)（theorem，第 13 行）

已核对：各式由 M4 全指标结论与 M5 实际 Burnside 得到，非有限展开比较。

**外部审阅问题：**检查 V/R 的奇偶分支、系数域以及四个分母常数项；此处不使用基本块路线结论。

外部判断：待审。

## S24 · M6 · introduction.tex 式 eq:main；formalization.tex

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

B=(1-X)(1-4X+X²)(1-4X²+X⁴)，N=1-3X-4X²+10X³-4X⁵+X⁶，BA=N，A=NB⁻¹。


**Lean 入口：**
- [`Domino.orbitDenom`](../../lean/Domino/ThreeRows/Algebra.lean#L15)（def，第 15 行）
- [`Domino.orbitNumerator`](../../lean/Domino/ThreeRows/Algebra.lean#L16)（def，第 16 行）
- [`Domino.common_numerator_identity`](../../lean/Domino/ThreeRows/Algebra.lean#L28)（theorem，第 28 行）
- [`Domino.orbitDenom_constant`](../../lean/Domino/ThreeRows/Algebra.lean#L35)（theorem，第 35 行）
- [`Domino.orbitDenom_isUnit`](../../lean/Domino/ThreeRows/Algebra.lean#L38)（theorem，第 38 行）
- [`Domino.orbit_series_identity`](../../lean/Domino/ThreeRows/Main.lean#L20)（theorem，第 20 行）
- [`Domino.orbit_series_rational`](../../lean/Domino/ThreeRows/Main.lean#L34)（theorem，第 34 行）
- [`Domino.orbit_series_paper`](../../lean/Domino/ThreeRows/Main.lean#L38)（theorem，第 38 行）

已核对：纯代数模块不导入计数结论；B(0)=1 后取逆，原题符号排列分母常数项为 -1。

**外部审阅问题：**请同时核对正负号、半宽指数与单位条件。机器不负责确认文献首次性。

外部判断：待审。

## S25 · M6 · introduction.tex 式 eq:recurrence 与七项初值

论文位置：[中文源码](../../papers/zh/sections/introduction.tex) · [英文源码](../../papers/en/sections/introduction.tex)

对全部自然数 n 在 ℤ 中证明 a(n+7)=5a(n+6)-a(n+5)-19a(n+4)+19a(n+3)+a(n+2)-5a(n+1)+a(n)。


**Lean 入口：**
- [`Domino.orbitLag`](../../lean/Domino/ThreeRows/Recurrence.lean#L14)（def，第 14 行）
- [`Domino.orbit_coefficient_equation`](../../lean/Domino/ThreeRows/Recurrence.lean#L16)（theorem，第 16 行）
- [`Domino.orbit_recurrence_seven`](../../lean/Domino/ThreeRows/Recurrence.lean#L36)（theorem，第 36 行）
- [`Domino.orbit_recurrence_seven_add`](../../lean/Domino/ThreeRows/Recurrence.lean#L41)（theorem，第 41 行）
- [`Domino.orbit_initial_values`](../../lean/Domino/ThreeRows/Recurrence.lean#L47)（theorem，第 47 行）
- [`Domino.orbit_recurrence_first`](../../lean/Domino/ThreeRows/Recurrence.lean#L69)（theorem，第 69 行）
- [`Domino.three_row_main_theorem`](../../lean/Domino/ThreeRows/Recurrence.lean#L76)（theorem，第 76 行）

已核对：从 BA=N 取系数；n+7 时分子系数为零，0..6 解出完整初值，a(7)=2037。

**外部审阅问题：**整数强制转换必须涵盖所有负项；论文 n≥7 与代码 n+7（n≥0）量词等价。没有证明七阶最小。

外部判断：待审。
