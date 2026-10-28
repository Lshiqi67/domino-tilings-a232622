# M1：棋盘、部分铺法与四元群作用

> 本文保留所标日期的阶段记录与当时待办；当前 M1–M11 已完成，英文 v2.1 已对应这些结果，见 [当前进度](progress.md)。

> 本文保留该阶段形成时的范围与后续计划；当前 M1–M6 均已完成本地验收，发布说明见 [进度表](progress.md)。

日期：2026-10-25。路线：P002 / A002 半棋盘路线。状态：**M1 已完成本地 Lean 构建、公理审计及定义语义核对；三行主计数定理尚未完成形式化。**

## 1 本轮目标与实际范围

原目标是对所有自然数 n 证明三行棋盘轨道数的生成函数、递推和初值。本轮仅完成其基础对象层：任意自然数高度 m、实际宽度 w 的格子、无序砖、精确覆盖、完整与部分铺法，四种坐标对称及实际轨道/固定点计数。定义允许 m=0、w=0；完整矩形几何对称的论文解释限于正奇数高度和正偶数宽度。

构建与审计证据见 [M1 核验记录](../evidence/m1-2026-10-25/README.md)，机器可读输出见 [验收报告](../evidence/m1-2026-10-25/verification-02/report.json)。全部显式声明及源码行号见 [111 项声明清单](m1-declarations.json)。其中有 61 个 `theorem`、28 个 `def`、14 个命名 `instance`、7 个 `abbrev` 和 1 个 `structure`；这不等于证明了 111 个论文定理。

## 2 模块与依赖

```text
Domino/Board/Basic.lean
  └─ Board/Tiling.lean
       ├─ Board/Examples.lean
       └─ Board/Partial.lean
            └─ Symmetry/Action.lean
                 └─ Symmetry/Counting.lean
Domino.lean                 导入上述全部模块与原 Environment
Domino/Audit/M1.lean        导入 Domino，逐声明 #print axioms
```

`PartialTiling` 放在 `Board/Partial.lean`，因为它是独立于转移路径的几何对象。M2 的 `Transfer/` 将复用它，再定义局部规则与路径；不重复定义另一种“部分铺法”。`Counting.lean` 在 M1 仅建立计数的对象语义与零宽值；Burnside 等式仍归 M5。

| 文件 | 主要接口与已证明事实 |
| --- | --- |
| [Board/Basic](../Domino/Board/Basic.lean) | `Cell`、`Adjacent`、两种坐标反射；邻接对称、非自邻接，反射对合/交换并保持邻接 |
| [Board/Tiling](../Domino/Board/Tiling.lean) | `Edge`、`Cover`、`Tiling`；端点交换不变、砖恰含两格、覆盖唯一性与避洞、有限性、零宽/零高唯一铺法 |
| [Board/Partial](../Domino/Board/Partial.lean) | `State`、`reverseState`、`terminalHoles`、`PartialTiling`；状态反转对合、宽零守卫、空终端与完整铺法等价 |
| [Board/Examples](../Domino/Board/Examples.lean) | 构造 1×2 横砖与 2×1 竖砖铺法，证明 1×1 不可铺、对角两格不邻接 |
| [Symmetry/Action](../Domino/Symmetry/Action.lean) | 四元交换群、格子与砖的置换、任意带洞覆盖的搬移、完整铺法上的 `MulAction` |
| [Symmetry/Counting](../Domino/Symmetry/Counting.lean) | 铺法商类型、实际普通/固定点/轨道基数、四种对称的轨道关系刻画、空棋盘计数 |

## 3 与原题的语义核对

### 坐标、无序性与覆盖

`Cell m w := Fin m × Fin w` 使用零基坐标。`Adjacent a b` 表示同行而列差 1，或同列而行差 1；自然数上的相邻以 `x+1=y ∨ y+1=x` 表示，不使用截断减法定义距离。没有对角砖、周期边界或越界格。

`Edge m w` 是有限格子集合的子类型，要求集合等于相邻两格组成的 `{a,b}`。`edge_card_two` 证明恰有两格，`edgeOfAdjacent_swap` 证明端点交换给出同一块砖。铺法使用砖的 `Finset`，不记录砖编号或放置顺序，也没有 tatami 附加条件。

`IsCover H E` 要求覆盖到的格恰为 H 的补集，并要求共享格子的两块砖相等。由此证明 `cover_exactly_one` 与 `cover_avoids_holes`；空洞集时，`isCover_empty_iff` 给出“每格恰被一块砖覆盖”的双向等价。这与计划中的逐格覆盖数定义等价，但免于在每步证明中计算过滤集合基数。

`Cover`、`Tiling` 等是上述有效对象的子类型，不是另加“覆盖正确”假设的任意砖集合。有限性由有限棋盘、有限子集及其子类型取得。部分 `Fintype` 实例使用经典选择；本轮没有声称提供可执行的完整铺法枚举器。

### 末列洞与宽零守卫

`terminalHoles m w S = {(r,c) | c+1=w 且 r∈S}`。`PartialTiling m w S` 是覆盖此洞集的内部完整砖集合，再附条件 `w=0 → S=∅`。半块只是末列未覆盖格的标记，不增加越界格或另一种砖。

关键出口对全部 m、w、S 成立：

- `partialEmptyEquivTiling m w`：空终端的部分铺法与完整铺法互逆等价。
- `partial_width_zero_nonempty_iff`：零宽部分对象存在当且仅当 S 为空。
- `partial_width_zero_card`：零宽基数在 S 为空时为 1，否则为 0。
- `reverseState_twice`：行集合反转两次恢复原状态。

守卫不可删除：零宽没有末列，洞集对任意 S 都为空；若只保留洞集，非空终端会错误地产生一个空对象。M1 已排除这一建模错误。

### 四元群、商与计数

`RectangleSymmetry` 由两个布尔位表示是否反转行、列，乘法为逐位异或。群律、四元素穷尽、群基数为 4 已证明；不是把待证群律当作公理。`horizontal` 反转行，对应上下反射；`vertical` 反转列，对应左右反射；`halfTurn` 同时反转两者。

零基行反转为 `m-1-r`，加回 1 后得到论文的一基公式 `m+1-(r+1)`；三行即 `4-r₁`。列反转同理。代码通过 `Fin.rev` 保证坐标仍在棋盘内；其保持邻接性已在 Lean 中证明。

作用依次提升到无序砖、砖集合和完整覆盖。`isCover_map` 还证明同时搬移洞集与砖集保持任意带洞覆盖。`rectangle_action` 的单位律、乘法律来自实际集合映射；空棋盘上的四个群元素均固定唯一铺法。不要求该作用忠实。

`TilingOrbit m w` 是真实 `Tiling m w` 对轨道等价关系取商。`orbitRel_iff_four` 证明等价恰为恒等、上下反射、左右反射、半周旋转四种情形之一。计数定义为：

```lean
ordinaryCount m n = Fintype.card (Tiling m (2*n))
orbitCount m n = Fintype.card (TilingOrbit m (2*n))
fixedCount m n g = Fintype.card {T : Tiling m (2*n) // g • T = T}
a n = orbitCount 3 n
```

这里 n 是半宽，`PartialTiling` 的 w 是实际列数。没有用目标递推或预期答案定义轨道数。已证明 `ordinaryCount m 0 = orbitCount m 0 = fixedCount m 0 g = 1`，特别 `a 0 = 1`。

`three_ne_even_width` 和 `odd_height_ne_even_width` 证明相关边长不等；本轮没有建立欧氏平面全等距变换分类。对正方形也能使用此四元群作用，但其轨道数不应解读为正方形完整八元对称群的轨道数。上述是人工语义核对及明确形式化范围，不把人工几何解释伪装成 Lean 定理。

## 4 原证明链的覆盖边界

M1 的所有几何对象与作用要求已完成。原 C00 同时打包了几何对象与形式幂级数约定，因此 [覆盖表](coverage.json) 将 **M1 标为 checked、C00 总节点标为 partial**：本轮几何部分已核验，具体系数级数的表示留在 M6。原方案表中“C00 完整”据此细化为“C00 几何基础完整”，不把整个原节点提前标为通过。

T04 只新增零宽完整/部分铺法与固定点/轨道边界的形式化证据；3×2 的 `(3,1,3,1,2)` 计数及 k=1 基本块边界仍待对应阶段。B01 的输入对象已存在，但几何路径双射与转移计数递推仍为 planned；L001—L011 均未因本轮对象层完成而整条升级。

## 5 复现、审计与信任范围

在 `lean` 目录使用已固定的 Lean/mathlib 4.35.0，运行：

```powershell
python -X utf8 scripts/check_m1.py --report-dir checks/m1-rerun-new
```

报告目录必须尚不存在。脚本核对声明清单与审计入口、实际工具版本、九个锁定依赖的提交和已跟踪源码状态、覆盖表 DAG，执行 `lake --wfail build`、入口检查及逐声明 `#print axioms`，保存命令、退出码、日志、源码 SHA-256 和公理映射。未更改工具链、mathlib 或 manifest。

111 项显式声明及其传递依赖只出现标准基础 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`、自设数学公理或 `native_decide` 所需的额外信任。小有限群与固定例子中的 `decide` 产生内核可检查证明。公理审计不代替定义与原题的语义核对，本文件第 3 节单独记录后者。

新增 [CI 工作流](../../.github/workflows/lean.yml) 在未来 push/PR 时恢复固定工具链与 mathlib 缓存，再调用同一 M1 检查并保存报告。设置方式核对了 [Lean Action 官方说明](https://github.com/leanprover/lean-action/blob/v1/README.md)（2026-10-25）。**本轮只保存本地；没有推送或触发远端 CI，不声称 CI 已通过。**

## 6 下一项可执行工作：M2

在 `Transfer/` 依次实现三行单列填充、合法状态对及竖直补全唯一性，定义从空状态到 S 的长度 w 路径，再构造与 `PartialTiling 3 w S` 的双向映射并证明两个逆等式。由空终端特例取得完整铺法的路径等价，最后推出计数递推。

M2 必须直接复用本轮几何对象和零宽定理，特别检查跨列砖的拆分/恢复。半棋盘反射与半周补全留在 M3；主生成函数和七阶递推留在 M6。本轮没有改动论文、历史证明或旧核验报告。
