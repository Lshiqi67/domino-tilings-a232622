# M2：三行局部规则、几何路径双射与计数递推

> 本文保留该阶段形成时的范围与后续计划；当前 M1–M6 均已完成本地验收，发布说明见 [进度表](progress.md)。

日期：2026-10-25。路线：P002 / A002。**M2 已完成本地 Lean 验证，原证明链 C01、A01、B01 已覆盖；论文主生成函数、七阶递推和对称固定点公式仍待后续阶段。**

## 1 精确范围与出口

高度固定为 3，实际列数 w 为任意自然数，终端 S 为任意 `Fin 3` 的子集。复用 M1 的无序砖、精确覆盖和 `PartialTiling`，不改原计数对象；包括 w=0、空终端和非空终端、奇偶宽度。论文中的半宽 n 仅在普通数接口处转换为 `w=2*n`。

| 出口 | 已证明内容 |
| --- | --- |
| `legal3_iff_column_cover` | 输入 p 与输出 q 合法，当且仅当存在恰好覆盖剩余行的竖砖选择 |
| `column_cover_unique` | 给定输入输出后，列内竖砖选择唯一 |
| `partialTilingEquivPath w S` | `PartialTiling 3 w S ≃ StatePath w S`，两个方向互逆 |
| `tilingEquivClosedPath w` | `Tiling 3 w ≃ StatePath w ∅`，适用全部宽度 |
| `partial_path_roundtrip`、`path_partial_roundtrip` | 两个复合分别等于恒等，没有只证明单向注入 |
| `partial_path_state` | 路径的第 k 个状态确为从几何配对提取的跨切口行集合，末状态保留指定洞集 |
| `pathSuccEquiv w q` | 长度 w+1、末状态 q 的路径与“前缀路径＋最后一步”互逆 |
| `profile_count_zero`、`profile_count_succ` | 真实部分铺法基数的初值及逐列转移递推 |
| `profile_count_matrix`、`tiling_count_matrix` | 实际部分/完整铺法数等于转移矩阵幂的相应元素 |

新增 8 个模块、111 项显式声明，其中 61 个定理。累计 M1+M2 为 14 个数学模块、222 项显式声明，其中 122 个定理。声明数包括类型和定义，不等于论文定理数。源码行号见 [清单](m2-declarations.json)，完整构建、公理审计及复现命令见 [M2 核验记录](../evidence/m2-2026-10-25/README.md)。

## 2 目录和证明顺序

```text
Transfer/Bonds.lean       有限砖覆盖 ↔ 有向相邻配对关系
Transfer/ThreeRows.lean   三行局部覆盖与合法转移，唯一竖直补全
Transfer/Grid.lean        配对关系改用自然数列坐标；棋盘外关系为空
Transfer/Links.lean       切口与竖砖产生的相邻关系、每格度数为一
Transfer/Frame.lean       几何配对 ↔ 全部列的切口和竖砖，双向重建
Transfer/PathEquiv.lean   唯一竖砖信息消去，得到纯状态路径等价
Transfer/Count.lean       末步分拆、实际基数递推和矩阵幂公式
Transfer/Examples.lean    12 条转移及少量边界计数的形式化推论
```

代码集中在 [Transfer 入口](../Domino/Transfer/PathEquiv.lean)，总入口 [Domino.lean](../Domino.lean) 导入所有已实现模块；逐声明审计独立放在 [Audit/M2.lean](../Domino/Audit/M2.lean)。M1 六个数学源文件和工具链/依赖锁保持原字节，不通过更换铺法定义简化本阶段任务。

## 3 定义语义核对

### 局部规则

零基行号为 0、1、2。列内只有两种竖砖：0–1 和 1–2，以 `Fin 2` 的子集表示所选竖砖。`ColumnRule p q v` 要求每一行收到的输入水平半砖、输出水平半砖及所选竖砖的覆盖总数恰为 1。

`Legal3 p q` 明确为 p、q 不交，且未被 p∪q 占用的行集合恰为 ∅、{0,1} 或 {1,2}。对全部 64 个状态对、全部 4 个竖砖选择，Lean 的 `decide` 证明存在性等价和唯一性；另证明 64 对中恰有 12 条合法转移。这里的有限穷尽产生内核可检查证明，没有调用 `native_decide` 或依赖外部枚举器。

局部模型与实际几何的连接由 `GridLink` 的相邻性、`columnRule_iff_unique_neighbors` 及 `Frame` 中的双向构造给出，不能只凭局部真值表把路径计数等同于铺法计数。

### 从无序砖到列分解

`coverEquivBonds` 将每块无序砖 {a,b} 对应到两个有向配对 (a,b)、(b,a)，证明有效覆盖恰给出对称、相邻、避洞且每个非洞格有唯一邻格的关系；逆向按无序对恢复砖集合。两向互逆排除了端点顺序和砖标号造成的重计。

`partialEquivGrid` 仅把有限列坐标换成自然数坐标，关系在棋盘外为空，并保留宽零守卫。`GridMatching.live` 与对称性保证任何实际配对的两个端点都在棋盘内；它不是另加未经证明的“几何双射正确”假设。

`ColumnFrame` 保存每个切口的行集合和每列的竖砖。`gridH` 提取内部跨列配对，并在右边界记录指定 S；`gridV` 提取两种竖直配对。辅助 `GridCompletion` 在逻辑关系中给末列洞配上终端标记，用于统一“每格恰有一个邻格”的局部证明；恢复实际棋盘时明确要求两个端点均在宽度 w 内，**不会向 M1 的砖集合加入越界砖**。

`grid_frame_roundtrip`、`frame_grid_roundtrip` 以及横/竖信息的分别恢复证明共同建立 `gridEquivFrame`。本轮的 `GridCompletion` 只是末列标记辅助关系，不是 M3 的反射或半周旋转补全。

### 纯状态路径和零宽

`StatePath w S` 只记录状态函数，要求第 0 个状态为空、第 w 个状态为 S、每个 k<w 的相邻状态满足 `Legal3`。为避免不断转换 `Fin` 下标，使用自然数索引，并把 k>w 的状态固定为空；这只是有限路径的统一延拓约定。`pathCode_injective` 将它嵌入长度 w+1 的有限状态数组，证明对象有限。

`frameEquivPath` 用已证明的列填充唯一性消去竖砖信息；逆向用局部存在性选择填充，再由唯一性证明恢复原填充。最终 `partialTilingEquivPath` 是已经验证的等价的复合，不以递推式或预期基数定义铺法。

w=0 时起点与终点必须相等，所以只有 S=∅ 才有对象；这是 M1 宽零守卫在路径端的对应。几何和路径的等价对全部 w、S 一次证明，没有只验证有限宽度后外推。

## 4 真实计数及矩阵方向

定义

$$q_w(S)=\operatorname{card}(\texttt{PartialTiling}\;3\;w\;S),\qquad T[p,q]=[\texttt{Legal3}\;p\;q].$$

先证明路径前缀/追加一步的两个逆等式，取得按倒数第二个状态 p 分类的有限不交并；再通过几何路径等价取基数，得到

$$q_0(S)=[S=\varnothing],\qquad q_{w+1}(q)=\sum_p q_w(p)T[p,q],$$
$$q_w(S)=(T^w)[\varnothing,S],\qquad |\texttt{Tiling}\;3\;w|=(T^w)[\varnothing,\varnothing].$$

第一指标为输入、第二指标为输出，计数向量按行向量右乘 T。`ordinary_count_profile` 另外给出 `ordinaryCount 3 n = profileCount (2*n) ∅`，不混用实际宽度和半宽。

`profileEval` 是供小范围计算的递推函数；`profile_count_eval` 在一般计数递推之后证明它等于真实基数。因此下列有限推论有一般双射作为依据：宽 1 时只有终端 {0}、{2}、全三行各计 1，其余为 0；完整三行棋盘宽 0、1、2、3、4 的普通铺法数为 1、0、3、0、11。这些不是对称轨道数。

## 5 验收与剩余范围

固定 Lean 4.35.0 和 mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。完整 `lake --wfail build` 通过（3164 个含依赖的构建任务）；222 项声明及传递依赖的公理审计只出现 `propext`、`Classical.choice`、`Quot.sound`。没有源码占位证明、自设数学公理或额外计算信任。

[最终报告](../evidence/m2-2026-10-25/verification-01/report.json) 记录 M1 回归、九个固定依赖、覆盖表 DAG、入口、全部公理及源码哈希。定义的题面对应由同一助手逐项核对，尚无外部人工审阅。本轮未修改论文、原证明或旧报告，未重跑历史 Python 铺法枚举，也未对外发布；CI 配置已改为调用 M2 验收，未运行远端 CI。

C01、A01、B01 升级为 checked，L001 取得三行全部宽度的形式化证据。C00 保留幂级数部分的缺口；T04 只增加普通小棋盘计数的子项证据，3×2 的四类固定点和轨道数仍未完成。L006/L007/L008 等其他引理没有自动升级。

## 6 下一项工作：M3

依次建立左右反射补全与限制、半周旋转补全与限制的互逆等价；半周定义域必须恰为 `reverseState S = S`，不要求左半部分本身上下对称。再处理三行上下反射固定铺法唯一性。目标是 B02、B03、B04，统一包含零半宽。

可复用 `partialTilingEquivPath`、`partial_path_state` 和 `profile_count_succ`，但 M3 的几何固定点条件仍须针对 M1 的实际群作用证明。二阶压缩、Burnside 和主生成函数继续分别归 M4、M5、M6。
