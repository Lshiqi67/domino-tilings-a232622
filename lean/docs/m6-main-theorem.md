# M6：三行主生成函数、七阶递推与完整初值

日期：2026-10-25。继续 A002 半棋盘路线，复用 M1–M5 的实际铺法、群作用、几何双射和计数公式。最终证据见[验收报告](../evidence/m6-2026-10-25/verification-02/report.json)与[核验记录](../evidence/m6-2026-10-25/README.md)。本阶段验证三行主计数定理；全文推广、基本块第二证明及外部人工审阅仍待完成。

## 最终命题与原题对应

`a n` 保持 M1 定义：真实 `Tiling 3 (2*n)` 在上下反射、左右反射与半周旋转生成的四元群作用下，商类型的基数。砖为相邻两格的无序集合，每格恰好覆盖一次，不增加 tatami 限制或砖标签。零宽为空铺法，a(0)=1。

在 `PowerSeries ℚ` 中定义 `orbitSeries := countSeries a`，`coeff_orbitSeries n` 证明其第 n 个系数恰为实际 a(n) 的有理数像。指数 n 表示完整棋盘半宽，不是列数 2n。级数由系数函数构造，不涉及解析收敛。

令

$$P=1-4X+X^2,\qquad Q=1-4X^2+X^4,$$
$$B=(1-X)PQ,\qquad N=1-3X-4X^2+10X^3-4X^5+X^6.$$

`orbit_series_identity` 证明 **B·A=N**；`orbitDenom_constant` 证明 B 的常数项为 1，`orbitDenom_isUnit` 证明它可逆，`orbit_series_rational` 得 **A=N·B⁻¹**。没有把非零常数项条件省略为“任意非零级数都可逆”。

`orbit_series_paper` 直接给出题面原始符号排列：

$$A=\bigl(-1+3X+4X^2-10X^3+4X^5-X^6\bigr)
\bigl((X-1)(X^2-4X+1)(X^4-4X^2+1)\bigr)^{-1}.$$

这里倒数是形式幂级数的单位逆；原始分母常数项为 −1。两个符号版本都已在 Lean 中证明。没有把目标公式当作 a 的新定义，也没有增加“假设双射正确”“假设递推成立”等待证前提。

对全部自然数 n，`orbit_recurrence_seven` 在整数中证明

$$a(n+7)=5a(n+6)-a(n+5)-19a(n+4)+19a(n+3)
+a(n+2)-5a(n+1)+a(n).$$

同时给出有理数版本和自然数无减法版本，避免截断减法。`orbit_initial_values` 证明

$$a(0),\ldots,a(6)=1,2,5,14,46,156,561.$$

`orbit_recurrence_first` 在递推起点给出 a(7)=2037。`three_row_main_theorem` 将生成函数乘法式、可逆分式、全部指标递推和七项初值汇总为一个无额外假设的定理。

原题的非空 3×2n 棋盘不为正方形，本实现使用题面明确列出的四种坐标对称；没有另行形式化欧氏平面全部等距变换的分类。空棋盘使用同一个抽象四元群的平凡作用。形式化确认的是这些明确对象和等价关系下的主计数结论，不认证文献优先权、全球开放状态或全文其他结论。

## 证明链

1. `Series/Basic` 以系数外延证明普通二阶递推对应的级数恒等式；分别处理系数 0、1 和 n+2。`series_shift` 分离常数项。`doubleSeries` 使用 mathlib 的 `expand 2` 代数同态，逐系数证明偶数位置保留、奇数位置为零及乘 X 后的奇偶位置。
2. `ThreeRows/Series` 的 D、H、V、R 均按实际普通数或固定点数定义。用 M4 二阶递推得到 P·D=1−X。令 E 的第 n 项为 d_(n+1)，证明 X·E=D−1，借乘 X 的单射性得到 P·E=3−X；这里没有把 X 当作单位。
3. 对 `doubleSeries` 应用上述恒等式，得到 Q·D(X²)=1−X²、Q·E(X²)=3−X²，以及 X²·E(X²)=D(X²)−1。M4 的奇偶计数公式逐系数给出 R=D(X²)+X·D(X²)，V+2D(X²)=E(X²)+X·E(X²)。由此证明

   $$PD=1-X,\quad (1-X)H=1,$$
   $$QV=1+3X+X^2-X^3,\quad QR=1+X-X^2-X^3.$$

4. `ThreeRows/Algebra` 独立证明通分分子和展开分母恒等式。该模块不导入组合计数、固定点或主生成函数，不存在用结论证明通分的循环。
5. `ThreeRows/Main` 从 M5 的真实群作用逐系数得到 4A=D+H+V+R。乘以共同分母，使用四个恒等式和纯环证书得到 4BA=4N，再在有理系数上消去 4，取得 B·A=N。分母常数项检查之后才取逆。
6. `ThreeRows/Recurrence` 从 B·A=N 取任意第 n 个系数，产生 `orbit_coefficient_equation`。n+7 次项的分子系数为零，得到七阶递推；取 0 至 6 次项依次解出七项初值。这些初值不是枚举器返回值，也不是归纳主定理时预先假设的条件。

`orbitLag` 只是记录 n<k 时移位系数为零的有理数辅助函数，不是新轨道模型。所有自然数下标的减法都处在明确的 k≤n 分支；最终含负系数的递推使用整数。

## 模块、出口与范围

| 文件 | 主要出口 |
| --- | --- |
| [Series/Basic.lean](../Domino/Series/Basic.lean) | `countSeries`、`series_second_order`、`series_shift`、奇偶插零系数、`series_ext_parity` |
| [ThreeRows/Algebra.lean](../Domino/ThreeRows/Algebra.lean) | 四个分子/分母定义、`common_numerator_identity`、`orbitDenom_expanded`、常数项与可逆性 |
| [ThreeRows/Series.lean](../Domino/ThreeRows/Series.lean) | 实际系数级数、`ordinary_series_identity`、`fixed_series_identities`、两个移位恒等式 |
| [ThreeRows/Main.lean](../Domino/ThreeRows/Main.lean) | `burnside_series_identity`、`orbit_series_identity`、`orbit_series_rational`、`orbit_series_paper` |
| [ThreeRows/Recurrence.lean](../Domino/ThreeRows/Recurrence.lean) | `orbit_coefficient_equation`、三种数域的递推、`orbit_initial_values`、`orbit_recurrence_first`、汇总定理 |

新增五个数学模块、51 项显式声明，其中 38 个定理、13 个定义。累计 M1–M6 为 32 个数学模块、413 项显式声明，其中 268 个定理。声明数包含辅助定义、实例等，不等于论文定理数。[声明清单](m6-declarations.json)保存阶段、文件和行号。

覆盖 C00 的形式幂级数约定、B08、C03、T02、T03；T04 增加七阶递推起点，仍因基本块 k=1 未验证而保持 partial。L009 的三行 B05—B08 全部完成；L005 的基本块证明、L007/L008 的一般高度及 L010/L011 等扩展不自动升级。

## 验收与复现

固定 Lean `leanprover/lean4:v4.35.0` 与 mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原 M1–M5 的 27 个数学源文件和三个版本配置文件保持不变。最终验收从现有项目执行完整构建、总入口、M1–M5 回归、九个依赖实际提交及源码清洁性检查、覆盖 DAG、全部 413 项声明公理审计。只允许 `propext`、`Classical.choice`、`Quot.sound`，没有占位证明、自设公理或 `native_decide`。

此外在新建 `clean-project` 中复制并逐文件核对源代码，开始时不存在项目 `.lake/build`，重新构建全部项目模块，再执行累计公理审计并与原目录输出精确比较。第三方依赖使用已核对版本及清洁性的缓存；这是**项目源码的独立干净重建**，不声称重新从源代码构建全部 mathlib 或重新安装工具链。

在 lean 目录执行，报告目录必须不存在：

```powershell
python -X utf8 scripts/check_m6.py --report-dir checks/m6-rerun-new
```

脚本保存原目录及干净目录的命令、退出码、日志、源码哈希和逐声明公理依赖；[MainStatement.lean](../Domino/Audit/MainStatement.lean)输出 a、商集基数、级数定义与最终定理类型供语义核对。Windows PowerShell、Python 3.13.0；确定性，无随机种子。开发失败保留在检查目录，未重跑历史 Python 数学枚举。原论文、原证明草稿与历史验收报告不改写；CI 配置仅本地保存，没有推送或远端运行。

## 后续

M6 完成后，半棋盘路线的三行主计数定理取得本地 Lean 证据。按照既定计划下一项为 M7：唯一上下反射固定铺法的全部对称、非恒等固定集交集、四元群精确稳定子分类和各类轨道数。一般奇数高度、五行、渐近及基本块第二证明继续分别安排 M8–M11。

外部人工审阅仍应核对原题与形式化定义、引用和全文表述；不把本阶段结果扩大为文献新颖性或整篇论文已全部形式化的结论。
