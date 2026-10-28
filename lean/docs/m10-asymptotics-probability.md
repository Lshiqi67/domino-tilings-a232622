# M10：三行渐近与两种均匀抽样概率

> 本文保留所标日期的阶段记录与当时待办；当前 M1–M11 已完成，英文 v2.1 已对应这些结果，见 [当前进度](progress.md)。

> 2026-10-26 发布说明：本阶段代码和公开证据已纳入 M7–M11 发布；下文“本轮”和“下一步”保留 2026-10-25 阶段记录的时间含义。当前完成范围见 [进度表](progress.md)。

日期：2026-10-25。署名：Shiqi Liu。沿用 A002 半棋盘路线。

状态：**M10 已完成本地验收，`m10_passed`，退出码 0。** M1–M9 回归、72 数学模块构建、888 项声明公理审计、干净项目重建及主定理类型比较全部通过。见 [M10 实际报告](../evidence/m10-2026-10-25/verification-01/report.json)。本轮新增 6 模块、95 声明（75 定理、15 定义、2 缩写、3 实例）；累计 577 定理、240 定义、33 缩写、30 实例、7 结构和 1 归纳谓词。

## 对象与范围

本阶段对应既定方案 §8.4、论文三行渐近定理和轨道抽样段落。n 是 `3 × 2n` 棋盘的半宽，n 为任意自然数；极限均为 `n → ∞` 或奇偶子列的 `j → ∞`。砖无标签、允许横竖放置、没有 tatami 限制。四种坐标对称、实际铺法、固定点数与轨道数复用 M1–M7 的定义。空棋盘有一个铺法和一个轨道，抽象四元群的作用可以不忠实。

**本阶段只证明三行渐近。** M8/M9 的一般高度及五行计数不自动带来这些高度的渐近结论；本轮没有提出这样的验证主张。

令 $d_n$ 为普通铺法数，$v_n,r_n$ 为左右反射、半周旋转固定数，$a(n)$ 为实际轨道数。定义

$$\lambda=2+\sqrt3,\qquad \mu=2-\sqrt3=\lambda^{-1},\qquad c_+=\frac{3+\sqrt3}{6},\quad c_-=\frac{3-\sqrt3}{6}.$$

Lean 名称依次为 `Domino.Asymptotic.growth`、`decay`、`leading`、`trailing`，均取实数。另证 $\lambda>1$、$0<\mu<1$、$c_+,c_->0$ 和 $c_++c_-=1$。

## 两个不同的有限样本空间

`HasSymmetry T` 的定义是存在非恒等群元素 g 使 `g • T = T`。`SymmetricTilings n` 是满足该谓词的真实铺法子类型，`symmetricCount n` 是其基数。证明该谓词等价于 M7 中稳定子类型不为平凡类型，并证明

$$s_n+1=v_n+r_n.$$

均匀选一个普通铺法时，事件概率定义为真实子类型基数除以全体铺法基数：

$$p_n=\frac{s_n}{d_n}=\frac{v_n+r_n-1}{d_n}.$$

`SymmetricOrbits n` 是在这个不变子类型上限制群作用后取商。`symmetricOrbitInclusion_injective` 证明它单射到全体真实轨道；`symmetricOrbitInclusion_image` 刻画像恰为存在有非恒等对称代表元的轨道，故不重复计算同一轨道。在该作用上再次使用 Burnside，得到

$$2b_n=v_n+r_n.$$

均匀选一个完整轨道时，事件概率是

$$q_n=\frac{b_n}{a(n)}=\frac{v_n+r_n}{2a(n)}.$$

这两种概率通过有限基数比例定义，不需要额外的连续概率模型。分别证明分母正、两个概率均在 $[0,1]$ 内；n=0 时两者均为 1。`probabilities_two` 给出 $p_2=7/11$、$q_2=4/5$，展示两种样本空间的差别。自然数计数先写无减法恒等式，再转为实数公式，避免截断减法。

## 闭式、渐近与误差界

由既有真实计数二阶递推及 d₀=1、d₁=3，以二步归纳证明

$$d_n=c_+\lambda^n+c_-\lambda^{-n}>0.$$

普通计数闭式不是概率或轨道公式的额外假设。用 $0<\mu<1$ 的幂极限得到 $d_n/\lambda^n\to c_+$，再利用 M4/M5 的奇偶固定点公式证明

$$p_{2j}\sim(\lambda-1)\lambda^{-j},\qquad p_{2j+1}\sim\frac{\lambda+1}{\lambda}\lambda^{-j}.$$

两条 `probability_*_asymptotic_ratio` 定理直接陈述相应比值趋于 1；`probability_*_asymptotic` 另提供 mathlib 的 `IsEquivalent` 表述。通过独立的奇偶合并引理得到完整序列的结论

$$p_n=O(\lambda^{-n/2})\to0.$$

这里 n/2 是实数除法：`halfGrowth n = Real.rpow growth ((n : ℝ) / 2)`，`halfDecay` 为其倒数。`halfDecay_rpow` 证明其等于 $\lambda^{-n/2}$。偶数和奇数下标的实数幂换算另有证明，没有使用自然数整除代替半指数。

由真实 Burnside 计数和 $s_n+1=v_n+r_n$ 得

$$\frac{a(n)}{d_n}=\frac{1+p_n+2/d_n}{4}\to\frac14,$$

进而证明

$$a(n)=\frac{d_n}{4}+O(\lambda^{n/2})\sim\frac{3+\sqrt3}{24}\lambda^n.$$

误差项定义为 `orbitError n = (a n : ℝ) - d n / 4`。`orbit_exponential_error_bound` 给出可直接阅读的量词：存在 C>0 和 N，使所有 n≥N 都有 $|a(n)-d_n/4|\le C\lambda^{n/2}$。`probability_exponential_bound` 同样给出完整序列概率的指数上界。这里证明界的存在，不宣称已经给出最优或数值指定的 C、N。

最后利用

$$q_n=\frac{p_n+1/d_n}{2(a(n)/d_n)}$$

证明均匀轨道抽样的对称概率也趋于 0。没有将其与普通铺法概率混用。

## 文件与主要出口

所有新增数学文件位于 `Domino/Asymptotics/`，命名空间为 `Domino.Asymptotic`。

| 模块 | 作用及关键出口 |
| --- | --- |
| [ClosedForm](../Domino/Asymptotics/ClosedForm.lean) | 代数根、真实 d 的闭式和主增长项极限 |
| [Sampling](../Domino/Asymptotics/Sampling.lean) | 真实有限样本空间、轨道单射/像、基数公式、概率和正性 |
| [ParityLimits](../Domino/Asymptotics/ParityLimits.lean) | 奇偶合并、两个概率首项常数及比值趋于 1 |
| [OrbitLimits](../Domino/Asymptotics/OrbitLimits.lean) | a/d→1/4、轨道主项和均匀轨道概率趋零 |
| [ErrorBounds](../Domino/Asymptotics/ErrorBounds.lean) | 实数半指数及两项完整序列 Big-O 界 |
| [Main](../Domino/Asymptotics/Main.lean) | 可读量词、`IsEquivalent`、边界样例及 `three_row_asymptotic_main` |

累计声明清单为 [m10-declarations.json](m10-declarations.json)，定义和主定理类型输出入口为 [M10Statement.lean](../Domino/Audit/M10Statement.lean)。声明数量包括辅助工具，不能解读为论文定理数量。

## 实际验收与复现

Lean 4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 以及九个依赖仍按原锁定版本。M1–M9 的 66 个数学源文件和三份版本配置通过旧报告哈希核对后，执行累计回归；不改变前面阶段的数学源码。

在项目 `lean` 目录运行：

```powershell
lake --wfail build
python -X utf8 scripts/check_m10.py --report-dir ("checks/m10-rerun-" + (Get-Date -Format "yyyyMMdd-HHmmss"))
```

完整验收成功标记为 `m10_passed`、进程退出码 0。脚本递归回归 M1–M9，重新构建整个项目，逐项核对累计声明的传递公理依赖，并检查主定理类型。允许公理仍仅为 `propext`、`Classical.choice`、`Quot.sound`，不用占位证明、自设数学公理或 `native_decide`。

本次干净重建目录为报告目录下的 `m9-regression/m7-m8-regression/m6-regression/clean-project/`。项目自身编译产物从空目录重新生成；只共享已核对的固定第三方缓存，未全量重编译 mathlib。要求源码哈希、公理输出和主定理类型输出一致。确定性过程，无随机种子，也没有重跑历史 Python 枚举。

完整命令、退出码、范围和失败过程保存在 [本轮检查记录](../evidence/m10-2026-10-25/README.md)。M9 历史报告的整理副本进入 `evidence/m9-2026-10-25/`，用于独立复现时核对旧源码，保留原哈希，不改写原始 checks 记录。本轮仅保存本地，未上传或运行远端 CI。

## 下一步

下一阶段是 **M11 基本块第二证明**：先完成首次回空路径的基本块分类与唯一分解，再证明块字上的对称作用和回文计数，覆盖 T04 的 k=1 条目。不能用已有主公式反推基本块分类。

一般高度/五行渐近、最小递推阶、欧氏全部等距分类、外部人工语义审阅和文献首次性核查仍不在 M10 的完成范围内。
