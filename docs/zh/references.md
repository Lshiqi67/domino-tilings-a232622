> **公开研究草稿，工作尚未完成。本文档中的推导及结论仍待复核，不宣称已经解决猜想。论文还需打磨，证明准确性还需 Lean 形式化验证；尚未完成 Lean 验证。详见 [当前状态](../../STATUS.md)。**

# 文献与已知结果

## 2026-10-25 · 独立审查新增的直接相关前作

REF009：Daryl DeFord, *Enumerating Distinct Chessboard Tilings*, Fibonacci Quarterly 52(5), 102–116，[期刊全文](https://www.fq.math.ca/Papers1/52-5/DeFord.pdf)。本轮实际读取定理 6.1 与第 6.2.1 节；前者讨论固定高度对称轨道序列的常系数递推，后者给两行多米诺实例。[官方卷目录](https://www.fq.math.ca/52-5.html) 标注 December 2014；所读期刊 PDF 首页日期 2015-04-20，作者网站版本日期 2014-11-29。不得把搜索抓取日期当发表日。

这一前作应补入论文第 1、5 节：轨道有理性/递推存在性本身不是新颖性依据；本地显式边界矩阵、三行证明、五行有理式及细化结果的具体首次性仍未核实。本轮未在该文所读范围中取得三行或五行目标显式公式的相同证明，不能据此宣布原猜想已早获证明。详细范围、检索边界及修订建议见 [本轮审查 E03](../../research/README.md)。

以下旧核查条目保留作为历史，不把本轮新发现回写成此前已经找到的文献。

## 已保存来源

以下来源继承自 T002 的 2026-10-24、2026-10-25 核查；本轮又读取 REF001—REF003。核查日期均按北京时间；“已读”仅指相应条目列出的范围，不代表阅读全文。

| 编号 | 来源 | 可用内容与核查范围 | 日期 |
| --- | --- | --- | --- |
| REF001 | [OEIS A232622](https://oeis.org/A232622) | 原题、生成函数、七阶递推与初值；页面仍有猜想标签 | 2026-10-25 |
| REF002 | R. J. Mathar, *Paving rectangular regions with rectangular tiles: tatami and non-tatami tilings*, [arXiv:1311.6135](https://arxiv.org/pdf/1311.6135), 2013 | 定义、表 10、Conjecture 6、式 (26)；按列数计次 | 2026-10-25 |
| REF003 | R. J. Mathar, *Tilings of rectangular regions by rectangular tiles: Counts derived from transfer matrices*, [arXiv:1406.7788](https://arxiv.org/pdf/1406.7788), 2014 提交 | 第 2.1—2.3 节式 (4)—(6)，普通铺法、不可竖切块与转移矩阵；该处按砖数计次 | 2026-10-25 |
| REF004 | R. P. Stanley, *Topics in Algebraic Combinatorics*, [作者讲义 PDF](https://math.mit.edu/~rstan/algcomb/algcomb.pdf), 2013-02-01 版本 | 第 7 章 Lemma 7.2，Burnside 引理及证明；前一轮已读，本轮未重复全文请求 | 2026-10-25 |
| REF005 | D. Klarner and J. Pollack, *Domino tilings of rectangles with fixed width*, Discrete Mathematics 32 (1980), 45–52, [出版链接](https://doi.org/10.1016/0012-365X(80)90098-9) | 仅核查出版方索引摘要：固定宽度普通铺法满足常系数线性递推、生成函数有理；全文请求 403，未核对定理编号 | 2026-10-25 |
| REF006 | [OEIS A001835](https://oeis.org/A001835) | 普通三行铺法序列及相关文献；本题 $d_n=\mathrm{A001835}(n+1)$，不可直接沿用条目的起始下标 | 2026-10-25 |
| REF007 | M. Hujter and A. Kaszanyitzky, *Symmetries related to domino tilings on a chessboard*, [arXiv:1603.03298](https://arxiv.org/pdf/1603.03298), 2016 | 所读内容涉及 Hamilton 路与六行普通铺法递推，未取得本题轨道公式的证明 | 2026-10-25 |
| REF008 | [AlgebraicCombinatorics.Details.DominoTilings 文档](https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics/Details/DominoTilings.html) | 读到三行基本块与上下反射定义；未编译、未审计依赖，不能视为已验证的本题形式化证明 | 2026-10-25 |

## 变量换元与可引用部件

REF002 式 (26) 以列数计次，原式为

$$\overline T(z,3)=\frac18\left(\frac1{1+z}+\frac1{1-z}\right)+\frac{1+2z^2-z^6}{2(1-4z^4+z^8)}+\frac{1-z^2}{4(1-4z^2+z^4)}.$$

本题应比较 $\overline T(z,3)=A(z^2)$。A001 的符号检查已经核对这个等式，不能把 $z$ 直接当成半长度变量 $x$。

REF003 的对应三行公式以砖数计次。$3\times2n$ 棋盘恰用 $3n$ 块砖，因此将其中的 $z^3$ 换成 $x$，得到

$$D(x)=\frac{1-x}{1-4x+x^2},\qquad F(x)=3x+\frac{2x^2}{1-x},\qquad D=\frac1{1-F}.$$

REF003 明确保留反射、旋转得到的有方向铺法，因此只提供原题的部件。A001 现在从局部规则重新推导了这些式子，再补全对称计数；证明不依赖将目标猜想或有限数值当作前提。

## 新颖性与开放状态

REF001 仍有猜想标签是已读页面的事实，但不是“所有文献均未解决”的证明。已有检索包括 `A232622 proof`、Mathar 与 Conjecture 6 的组合、三行铺法与 Burnside/反射的组合。未进行全面引文追踪，不能声明本轮为首次证明。

本轮发现并写出的论证按本地研究草稿记录，没有向 OEIS、作者或其他人发送消息，也未发表。若后续查到既有证明，应将成果定位调整为复现、整理或补充证明，并补上来源。

## 下一项文献工作

检索三行棋盘的 reflection/rotation classes、fault-free domino tilings、palindromic compositions；从 REF002、REF003 的引用与后续引用继续追踪。核对原始提交版本和后续版本的对应公式，避免仅依靠 OEIS 标签判断状态。

## 2026-10-25 后续深化轮：五行对照与局限

本轮重新读取 REF002 的 [表 12](https://arxiv.org/pdf/1311.6135)（PDF 第 10 页）：五行棋盘列数 $2,4,6,8,10$ 的无全等轨道数分别为 $5,33,329,3818,46878$。A002 从半棋盘矩阵独立计算的对应项一致；表格用于事后对照，没有参与求递推或拟合函数。

同轮检索 `domino incongruent 5 Mathar proof`、`domino tilings reflection Burnside rectangle generating function` 和五行棋盘相关组合，未获得可直接核对的现成完整证明。该检索远非穷尽，不证明 A002 的一般奇数行公式或五行有理式在文献中不存在。

后续重点是查阅对称铺法、有限宽度矩形匹配和反射商图的引文网络；在核查前，R001、R002 均只主张本地已得到相应论证与证据，不主张首次发现。

## 2026-10-25 · 公开解决状态专项复查

用户询问本地“三行矩形铺砖在旋转、反射下的计数猜想”是否已被公开解决。本轮重新核对的对象为 A232622：所有无标号多米诺铺法按矩形的旋转、反射取商，不附加 tatami 条件。

- 实际重新读取 [OEIS A232622](https://oeis.org/A232622)：生成函数仍标 `Conjecture`，七阶递推仍标 Alcover 于 2019-01-21 猜测，页面未列出该公式的证明链接。网站页脚的全站修改日期不能当作本条目的修改日期。
- 实际重新读取 [Mathar 2013 论文](https://arxiv.org/pdf/1311.6135) PDF 第 9 页：目标仍列为 Conjecture 6、式 (26)；邻近的 Theorem 10、式 (25) 是带下标 0 的 tatami 子类，不能混称为本题总计数的证明。
- 重新打开 [Mathar 2014 论文](https://arxiv.org/pdf/1406.7788) 及 [DominoTilings 形式化文档](https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics/Details/DominoTilings.html)。后者可见三行基本块与反射相关定义、定理，但本轮未取得目标轨道生成函数的形式化定理，也未编译或审计依赖。
- 实际检索包括 `"A232622" proof`、`"Mathar" "Conjecture 6" tilings`、`"1311.6135" proof`，以及 domino tilings 与 three / 3 × 2n / incongruent / inequivalent / Burnside / reflection 的组合。本轮未找到可核对的公开完整证明。检索命中 *Intersecting Domino Tilings*，其出版方摘要讨论铺法两两相交的极值问题，不能据其中的“solve”判定本题已解决；见 [出版方摘要](https://www.tandfonline.com/doi/abs/10.1080/00150517.2010.12428111)。

**结论：截至本次核查，未找到已公开解决的可靠证据；仍不能确认它在全部公开文献中尚未解决。** OEIS 的猜想标签和检索未命中不足以证明开放性。本地 A001、A002 的存在也不能确定首次证明或公开发表状态。本轮没有重跑实验、重新审定两份证明或对外发布。

下一项可执行工作：继续追踪原论文的后续引用，重点寻找一般矩形的对称轨道公式，并逐式核对其三行特例是否已蕴含目标；在此之前继续保留“外部开放状态及新颖性未核实”的标注。

## 2026-10-25 · 论文整理时的来源复核

本轮重新读取 OEIS A232622 的公式与署名栏、Mathar 2013 的 Conjecture 6 / 式 (26) 和表 12、Mathar 2014 原文及书目信息，以及 Stanley 讲义第 7 章 Lemma 7.2。论文仅收录实际使用的四项参考文献，明确三行列数变量 z²=x 和砖数变量 z³=x 的区别。OEIS 猜想标签仍在，但文献优先权及全球开放状态仍未核实；不把此轮排版或再次读取来源称为原创性证明。
