# 英文 v2.1 与 M1–M11 的对应

整理日期 2026-10-29；对象为[16 页英文候选稿](../../papers/en/domino-tilings-en.pdf)。论文主张与源码接口由同一 AI 辅助流程核对，**外部数学/语义审阅仍待完成**。

| 论文章节 | 正式覆盖 | 代表出口 |
| --- | --- | --- |
| §1.1、§3 | M1–M6：三行主式、七阶递推、全部初值、半棋盘路线 | Domino.three_row_main_theorem |
| §2 | M11：基本块、全部断口、真实字双射及第二条主式 | Domino.Blocks.three_row_block_main |
| §4.1 | M7：实际稳定子及分类铺法/轨道数 | Domino.three_row_stabilizer_counting |
| §5 | M8：奇数高度计数、矩阵级数、有理性与最终递推 | Domino.General.odd_height_main |
| §6、附录 A | M9：五行压缩、证书、有理式及递推/初值 | Domino.FiveRows.five_row_main_theorem |
| §4.2 | M10：三行渐近、两种概率与指数界 | Domino.Asymptotic.three_row_asymptotic_main |

[12 个实际声明、文件及固定版本行号](formal-coverage.csv)提供更细定位。形式化从实际铺法/轨道基数出发，不以待证递推定义计数。零宽、一行和基本块 k=1 已覆盖。

## 证据层次

- [完整累计验收](verification/lean/report.json)：2026-10-28 启动，10-29 完成，m11_passed；83 模块、1078 声明、699 个 theorem。允许公理仅三项标准公理。
- 同目录包含嵌套回归、定理类型、公理输出和新目录重建记录；固定第三方缓存共享，未从零重编译 mathlib。路径已清理，JSON 的 publication_note 解释处理，历史数值和哈希保留。
- [候选稿打包检查](candidate-package-report.json)、[候选稿公式审核](candidate-manuscript-audit.json)、[16 页版面检查](visual-review.json)。这些是上一准备轮实际检查的公开副本。
- [固定旧提交的 CI 记录](github-ci.json)与[线上对应运行](https://github.com/Lshiqi67/domino-tilings-a232622/actions/runs/40214848402)；当前仓库提交的 CI 状态另看 Actions。
- [旧 M1–M6 语义审阅包](../m1-m6/README.md)维持原来范围。它不是 M7–M11 的外部审阅证明。

## 尚待判断

全部欧氏等距变换分类、最小递推阶、一般高度渐近、偶数高度/正方形推广和文献优先权不在已完成声明中。外部审阅者应按 [REVIEW.md](../../REVIEW.md)检查论文与形式化对象/量词/定义是否对应，并记录自己的实际范围。
