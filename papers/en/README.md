# 英文论文 v2.1 · arXiv 投稿候选稿

Shiqi Liu · Dalian University of Technology。稿件日期 2026-10-28，公开仓库更新 2026-10-29，16 页。

[PDF](domino-tilings-en.pdf) · [LaTeX](main.tex) · [论文—形式化对应](../../review/arxiv-v2.1/README.md) · [投稿文件说明](../../submission/README.md)

本版与已核验的 arXiv 候选稿逐字节一致。摘要、第 7 节及复现附录报告 M1–M11：两条三行证明、精确稳定子、奇数高度计数与有理性、五行证书和十四阶递推、三行渐近。列出实际声明、固定源码版本和复现命令；机构显示在 AMS 稿件文末。

外部数学/语义审阅及文献优先权仍待完成；没有把全部欧氏等距分类、最小阶、一般高度渐近或偶数高度/正方形推广列为已证。尚未向 arXiv 提交或取得文章号。

## 构建

本目录运行 `./build.ps1`，需要 Python、SymPy 和 pdfLaTeX。构建先执行精确转录核查，再编译两遍；本地成功不能替代 arXiv 服务器编译。复现会更新本地审核报告和 PDF，原发布字节可从固定标签恢复。

## 历史版本

- [v2.0：15 页，M1–M6 说明](archive/v2.0/README.md)，[冻结摘要](archive/v2.0/SHA256.json)；旧相对链接按原字节保留，历史上下文以旧 Release 为准。
- [v1.0](archive/v1.0/README.md) 继续保留。
- `checks/readability-revision.md` 是 2026-10-25 的历史 E04 记录，新检查见 [v2.1 记录](../../review/arxiv-v2.1/README.md)。
