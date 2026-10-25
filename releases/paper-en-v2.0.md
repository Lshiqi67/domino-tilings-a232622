# 英文论文 v2.0 归档发布

署名：**Shiqi Liu**。GitHub 账号：**Lshiqi67**。

- 论文题名：*Domino tilings of odd-height rectangles up to symmetry*。
- 论文版本：2.0；文稿日期：2026-10-25；正文：15 页。
- 本次 Release 日期：2026-10-26（北京时间）；标签：`paper-en-v2.0`。
- 归档前仓库基线：`e35709bb336d237cda2a0b631ec185d61cacdabd`。英文稿在该基线中已经存在；本次未修改 PDF 或 TeX。
- PDF SHA-256：`c6af448ddd085f1df8abf04ac2b0fa78c19b07f012a9c42299f01cf5ad4c77dc`。

本标签固定英文论文 v2.0 及配套公开研究快照；仓库中的中文稿仍为 v2.1。不同对象的版本号分别使用。今日建立 Release 不追溯改变此前 GitHub 公开时间，不主张文献首次性或优先权已获认证。

## 论文内容及验证范围

本稿给出三行棋盘按矩形对称取商的两条生成函数推导、七阶递推及初值，讨论稳定子类型和渐近，并给出奇数高度转移表达与五行显式证书。

**论文 v2.0 报告的形式化范围固定为 Lean M1–M6**：真实三行铺法轨道的主生成函数、递推和初值及其所述依赖。仓库配套快照已含后续 M7–M11 源码、固定依赖版本和历史验收证据；这不把 PDF 的覆盖说明自动扩大至 M11。具体内容见 [研究状态](../STATUS.md)与 [M1–M6 审阅包](../review/m1-m6/README.md)。

独立外部数学和语义审阅、文献优先权核查仍待完成。AI 使用披露保留在论文中。此次归档只进行文件完整性、引用格式和恢复检查，没有重新运行 Lean 或铺法枚举，不将复制历史报告表述为新验证。

## 附件与引用

[Release 页面](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.0)提供：

- `domino-tilings-en-v2.0.pdf`：原字节英文论文。
- `domino-tilings-paper-en-v2.0-source.zip`：标签所固定的全部公开文件，含旧版 PDF/TeX、研究文档、程序、Lean 源码及公开历史核验记录。
- `domino-tilings-paper-en-v2.0-history.bundle`：截至本标签的完整可达公开 Git 历史，供恢复仓库；后续提交不属于此附件。
- `SHA256SUMS.txt`：以上三个附件的 SHA-256。
- `release-manifest.json`：实际发布提交、论文基线、附件摘要和核验范围。

推荐引用：Shiqi Liu. *Domino tilings of odd-height rectangles up to symmetry*. Version 2.0, preprint, 2026. 具体信息见 [CITATION.cff](../CITATION.cff)和 [BibTeX](../CITATION.bib)。没有 DOI 或 ORCID 时不填造占位值。

本次没有选择或变更许可。引用说明不等于许可授权。公开资料与本地完整研究备份的区别、恢复方法见 [归档说明](../ARCHIVING.md)。
