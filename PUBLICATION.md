# Public edition / 公开版说明

This is a curated research snapshot, not the complete private workspace.

Included: Chinese and English manuscripts, selected research notes, both proposed proof routes, illustrated block-proof guides, six historical computational programs, and now the complete Lean M1–M6 project with pinned dependencies, scripts, stage documentation and sanitized evidence.

Excluded: institutional information, complete private archives, conversation dumps, unredacted machine logs, local absolute paths, credentials, build caches and unrelated projects. Git commits use the author and committer identity explicitly provided by the repository owner.

The Chinese manuscript PDF and all its TeX files are byte-identical to the retained source edition. The English public edition updates its abstract, status statements and reproduction notes to describe unfinished research, the then-pending Lean verification and the curated public materials. Mathematical formulas are retained for review; retaining a formula is not certifying it.

Historical JSON reports have invocation, working-directory and platform fields removed. Their numerical fields are unchanged. Their source hashes identify the unchanged historical programs, not the modified JSON bytes. Each sanitized report is labelled explicitly. They are not represented as newly run experiments.

[PUBLICATION.json](PUBLICATION.json) records source-relative provenance, hashes and editorial treatments. It contains no absolute workstation path. The six historical computational programs remain unchanged; commands should be run in a temporary working copy because some historical programs write metadata and reports.

[MANIFEST-SHA256.json](MANIFEST-SHA256.json) records the SHA-256 digest of every published file except the manifest itself, for checking this snapshot's integrity.

本公开版只包含适合复核的研究材料。中文论文 PDF 与 TeX 源码保持原样；英文论文增加未完成状态说明。数值报告去除本机调用信息和路径后公开，数学数据未改写。原始私人工作区中的所有版本仍在本地保留，筛选公开材料不等于删除历史记录。

No licence has been selected for this snapshot. Repository write permissions and the ability to read or fork a public repository are separate matters. The repository has no intended collaborator write access.

See [STATUS.md](STATUS.md) for the current scientific claims and limitations.

## Lean 发布补充（2026-10-25）

32 个数学模块、审计入口、版本锁、验收脚本、完整阶段方案和证明链公开副本一起发布。源码按主题分组，进展按 M1–M6 登记；下一步 M7–M11 见 [计划](lean/docs/progress.md)。Lean 数学源文件与版本锁保持原样，脚本仅调整历史报告路径，文档更新公开导航和现状。

`lean/evidence/` 来自实际历史运行，只隐去本机绝对路径，保留结果、退出码、日期、公理映射与原始源码哈希。文本日志的处理规则统一见其 README，JSON 另有 publication_note。历史哈希不因文档改版重写。`lean/checks/` 的原始完整记录及用户复跑结果继续留在本地；`.lake/`、clean-project 编译副本不提交。当前发布文件的 SHA-256 在根目录清单中重新登记。

旧论文及阶段记录中的“未形式化”描述各自形成时的状态。当前仅三行主计数按明确语义完成形式化；全文扩展、基本块第二证明、欧氏等距分类、外部人工审阅及新颖性仍需分别处理。
