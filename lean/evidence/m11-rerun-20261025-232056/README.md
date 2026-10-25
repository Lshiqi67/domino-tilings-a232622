# M1–M11 用户本地复跑证据

来源：用户提供的 PowerShell 成功输出，以及本地同一运行目录中的实际报告。报告记录开始时间为 2026-10-25 23:21（北京时间）；2026-10-26 核对并整理公开。状态 **m11_passed**，全部顶层命令退出码为 0。

- [累计报告](report.json)：83 数学模块、1078 项显式声明及所有检查状态。
- [公理输出](axioms.txt)、[主定理类型](main-statements.txt)。
- [干净重建后的公理输出](clean-axioms.txt)、[主定理类型](clean-main-statements.txt)。
- [M10 回归](m10-regression/report.json)，其子目录递归保留 M9、M7/M8、M6 及更早回归。
- [项目干净构建日志](m10-regression/m9-regression/m7-m8-regression/m6-regression/clean-lake-build.txt)。

2026-10-26 发布前逐一比较报告中 113 个输入文件（Lean 源码、审计入口、清单、版本配置和验收脚本）的 SHA-256，全部与当前本地文件一致。此处是历史复跑证据的整理，不冒称发布当日又做了一次完整验收。

仅替换本机路径为占位符；JSON 添加 publication_note。日期、命令结构、结果、退出码、声明公理映射和源码哈希保留。占位路径不是可直接执行的命令。原始报告与编译副本留在本地，公开副本不含 clean-project、依赖缓存或编译产物。固定第三方缓存共享，不是无缓存重编译 mathlib。

复现命令见 [Lean 项目说明](../../README.md)。论文语义的外部人工审阅、一般高度渐近、最小阶、全部欧氏等距分类和文献优先权仍未认证。
