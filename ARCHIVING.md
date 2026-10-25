# 版本归档与恢复

作者：**Shiqi Liu**。更新：2026-10-26。

## 已固定的公开版本

[英文论文 v2.0 Release](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.0)固定论文及配套公开材料。文稿日期为 2026-10-25，Release 日期为 2026-10-26；两者不混用。具体内容和核验边界见 [版本说明](releases/paper-en-v2.0.md)。

原始根提交 `990f903f57fc0ddb68496c3ee47da1f13aaf06c6` 及此后的公开历史保留。它们可用于比较每个版本已包含的具体内容；Git 提交日期、仓库创建日期不等同于平台独立认证的首次公开时刻。没有改写旧提交来更改姓名或日期。

## 备份范围

| 备份 | 范围与位置 |
| --- | --- |
| Release 源码 ZIP | 本标签固定的全部公开文件，包括旧版论文、TeX、两条路线的公开推导、计算程序及公开 Lean 检查记录 |
| Release Git bundle | 截至标签的完整可达公开 Git 历史；包括作者、提交者信息和历史文件版本 |
| 本地完整研究备份 | P002 题目资料、初始筛选、公开仓库工作文件、原始研究和失败日志、原始 Lean 检查报告及旧版材料；另存于仓库之外，不包含无关题目 |

完整研究备份排除可再生的 `.lake` 依赖/编译缓存和 Python 缓存；依赖版本锁与重建说明已保留。Git 历史通过 bundle 单独保存。公开快照只使用原已筛选的资料；原始机器日志和私人归档保存在本地。

本地备份使用独立目录并逐文件核对 ZIP 中的 SHA-256，但仍与工作区位于同一磁盘，不是异地灾备。可把完整备份目录再复制至移动硬盘或其他受控存储。当前这轮的独立远程副本是 GitHub 上的公开历史与 Release 附件，未声称已上传完整私密研究包。

## 恢复与核对

下载 Release 附件及 `SHA256SUMS.txt`。在 PowerShell 中执行：

```powershell
Get-FileHash -Algorithm SHA256 .\domino-tilings-en-v2.0.pdf
Get-FileHash -Algorithm SHA256 .\domino-tilings-paper-en-v2.0-source.zip
Get-FileHash -Algorithm SHA256 .\domino-tilings-paper-en-v2.0-history.bundle
git clone -c core.longpaths=true .\domino-tilings-paper-en-v2.0-history.bundle restored-repository
git -C restored-repository checkout --detach paper-en-v2.0
git -C restored-repository fsck --full
```

将三个输出摘要与 `SHA256SUMS.txt` 比较。Windows 上部分历史 Lean 日志路径较长，克隆时的 `core.longpaths=true` 仅设置新克隆仓库；解压 ZIP 也请选短目标路径或支持长路径的解压工具。`release-manifest.json` 给出实际发布提交及核验范围；仓库根目录 `MANIFEST-SHA256.json` 覆盖公开快照中除清单自身外的每个文件。ZIP 不包含 Git 历史；需要历史时使用 bundle。编译环境按 [Lean 运行说明](lean/README.md)重建。

哈希用于判断内容一致性，不独立证明作者、完成时间、数学正确性或文献首次性。今后修订使用新提交和新版本，旧版及其范围继续保留。
