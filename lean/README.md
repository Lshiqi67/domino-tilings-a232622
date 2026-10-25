# 半棋盘路线 Lean 形式化项目

署名：**Shiqi Liu**。日期：2026-10-25。

**M1–M6 已完成本地验证：真实三行铺法轨道的主生成函数、全部自然数指标的七阶递推及七项初值已证明。** 共有 32 个数学模块、413 项显式声明，其中 268 个定理。完整构建、累计公理审计和独立项目源码重建均通过。全文扩展、第二条证明和外部人工审阅仍待完成。

## 阅读顺序

1. [成果及后续阶段](docs/progress.md)：已完成内容、范围和 M7–M11 顺序。
2. [M6 主定理](docs/m6-main-theorem.md)：精确对象、生成函数、递推、初值及主要出口。
3. [完整形式化方案](docs/formalization-plan.md)与[覆盖表](docs/coverage.json)：原证明链到 Lean 的对应关系。
4. [公开验证证据](evidence/README.md)与[累计声明清单](docs/m6-declarations.json)。
5. [原书面证明链的公开副本](docs/proof-chain/proof-chain.md)及[半棋盘草稿](../docs/zh/half-board-proof.md)。历史材料中的状态不代替当前覆盖表。

## 固定环境

| 项目 | 固定值 |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0` |
| mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| 依赖锁 | [lake-manifest.json](lake-manifest.json)，九个 Git 依赖锁定完整提交 |
| 配置 | [lakefile.toml](lakefile.toml)，关闭自动隐式参数 |
| 构建入口 | [Domino.lean](Domino.lean) |

需要 Git、通过 elan 管理的 Lean/Lake，以及 Python 3。验收脚本只使用标准库，原本地运行使用 Python 3.13.0。不要为了复现随意执行 `lake update` 或改动版本锁。

## 获取与运行

```powershell
git clone https://github.com/Lshiqi67/domino-tilings-a232622.git
cd domino-tilings-a232622/lean
lake exe cache get
lake --wfail build
python -X utf8 scripts/check_m6.py --report-dir checks/m6-first-run
```

Linux/macOS 可将最后一行的 `python` 换成 `python3`。首次获取工具链、依赖和缓存需要网络；缓存下载只是准备，构建与审计才是这里记录的核验。

报告目录必须尚不存在。在 PowerShell 中重复验收可使用：

```powershell
python -X utf8 scripts/check_m6.py --report-dir ("checks/m6-rerun-" + (Get-Date -Format "yyyyMMdd-HHmmss"))
```

成功时最后输出 `m6_passed`，且进程退出码为 0。报告保存在该目录的 `report.json`；只出现 `运行 ...` 表示该步骤正在执行。`Domino.Environment` 的 `info:` 是接口检查信息，不是错误。`3218 jobs` 包括依赖构建任务，不是 3218 个论文定理。

在 VS Code 中用 Lean 4 扩展打开本 `lean` 目录，在内置终端执行上述构建及验收命令；打开 [ThreeRows/Recurrence.lean](Domino/ThreeRows/Recurrence.lean) 可查看汇总出口 `three_row_main_theorem`。单个文件无报错不等于完成全项目验收。

## 验收范围

`check_m6.py` 递归运行 M4/M5、M3、M2、M1 和环境检查，核对九个依赖的实际提交及已跟踪文件清洁性，构建所有项目模块，并逐项审计 413 项声明。允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`；源码筛查及审计拒绝占位证明、自设数学公理和 `native_decide`。

脚本使用 `evidence/` 中公开历史报告核对旧阶段的数学源文件及版本锁未变。随后将项目源码复制到新的 `clean-project/`，通过 Lake 的 `--packages` 参数共享已核对的第三方依赖缓存，重新构建项目并要求两次累计公理输出完全相同。此项不是从零重编译全部 mathlib。

历史报告去除了本机路径，数学结果、原始源码哈希与公理映射保留。发布时文档和脚本路径发生变化，原报告仍对应当时快照；当前文件哈希见 [发布清单](../MANIFEST-SHA256.json)。新运行写入被 Git 忽略的 `checks/`，不会覆盖公开历史证据。

## 目录分工

| 目录 | 内容 |
| --- | --- |
| `Domino/Board/` | 格子、无序砖、精确覆盖和部分铺法 |
| `Domino/Symmetry/` | 坐标作用、商集、路径作用、Burnside |
| `Domino/Transfer/` | 三行列规则、几何与路径等价、转移计数 |
| `Domino/HalfBoard/` | 补全与限制、实际砖对应、三类固定点 |
| `Domino/ThreeRows/`、`Domino/Series/` | 递推、固定点公式、幂级数与主定理 |
| `Domino/Audit/` | 阶段公理审计及主定理类型检查 |
| `docs/` | 方案、覆盖表、声明清单及阶段说明 |
| `evidence/` | 去除本机路径的历史成功及失败记录 |
| `scripts/` | 可重复执行的验收程序 |
| `checks/`、`.lake/` | 本机新报告、依赖和编译缓存；不提交 |

[GitHub Actions 工作流](../.github/workflows/lean.yml)随代码提供，运行同一 M6 验收。远端是否通过，请查看 [Actions 对应提交](https://github.com/Lshiqi67/domino-tilings-a232622/actions/workflows/lean.yml)；本地通过与远端通过分别记录。

下一项是 **M7 精确稳定子和轨道类型计数**。欧氏全部等距分类、全文推广及文献优先权未在 M1–M6 中获得认证。
