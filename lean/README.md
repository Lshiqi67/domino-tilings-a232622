# 多米诺铺法 Lean 形式化项目

署名：**Shiqi Liu**。更新日期：2026-10-26。

**M1–M11 已完成本地验证。** 新增基本块分类、全部断口唯一分解、真实字对称、回文中心及第二条主生成函数证明。累计 83 数学模块、1078 声明（699 定理）；旧阶段回归、累计公理审计和干净重建通过。M7–M11 随本次增量发布提供；一般高度渐近、最小阶及外部审阅仍待办。

## 阅读顺序

1. [成果及后续阶段](docs/progress.md)：已完成内容、精确范围和后续工作。
2. [M11 基本块第二证明](docs/m11-block-route.md)、[M10 渐近与概率](docs/m10-asymptotics-probability.md)、[M9 五行主定理](docs/m9-five-row-certificate.md)、[M7/M8 扩展](docs/m7-m8-stabilizers-odd-height.md)与[M6 主定理](docs/m6-main-theorem.md)：精确对象、生成函数、递推、初值及主要出口。
3. [完整形式化方案](docs/formalization-plan.md)与[覆盖表](docs/coverage.json)：原证明链到 Lean 的对应关系。
4. [用户最新复跑报告](evidence/m11-rerun-20261025-232056/report.json)、[历史验证证据](evidence/README.md)与[累计声明清单](docs/m11-declarations.json)。
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

首次获取项目（已有本地项目可直接进入其 `lean` 目录）：

```powershell
git clone https://github.com/Lshiqi67/domino-tilings-a232622.git
cd domino-tilings-a232622/lean
lake exe cache get
lake --wfail build
python -X utf8 scripts/check_m11.py --report-dir checks/m11-first-run
```

GitHub 源码现包含 M1–M11。Linux/macOS 使用对应项目路径，并可将 `python` 换成 `python3`。首次获取固定工具链、依赖和 mathlib 缓存需要网络；缓存下载只是准备，构建与审计才是这里记录的核验。

报告目录必须尚不存在。在 PowerShell 中重复验收可使用：

```powershell
python -X utf8 scripts/check_m11.py --report-dir ("checks/m11-rerun-" + (Get-Date -Format "yyyyMMdd-HHmmss"))
```

M11 成功时最后输出 `m11_passed`，且进程退出码为 0。报告保存在该目录的 `report.json`；只出现 `运行 ...` 表示该步骤正在执行。`Domino.Environment` 的 `info:` 是接口检查信息，不是错误。构建显示的 jobs 包括依赖任务，不是论文定理数量。

在 VS Code 中用 Lean 4 扩展打开本 `lean` 目录，在内置终端执行上述构建及验收命令；打开 [ThreeRows/Recurrence.lean](Domino/ThreeRows/Recurrence.lean) 可查看汇总出口 `three_row_main_theorem`。M7/M8 可打开 [Stabilizers/Examples](Domino/Stabilizers/Examples.lean) 与 [OddHeight/Boundary](Domino/OddHeight/Boundary.lean)。M9 可打开 [FiveRows/Recurrence.lean](Domino/FiveRows/Recurrence.lean) 查看 `five_row_main_theorem`。M10 入口为 [Asymptotics/Main.lean](Domino/Asymptotics/Main.lean)，总出口 `three_row_asymptotic_main`。M11 入口为 [Blocks/Main.lean](Domino/Blocks/Main.lean)，主出口 `orbit_series_via_blocks`。单个文件无报错不等于完成全项目验收。

## 验收范围

`check_m11.py` 递归运行 M10、M9、M7/M8、M6、M4/M5、M3、M2、M1 和环境检查，核对九个依赖的实际提交及已跟踪文件清洁性，构建所有项目模块，并逐项审计 1078 项声明。允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`；源码筛查及审计拒绝占位证明、自设数学公理和 `native_decide`。

脚本使用 `evidence/` 中整理后的历史报告核对旧阶段的数学源文件及版本锁未变。随后将项目源码复制到新的 `clean-project/`，通过 Lake 的 `--packages` 参数共享已核对的第三方依赖缓存，重新构建项目并要求两次累计公理输出完全相同。此项不是从零重编译全部 mathlib。

历史报告去除了本机路径，数学结果、原始源码哈希与公理映射保留。发布时文档和脚本路径发生变化，原报告仍对应当时快照；本次提交的文件哈希见[发布清单](../MANIFEST-SHA256.json)，历史运行对应的数学源码哈希见 [M11 报告](evidence/m11-2026-10-25/verification-01/report.json)。新运行写入被 Git 忽略的 `checks/`，不会覆盖公开历史证据。

## 目录分工

| 目录 | 内容 |
| --- | --- |
| `Domino/Board/` | 格子、无序砖、精确覆盖和部分铺法 |
| `Domino/Symmetry/` | 坐标作用、商集、路径作用、Burnside |
| `Domino/Transfer/` | 三行列规则、几何与路径等价、转移计数 |
| `Domino/HalfBoard/` | 补全与限制、实际砖对应、三类固定点 |
| `Domino/ThreeRows/`、`Domino/Series/` | 递推、固定点公式、幂级数与主定理 |
| `Domino/Stabilizers/` | 三行精确稳定子与分类轨道 |
| `Domino/OddHeight/` | 一般高度双射及奇数高度计数、有理性 |
| `Domino/FiveRows/` | 五行压缩、显式证书、主式和十四阶递推 |
| `Domino/Asymptotics/` | 三行闭式、真实概率样本空间、渐近和指数误差界 |
| `Domino/Blocks/` | 基本块分类、真实保权字双射、字对称、回文中心与第二条主式证明 |
| `Domino/Audit/` | 阶段公理审计及主定理类型检查 |
| `docs/` | 方案、覆盖表、声明清单及阶段说明 |
| `evidence/` | 去除本机路径的历史成功及失败记录 |
| `scripts/` | 可重复执行的验收程序 |
| `checks/`、`.lake/` | 本机新报告、依赖和编译缓存；不提交 |

[GitHub Actions 工作流](../.github/workflows/lean.yml)随代码提供，执行 M1–M11 验收；推送会触发远端检查。远端是否通过，请查看 [Actions 对应提交](https://github.com/Lshiqi67/domino-tilings-a232622/actions/workflows/lean.yml)；本地通过与远端通过分别记录。

既定 **M1–M11 已全部完成**。下一步是外部人工语义审阅和论文覆盖说明更新；一般高度渐近仍是独立推广任务。欧氏全部等距分类、其余全文扩展及文献优先权未在本轮获得认证。
