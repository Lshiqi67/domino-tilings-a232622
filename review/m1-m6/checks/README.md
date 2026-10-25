# 本轮实际检查

日期：2026-10-25。不是历史 M6 报告的重命名副本。

命令（仓库根目录）：

```powershell
python -X utf8 review/m1-m6/check_pack.py --lean --output review/m1-m6/checks/verification-01
```

实际状态：[passed](verification-01/report.json)。32 个固定数学模块、25 项语义映射、152 个映射声明、413 项公理探针通过；Lean 4.35.0、mathlib 精确提交与锁一致。数学源码及三个环境配置与历史 M6 报告一致。允许公理只有 propext、Classical.choice、Quot.sound，逐声明依赖集合与历史 M6 完全一致。

- [构建输出](verification-01/build.txt)：成功，3215 个含依赖任务；这是显式指定模块的增量构建，不是全部任务都重新编译。
- [类型与关键定义输出](verification-01/types.txt)：方便审阅者逐项展开定义，与源码一同阅读。
- [413 项公理输出](verification-01/axioms.txt)。
- [工具版本](verification-01/lean-version.txt)、[mathlib 提交](verification-01/mathlib-revision.txt)。
- [交付检查](delivery-report.json)：论文引用、归档、摘要及局部推导等检查，运行脚本见上级目录。

运行环境：Windows PowerShell、Python 3.13.0、已固定的 Lean/mathlib 和已有第三方缓存；确定性，无随机种子。无新的干净项目重建，无新的历史铺法穷举，无外部人类审阅。各检查脚本保存范围，未将 M7–M11 导入探针。语义映射中的准备者判断不是编译器可自动判定的结论。

交付脚本首轮曾把自身尚未生成的 delivery-report.json 当作缺失链接；改为在全部检查通过后生成该报告，并仅排除该自指输出的预检查。修正后通过。额外版本化 PDF 复制首轮使用未解析的相对根路径而失败，改为已解析仓库绝对根后保存成功。均为交付工程问题，不改变数学或 Lean 结论。
