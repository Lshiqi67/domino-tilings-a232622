# 复现入口与实际检查范围

更新：2026-10-29。本页区分一般性 Lean 证明、有限计算和论文编译。

## 1. M1–M11 累计验收

需要 Git、elan 管理的 Lean/Lake、Python 3。固定 Lean 4.35.0 和 mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`；不要运行 `lake update` 改动版本锁。

```bash
git clone -c core.longpaths=true https://github.com/Lshiqi67/domino-tilings-a232622.git
cd domino-tilings-a232622
git checkout paper-en-v2.1
cd lean
lake exe cache get
python -X utf8 scripts/check_m11.py --report-dir checks/reproduction-v2.1
```

报告目录必须尚不存在；部分系统需使用 python3。成功条件是退出码 0 且最终 report.json 中 status=m11_passed。缓存下载只准备依赖，验收脚本才执行构建、回归、公理审计及新目录重建。83 模块/1078 声明包含辅助工具，不等于 1078 个论文定理。

[10 月 28–29 日实际运行](review/arxiv-v2.1/verification/lean/report.json)与[运行说明](lean/README.md)提供命令、源哈希、公理映射和范围。公开日志中的路径占位符只用于脱敏，不是可复制的运行路径。

## 2. 论文与发布文件检查

```powershell
python -X utf8 scripts/check_release.py
python -X utf8 review/m1-m6/check_pack.py
python -X utf8 review/m1-m6/check_delivery.py
cd papers/en
./build.ps1
```

发布检查核对当前 PDF/TeX 与投稿 ZIP、历史版本摘要、形式化输入哈希、声明定位及链接；不重新启动 Lean。旧审阅包检查继续绑定英文 v2.0，输出写入 tmp，原报告不覆盖。论文构建需要 Python/SymPy、pdfLaTeX 和标准 TeX 包；会更新本地 PDF 与当前转录报告。

## 3. 历史有限计算

2026-10-25 的公开准备运行使用 Python 3.13.0、SymPy 1.13.1，确定性、精确算术、无随机种子。原记录范围如下；本次仓库同步未再次运行这些枚举。

| 程序 | 实际历史范围 | 结果 |
| --- | --- | --- |
| verify_blocks.py | 三行 n=0..8，40,545 个铺法，分解及对称 | 通过 |
| derive_functions.py | 三/五行精确式，n=0..100 系数与矩阵对照 | 通过 |
| verify_geometry.py | 四种奇数高度指定范围，57,468 个铺法 | 通过 |
| five_row_certificate.py | 六维多项式证书及全矩阵比较 | 通过 |

[research/README.md](research/README.md)给出具体命令。请在新临时副本中运行会在源目录写报告的历史程序。n=0..100 对照不是该范围的全体铺法枚举；一般结论的依据是论文论证及对应 Lean 证明。
