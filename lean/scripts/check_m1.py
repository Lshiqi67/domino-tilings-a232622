"""复核 M1 的固定环境、完整构建与逐声明公理依赖；保留每次运行记录。"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = Path(__file__).resolve().parents[1]
MODULES = [
    "Domino/Board/Basic.lean", "Domino/Board/Tiling.lean",
    "Domino/Board/Partial.lean", "Domino/Board/Examples.lean",
    "Domino/Symmetry/Action.lean", "Domino/Symmetry/Counting.lean",
]
AUDIT = BASE / "Domino/Audit/M1.lean"
INVENTORY = BASE / "docs/m1-declarations.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECLARATION = re.compile(
    r"^(?:@\[[^\n]*\]\s+)?(?:noncomputable\s+)?"
    r"(abbrev|def|theorem|structure|instance)\s+([A-Za-z_][A-Za-z_0-9']*)\b", re.M)


def without_comments(source: str) -> str:
    """保留行号，移除行注释和可嵌套块注释；M1 源码无字符串字面量。"""
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.append(" " * (end - i))
            i = end
        else:
            c = source[i]
            result.append(c if not depth or c == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("未闭合的 Lean 块注释")
    return "".join(result)


def make_inventory() -> dict:
    declarations = []
    for relative in MODULES:
        source = without_comments((BASE / relative).read_text(encoding="utf-8"))
        if re.search(r"^(?:noncomputable\s+)?instance\s*[{(:]", source, re.M):
            raise ValueError(f"请为需审计的实例命名：{relative}")
        for match in DECLARATION.finditer(source):
            declarations.append({
                "name": f"Domino.{match[2]}", "kind": match[1], "file": relative,
                "line": source.count("\n", 0, match.start()) + 1,
            })
    names = [d["name"] for d in declarations]
    if len(names) != len(set(names)):
        raise ValueError("M1 声明名重复")
    return {"stage": "M1", "scope": "六个 M1 模块中显式命名的类型、定义、定理和实例；依赖递归由 Lean 审计",
            "modules": MODULES, "declarations": declarations}


def audit_source(inventory: dict) -> str:
    return ("module\n\nimport Domino\n\n"
            "/-! M1 逐声明公理审计。由 scripts/check_m1.py --refresh-audit 生成。 -/\n\n"
            + "".join(f"#print axioms {d['name']}\n" for d in inventory["declarations"]))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-audit", action="store_true",
                        help="只更新声明清单与审计入口，不执行也不宣称验收")
    parser.add_argument("--report-dir", help="新的报告目录，不覆盖已有结果")
    args = parser.parse_args()
    inventory = make_inventory()
    if args.refresh_audit:
        if args.report_dir:
            parser.error("生成审计入口与运行验收是两个独立命令")
        AUDIT.parent.mkdir(parents=True, exist_ok=True)
        AUDIT.write_text(audit_source(inventory), encoding="utf-8")
        INVENTORY.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"已生成 {len(inventory['declarations'])} 项声明清单；尚未运行验收。")
        return 0
    if not args.report_dir:
        parser.error("验收需要 --report-dir")
    report_dir = (BASE / args.report_dir).resolve()
    report_dir.mkdir(parents=True, exist_ok=False)
    report = {
        "date": datetime.now(timezone(timedelta(hours=8))).isoformat(),
        "stage": "M1", "scope": "有限棋盘、精确覆盖、部分铺法、四元群作用、实际轨道及空棋盘",
        "random_seed": None, "commands": [], "checks": {}, "source_sha256": {},
        "paper_main_theorem_verified": False,
        "not_verified": ["铺法与路径双射", "半棋盘补全双射", "Burnside 计数公式", "正宽固定点数",
                         "生成函数及七阶递推", "欧氏全等距变换分类"],
    }

    def run(name: str, argv: list[str]) -> str:
        print(f"运行 {name}", flush=True)
        proc = subprocess.run(argv, cwd=BASE, capture_output=True, encoding="utf-8",
                              errors="replace", timeout=1800)
        output = proc.stdout + proc.stderr
        (report_dir / f"{name}.txt").write_text(output, encoding="utf-8")
        report["commands"].append({"name": name, "argv": argv, "cwd": str(BASE),
                                   "exit_code": proc.returncode, "output": f"{name}.txt"})
        if proc.returncode:
            raise RuntimeError(f"{name} 失败：退出码 {proc.returncode}")
        return output

    try:
        if json.loads(INVENTORY.read_text(encoding="utf-8")) != inventory:
            raise ValueError("声明清单与源码不一致；先更新审计入口")
        if AUDIT.read_text(encoding="utf-8") != audit_source(inventory):
            raise ValueError("审计入口与声明清单不一致")
        report["checks"]["audit_inventory_matches_sources"] = True
        report["declaration_counts"] = dict(Counter(d["kind"] for d in inventory["declarations"]))
        # 沿用 E0 的锁定环境复核；其历史报告不修改，也不将其标签当成 M1 证明。
        run("environment-check", [sys.executable, "-X", "utf8", "scripts/check_project.py",
                                  "--report-dir", str(report_dir / "environment")])
        environment = json.loads((report_dir / "environment/report.json").read_text(encoding="utf-8"))
        if environment["status"] != "environment_passed":
            raise ValueError("基础环境复核未通过")
        report["checks"]["locked_environment_and_full_build"] = True
        report["lean_version"] = environment["lean_version"]
        report["lake_version"] = environment["lake_version"]
        report["dependencies"] = environment["dependencies"]

        forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide)\b")
        for source in [BASE / "Domino.lean", *sorted((BASE / "Domino").rglob("*.lean"))]:
            if forbidden.search(without_comments(source.read_text(encoding="utf-8"))):
                raise ValueError(f"源码中含需审阅的占位或信任声明：{source}")
        report["checks"]["source_screen"] = True
        output = run("axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Domino/Audit/M1.lean"])
        pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
        audited = {}
        for match in pattern.finditer(output):
            name = match[1]
            if name in audited:
                raise ValueError(f"重复审计输出：{name}")
            axioms = [] if match[3] else [x.strip() for x in match[2].split(",") if x.strip()]
            if set(axioms) - ALLOWED_AXIOMS:
                raise ValueError(f"{name} 含非许可公理：{axioms}")
            audited[name] = axioms
        expected = {d["name"] for d in inventory["declarations"]}
        if set(audited) != expected:
            raise ValueError(f"审计输出集合不一致：缺少 {sorted(expected-set(audited))}，额外 {sorted(set(audited)-expected)}")
        report["axiom_dependencies"] = audited
        report["allowed_axioms"] = sorted(ALLOWED_AXIOMS)
        report["checks"]["every_listed_declaration_audited"] = True
        report["status"] = "m1_passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        paths = [BASE / "lean-toolchain", BASE / "lakefile.toml", BASE / "lake-manifest.json",
                 BASE / "Domino.lean", BASE / "docs/coverage.json", INVENTORY,
                 BASE / "docs/formalization-plan.md", Path(__file__),
                 BASE / "scripts/check_project.py", *sorted((BASE / "Domino").rglob("*.lean"))]
        for path in paths:
            if path.is_file():
                report["source_sha256"][path.relative_to(BASE).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
        (report_dir / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(report["status"], flush=True)
    return 0 if report["status"] == "m1_passed" else 1


if __name__ == "__main__":
    sys.exit(main())
