"""复核 M1–M5：真实计数的二维压缩、奇偶公式、Burnside 及累计公理。"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

import check_m1 as foundations
import check_m3 as preceding

BASE = Path(__file__).resolve().parents[1]
M4_MODULES = [f"Domino/ThreeRows/{name}.lean" for name in ["ProfileRecurrence", "Ordinary", "FixedCounts"]]
M5_MODULES = ["Domino/Symmetry/Burnside.lean", "Domino/ThreeRows/OrbitCounts.lean", "Domino/ThreeRows/Boundary.lean"]
NEW_MODULES = M4_MODULES + M5_MODULES
MODULES = preceding.MODULES + NEW_MODULES
AUDIT = BASE / "Domino/Audit/M4M5.lean"
INVENTORY = BASE / "docs/m4-m5-declarations.json"


def make_inventory() -> dict:
    declarations = []
    prior_stages = {d["name"]: d["stage"] for d in preceding.make_inventory()["declarations"]}
    for relative in MODULES:
        source = foundations.without_comments((BASE / relative).read_text(encoding="utf-8"))
        for match in foundations.DECLARATION.finditer(source):
            declarations.append({"name": f"Domino.{match[2]}", "kind": match[1], "file": relative,
                                 "stage": "M4" if relative in M4_MODULES else ("M5" if relative in M5_MODULES else prior_stages[f"Domino.{match[2]}"]),
                                 "line": source.count("\n", 0, match.start()) + 1})
    names = [d["name"] for d in declarations]
    if len(set(names)) != len(names):
        raise ValueError("声明名称重复")
    return {"stage": "M1-M5", "scope": "27 个已实现生产模块的显式命名声明及其传递公理依赖",
            "modules": MODULES, "declarations": declarations}


def audit_source(inventory: dict) -> str:
    return ("module\n\nimport Domino\n\n"
            "/-! M1–M5 公理审计。由 scripts/check_m4_m5.py --refresh-audit 生成。 -/\n\n"
            + "".join(f"#print axioms {d['name']}\n" for d in inventory["declarations"]))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-audit", action="store_true")
    parser.add_argument("--report-dir", help="使用新的报告目录，不覆盖历史")
    args = parser.parse_args()
    inventory = make_inventory()
    if args.refresh_audit:
        if args.report_dir:
            parser.error("生成入口与验收分别执行")
        AUDIT.parent.mkdir(parents=True, exist_ok=True)
        AUDIT.write_text(audit_source(inventory), encoding="utf-8")
        INVENTORY.write_text(json.dumps(inventory, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"生成 {len(inventory['declarations'])} 项声明清单；尚未执行验收。")
        return 0
    if not args.report_dir:
        parser.error("验收需要 --report-dir")
    destination = (BASE / args.report_dir).resolve()
    destination.mkdir(parents=True, exist_ok=False)
    report = {
        "date": datetime.now(timezone(timedelta(hours=8))).isoformat(), "stage": "M1-M5",
        "scope": "全部自然数指标的三行支持与二维计数、普通二阶递推、固定点奇偶式、实际群作用 Burnside 与轨道奇偶式",
        "random_seed": None, "commands": [], "checks": {}, "source_sha256": {},
        "paper_main_theorem_verified": False,
        "not_verified": ["三行主生成函数与七阶递推及完整七项初值", "一般高度及全文扩展", "基本块第二证明"],
    }

    def run(name: str, argv: list[str]) -> str:
        print(f"运行 {name}", flush=True)
        p = subprocess.run(argv, cwd=BASE, capture_output=True, encoding="utf-8", errors="replace", timeout=2400)
        output = p.stdout + p.stderr
        (destination / f"{name}.txt").write_text(output, encoding="utf-8")
        report["commands"].append({"name": name, "argv": argv, "cwd": str(BASE),
                                   "exit_code": p.returncode, "output": f"{name}.txt"})
        if p.returncode:
            raise RuntimeError(f"{name} 退出码 {p.returncode}")
        return output

    try:
        if json.loads(INVENTORY.read_text(encoding="utf-8")) != inventory or AUDIT.read_text(encoding="utf-8") != audit_source(inventory):
            raise ValueError("声明清单或审计入口与源码不一致")
        report["checks"]["audit_inventory_matches_sources"] = True
        report["declaration_counts"] = dict(Counter(d["kind"] for d in inventory["declarations"]))
        for stage in ["M4", "M5"]:
            report[f"new_{stage}_declaration_counts"] = dict(Counter(d["kind"] for d in inventory["declarations"] if d["stage"] == stage))
        old_report = BASE / "evidence/m3-2026-10-25/verification-01/report.json"
        if old_report.exists():
            old = json.loads(old_report.read_text(encoding="utf-8"))
            for relative in preceding.MODULES + ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
                if hashlib.sha256((BASE / relative).read_bytes()).hexdigest() != old["source_sha256"][relative]:
                    raise ValueError(f"M1–M3 源码或版本锁发生改动，需要单独审阅：{relative}")
            report["checks"]["M1_M2_M3_sources_and_locks_unchanged"] = True
        else:
            report["checks"]["M1_M2_M3_sources_and_locks_unchanged"] = "历史报告不在当前副本中，跳过历史对比"
        # 原 M3 脚本递归复核固定环境及 M1–M3；旧报告不覆盖。
        run("m3-regression", [sys.executable, "-X", "utf8", "scripts/check_m3.py",
                              "--report-dir", str(destination / "m3-regression")])
        previous = json.loads((destination / "m3-regression/report.json").read_text(encoding="utf-8"))
        if previous["status"] != "m3_passed":
            raise ValueError("M3 回归未通过")
        report["checks"]["locked_environment_full_build_and_M1_M2_M3_regression"] = True
        for key in ["lean_version", "lake_version", "dependencies"]:
            report[key] = previous[key]
        output = run("axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Domino/Audit/M4M5.lean"])
        import re
        matches = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
        audited = {}
        for match in matches.finditer(output):
            if match[1] in audited:
                raise ValueError(f"重复公理输出：{match[1]}")
            axioms = [] if match[3] else [x.strip() for x in match[2].split(",") if x.strip()]
            if set(axioms) - foundations.ALLOWED_AXIOMS:
                raise ValueError(f"{match[1]} 有非许可公理：{axioms}")
            audited[match[1]] = axioms
        if set(audited) != {d["name"] for d in inventory["declarations"]}:
            raise ValueError("审计输出没有精确覆盖声明清单")
        report["axiom_dependencies"] = audited
        report["allowed_axioms"] = sorted(foundations.ALLOWED_AXIOMS)
        report["checks"]["every_listed_declaration_audited"] = True
        report["checked_paper_nodes"] = ["C01", "A01", "B01", "B02", "B03", "B04", "B05", "B06", "B07", "C02"]
        report["status"] = "m4_m5_passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        paths = [BASE / p for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "Domino.lean",
                                    "docs/coverage.json", "docs/formalization-plan.md", "docs/m4-m5-counting.md",
                                    "docs/m4-m5-declarations.json", "scripts/check_project.py", "scripts/check_m1.py", "scripts/check_m2.py", "scripts/check_m3.py"]]
        paths += [Path(__file__), *sorted((BASE / "Domino").rglob("*.lean"))]
        for path in paths:
            if path.is_file():
                report["source_sha256"][path.relative_to(BASE).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
        (destination / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(report["status"], flush=True)
    return 0 if report["status"] == "m4_m5_passed" else 1


if __name__ == "__main__":
    sys.exit(main())
