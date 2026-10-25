"""复核 M1–M9：五行压缩、真实铺法轨道有理式、十四阶递推及完整初值。"""
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

import check_m1 as foundations
import check_m7_m8 as preceding

BASE = Path(__file__).resolve().parents[1]
AUDIT = BASE / "Domino/Audit/M9.lean"
INVENTORY = BASE / "docs/m9-declarations.json"
DECLARATION = re.compile(
    r"^(?:@\[[^\n]*\]\s+)?(?:noncomputable\s+)?"
    r"(abbrev|def|theorem|lemma|structure|inductive|instance)\s+([A-Za-z_][A-Za-z_0-9']*)\b", re.M)


def make_inventory() -> dict:
    prior = preceding.make_inventory()
    declarations = prior["declarations"].copy()
    modules = prior["modules"].copy()
    for folder, stage, namespace in [("FiveRows", "M9", "Domino.FiveRows")]:
        for path in sorted((BASE / "Domino" / folder).glob("*.lean")):
            relative = path.relative_to(BASE).as_posix()
            modules.append(relative)
            source = foundations.without_comments(path.read_text(encoding="utf-8"))
            if re.findall(r"^namespace (\S+)", source, re.M) != [namespace]:
                raise ValueError(f"声明命名空间需显式审阅：{relative}")
            if re.search(r"^(?:noncomputable\s+)?instance\s*[{(:]", source, re.M):
                raise ValueError(f"请命名待审计实例：{relative}")
            for match in DECLARATION.finditer(source):
                declarations.append({"name": f"{namespace}.{match[2]}", "kind": match[1],
                    "file": relative, "stage": stage, "line": source.count("\n", 0, match.start()) + 1})
    names = [d["name"] for d in declarations]
    if len(names) != len(set(names)):
        raise ValueError("声明名称重复")
    return {"stage": "M1-M9", "scope": "全部生产数学模块的显式命名声明及其传递公理依赖",
            "modules": modules, "declarations": declarations}


def audit_source(inventory: dict) -> str:
    return ("module\n\nimport Domino\n\n"
        "/-! M1–M9 累计公理审计；由 scripts/check_m9.py --refresh-audit 生成。 -/\n\n"
        + "".join(f"#print axioms {d['name']}\n" for d in inventory["declarations"]))


def audit_output(output: str, inventory: dict) -> dict:
    pattern = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
    audited = {}
    for match in pattern.finditer(output):
        if match[1] in audited:
            raise ValueError(f"重复公理输出：{match[1]}")
        axioms = [] if match[3] else [x.strip() for x in match[2].split(",") if x.strip()]
        if set(axioms) - foundations.ALLOWED_AXIOMS:
            raise ValueError(f"{match[1]} 含额外公理：{axioms}")
        audited[match[1]] = axioms
    if set(audited) != {d["name"] for d in inventory["declarations"]}:
        raise ValueError("公理输出未精确覆盖声明清单")
    return audited


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-audit", action="store_true")
    parser.add_argument("--report-dir", help="尚不存在的目录；保留历史运行")
    args = parser.parse_args()
    inventory = make_inventory()
    if args.refresh_audit:
        if args.report_dir:
            parser.error("生成审计入口与验收分开执行")
        AUDIT.write_bytes(audit_source(inventory).encode("utf-8"))
        INVENTORY.write_bytes((json.dumps(inventory, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
        print(f"生成 {len(inventory['modules'])} 模块、{len(inventory['declarations'])} 项显式声明；尚未验收。")
        return 0
    if not args.report_dir:
        parser.error("验收需要 --report-dir")
    destination = (BASE / args.report_dir).resolve()
    destination.mkdir(parents=True, exist_ok=False)
    report = {"date": datetime.now(timezone(timedelta(hours=8))).isoformat(), "stage": "M1-M9",
        "scope": "M9 全部 32 状态的支持与反转压缩、真实五行四类计数、多项式证书、主有理式、十四阶递推、14 项初值和首个递推点",
        "random_seed": None, "commands": [], "checks": {}, "source_sha256": {},
        "not_verified": ["M10 渐近", "M11 基本块第二证明",
                         "最小递推阶", "欧氏全部等距分类", "外部人工语义审阅及文献优先权"]}

    def run(name: str, argv: list[str], cwd: Path = BASE) -> str:
        print(f"运行 {name}", flush=True)
        p = subprocess.run(argv, cwd=cwd, capture_output=True, encoding="utf-8", errors="replace", timeout=3600)
        output = p.stdout + p.stderr
        (destination / f"{name}.txt").write_text(output, encoding="utf-8")
        report["commands"].append({"name": name, "argv": argv, "cwd": str(cwd),
                                   "exit_code": p.returncode, "output": f"{name}.txt"})
        if p.returncode:
            raise RuntimeError(f"{name} 退出码 {p.returncode}")
        return output

    try:
        if json.loads(INVENTORY.read_text(encoding="utf-8")) != inventory or AUDIT.read_text(encoding="utf-8") != audit_source(inventory):
            raise ValueError("声明清单或审计入口与源码不一致")
        report["checks"]["inventory_matches_sources"] = True
        report["module_count"] = len(inventory["modules"])
        report["declaration_count"] = len(inventory["declarations"])
        report["declaration_counts"] = dict(Counter(d["kind"] for d in inventory["declarations"]))
        report["stages"] = {s: dict(Counter(d["kind"] for d in inventory["declarations"] if d["stage"] == s))
                            for s in ["M9"]}
        baseline = BASE / "evidence/m7-m8-2026-10-25/verification-01/report.json"
        if not baseline.is_file():
            raise ValueError("缺少 M7/M8 基线报告")
        old = json.loads(baseline.read_text(encoding="utf-8"))
        for relative in preceding.make_inventory()["modules"] + ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]:
            if hashlib.sha256((BASE / relative).read_bytes()).hexdigest() != old["source_sha256"][relative]:
                raise ValueError(f"M1–M8 数学源码或版本锁改变：{relative}")
        report["checks"]["M1_M8_57_sources_and_locks_unchanged"] = True
        # 递归回归 M1–M8；M6 的干净构建会复制当前全部数学源码（含 M9）。
        regression_dir = destination / "m7-m8-regression"
        run("m7-m8-regression", [sys.executable, "-X", "utf8", "scripts/check_m7_m8.py", "--report-dir", str(regression_dir)])
        prior = json.loads((regression_dir / "report.json").read_text(encoding="utf-8"))
        if prior["status"] != "m7_m8_passed":
            raise ValueError("M7/M8 回归未通过")
        for key in ["lean_version", "lake_version", "dependencies"]:
            report[key] = prior[key]
        report["checks"]["locked_environment_full_build_and_M1_M8_regression"] = True
        output = run("axioms", ["lake", "env", "lean", "-DwarningAsError=true", "Domino/Audit/M9.lean"])
        report["axiom_dependencies"] = audit_output(output, inventory)
        report["allowed_axioms"] = sorted(foundations.ALLOWED_AXIOMS)
        report["checks"]["all_declarations_audited"] = True
        statements = run("main-statements", ["lake", "env", "lean", "-DwarningAsError=true", "Domino/Audit/M9Statement.lean"])
        clean = regression_dir / "m6-regression" / "clean-project"
        for relative, digest in prior["clean_source_sha256"].items():
            if hashlib.sha256((BASE / relative).read_bytes()).hexdigest() != digest:
                raise ValueError(f"重建后源码已变动：{relative}")
            if hashlib.sha256((clean / relative).read_bytes()).hexdigest() != digest:
                raise ValueError(f"干净目录源码已变动：{relative}")
        report["clean_source_sha256"] = prior["clean_source_sha256"]
        clean_lake = ["lake", "--packages", str(regression_dir / "m6-regression" / "dependency-overrides.json"), "--no-cache"]
        clean_output = run("clean-axioms", clean_lake + ["env", "lean", "-DwarningAsError=true", "Domino/Audit/M9.lean"], cwd=clean)
        if clean_output != output:
            raise ValueError("干净重建的公理输出不一致")
        clean_statements = run("clean-main-statements", clean_lake + ["env", "lean", "-DwarningAsError=true", "Domino/Audit/M9Statement.lean"], cwd=clean)
        if clean_statements != statements:
            raise ValueError("干净重建的主定理输出不一致")
        report["clean_project_scope"] = "本次嵌套 M6 回归已复制全部新旧项目源码并在没有自身产物的新目录完整构建；复用该干净目录审计 M1–M9。第三方固定版本缓存共享，未全量重编译 mathlib。"
        report["checks"]["clean_build_sources_axioms_and_statements_identical"] = True
        report["status"] = "m9_passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        paths = [BASE / p for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "Domino.lean", "docs/m9-declarations.json"]]
        paths += [*sorted((BASE / "Domino").rglob("*.lean")), *sorted((BASE / "scripts").glob("check_*.py"))]
        for path in paths:
            report["source_sha256"][path.relative_to(BASE).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
        (destination / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(report["status"], flush=True)
    return 0 if report["status"] == "m9_passed" else 1


if __name__ == "__main__":
    sys.exit(main())
