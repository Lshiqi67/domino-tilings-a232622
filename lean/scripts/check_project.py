"""检查固定版本与基础构建；不会把环境成功标成数学证明成功。"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone, timedelta

BASE = Path(__file__).resolve().parents[1]
EXPECTED_LEAN = "leanprover/lean4:v4.35.0"
EXPECTED_MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", required=True,
                        help="必须是尚不存在的报告目录，避免覆盖历史记录")
    args = parser.parse_args()
    report_dir = (BASE / args.report_dir).resolve()
    report_dir.mkdir(parents=True, exist_ok=False)
    report = {
        "date": datetime.now(timezone(timedelta(hours=8))).isoformat(),
        "scope": "E0 固定版本与环境模块；无论文定理验证",
        "random_seed": None,
        "commands": [], "checks": {}, "source_sha256": {},
        "paper_theorems_verified": [],
    }

    def run(name: str, argv: list[str]) -> str:
        print(f"运行 {name}", flush=True)
        proc = subprocess.run(argv, cwd=BASE, capture_output=True,
                              encoding="utf-8", errors="replace", timeout=1800)
        output = proc.stdout + proc.stderr
        (report_dir / f"{name}.txt").write_text(output, encoding="utf-8")
        report["commands"].append({"name": name, "argv": argv,
                                   "cwd": str(BASE), "exit_code": proc.returncode,
                                   "output": f"{name}.txt"})
        if proc.returncode:
            raise RuntimeError(f"{name} 失败，退出码 {proc.returncode}")
        return output.strip()

    try:
        report["lean_version"] = run("lean-version", ["lean", "--version"])
        report["lake_version"] = run("lake-version", ["lake", "--version"])
        assert (BASE / "lean-toolchain").read_text().strip() == EXPECTED_LEAN
        assert "version 4.35.0," in report["lean_version"]
        report["checks"]["lean_version"] = True
        config = (BASE / "lakefile.toml").read_text(encoding="utf-8")
        assert f'rev = "{EXPECTED_MATHLIB}"' in config
        manifest = json.loads((BASE / "lake-manifest.json").read_text(encoding="utf-8"))
        packages = manifest["packages"]
        mathlib = next(p for p in packages if p["name"] == "mathlib")
        assert mathlib["rev"] == EXPECTED_MATHLIB
        report["dependencies"] = packages
        for p in packages:
            assert p["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", p["rev"])
            checkout = BASE / ".lake" / "packages" / p["name"]
            head = run(f"{p['name']}-revision", ["git", "-C", str(checkout), "rev-parse", "HEAD"])
            assert head == p["rev"], f"{p['name']} 实际提交不匹配"
            dirty = run(f"{p['name']}-status", ["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"])
            assert not dirty, f"{p['name']} 存在已跟踪文件修改"
        assert (BASE / ".lake/packages/mathlib/lean-toolchain").read_text().strip() == EXPECTED_LEAN
        report["checks"]["locked_dependencies"] = True

        coverage = json.loads((BASE / "docs/coverage.json").read_text(encoding="utf-8"))
        nodes = coverage["nodes"] + coverage["extensions"]
        mapping = {n["id"]: n for n in nodes}
        assert len(mapping) == len(nodes)
        visiting, visited = set(), set()
        def visit(key):
            assert key in mapping, f"未知依赖 {key}"
            assert key not in visiting, f"循环依赖 {key}"
            if key in visited:
                return
            visiting.add(key)
            for dep in mapping[key].get("depends", []):
                visit(dep)
            visiting.remove(key)
            visited.add(key)
        for key in mapping:
            visit(key)
        chain = (BASE / "docs" / coverage["source_chain"]).resolve()
        if chain.exists():
            originals = json.loads(chain.read_text(encoding="utf-8"))["claims"]
            assert {n["id"] for n in originals} == {n["id"] for n in coverage["nodes"]}
            report["checks"]["original_chain_ids"] = True
        else:
            report["checks"]["original_chain_ids"] = "本地研究工作区不存在，单仓库复现跳过"
        report["checks"]["coverage_dag"] = True
        report["coverage_statuses"] = {n["id"]: n["status"] for n in nodes}

        source_files = [BASE / "Domino.lean", *sorted((BASE / "Domino").rglob("*.lean"))]
        forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide)\b")
        for source in source_files:
            # 当前文件中没有嵌套注释；这里只是源码初筛，不替代出口公理审计。
            text = re.sub(r"/-.*?-/", "", source.read_text(encoding="utf-8"), flags=re.S)
            assert not forbidden.search(text), f"需要审阅的证明占位或信任声明：{source}"
        report["checks"]["source_screen"] = True
        run("lake-build", ["lake", "--wfail", "build"])
        run("lean-entry", ["lake", "env", "lean", "-DwarningAsError=true", "Domino.lean"])
        report["checks"]["environment_build"] = True
        report["status"] = "environment_passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = f"{type(exc).__name__}: {exc}"
    finally:
        paths = [BASE / "lean-toolchain", BASE / "lakefile.toml", BASE / "lake-manifest.json",
                 BASE / "Domino.lean", BASE / "docs/coverage.json",
                 BASE / "docs/formalization-plan.md", Path(__file__),
                 *sorted((BASE / "Domino").rglob("*.lean"))]
        for path in paths:
            if path.is_file():
                report["source_sha256"][path.relative_to(BASE).as_posix()] = sha256(path)
        (report_dir / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(report["status"], flush=True)
    return 0 if report["status"] == "environment_passed" else 1


if __name__ == "__main__":
    sys.exit(main())
