"""选题阶段有限核验；不是对任意 n 的证明。只使用 Python 标准库。"""

import argparse
import hashlib
import json
import platform
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path


def tilings(width):
    """每次覆盖行优先次序中第一个空格，枚举全部多米诺完美匹配。"""
    full = (1 << (3 * width)) - 1

    def visit(mask, pairs):
        if mask == full:
            yield tuple(sorted(pairs))
            return
        remaining = full ^ mask
        cell = (remaining & -remaining).bit_length() - 1
        row, col = divmod(cell, width)
        neighbors = []
        if col + 1 < width:
            neighbors.append(cell + 1)
        if row + 1 < 3:
            neighbors.append(cell + width)
        for other in neighbors:
            if not (mask >> other) & 1:
                yield from visit(mask | (1 << cell) | (1 << other),
                                 pairs + ((cell, other),))

    yield from visit(0, ())


def inspect(n):
    width = 2 * n
    # n=0 按空铺法计 1；四个形式操作都固定它。
    maps = []
    for flip_rows, flip_cols in [(False, False), (True, False),
                                (False, True), (True, True)]:
        maps.append(tuple((2-r if flip_rows else r) * width
                          + (width-1-c if flip_cols else c)
                          for r in range(3) for c in range(width)))
    fixed = [0] * 4
    orbits = set()
    for matching in tilings(width):
        images = [tuple(sorted(tuple(sorted((mapping[a], mapping[b])))
                               for a, b in matching)) for mapping in maps]
        for i, transformed in enumerate(images):
            fixed[i] += transformed == matching
        orbits.add(min(images))
    assert sum(fixed) == 4 * len(orbits)
    return {"n": n, "board": [3, width], "labelled_tilings": fixed[0],
            "fixed_counts_identity_rowflip_colflip_halfturn": fixed,
            "orbits": len(orbits)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0 <= args.max_n <= 8:
        parser.error("本筛选脚本只允许 0 <= max-n <= 8")
    started = time.perf_counter()
    rows = [inspect(n) for n in range(args.max_n + 1)]
    expected = [1, 2, 5, 14, 46, 156, 561, 2037, 7525]
    observed = [row["orbits"] for row in rows]
    recurrence = [5, -1, -19, 19, 1, -5, 1]
    checks = {str(n): observed[n] == sum(c * observed[n-i-1]
               for i, c in enumerate(recurrence))
              for n in range(7, args.max_n + 1)}
    report = {
        "date_beijing": datetime.now(timezone(timedelta(hours=8))).isoformat(),
        "command": "python " + " ".join(sys.argv),
        "cwd": str(Path.cwd()), "python": sys.version,
        "platform": platform.platform(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_for_expected": "https://oeis.org/A232622",
        "random_seed": None, "method": "deterministic exhaustive enumeration",
        "range": [0, args.max_n], "rows": rows,
        "matches_oeis_prefix": observed == expected[:len(observed)],
        "recurrence_checks_only_at_listed_indices": checks,
        "elapsed_seconds": time.perf_counter() - started,
        "limitations": "仅核验 n=0..max-n。Burnside 与轨道规范化共用同一铺法枚举；不构成任意 n 的证明或新颖性核查。",
    }
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2)
                           + "\n", encoding="utf-8")
    print(json.dumps({"counts": observed, "matches": report["matches_oeis_prefix"],
                      "recurrence_checks": checks,
                      "elapsed_seconds": report["elapsed_seconds"]}))
    assert report["matches_oeis_prefix"] and all(checks.values())


if __name__ == "__main__":
    main()
