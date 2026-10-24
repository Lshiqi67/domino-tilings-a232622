"""基本块路线的有限穷举与精确代数检查；不替代一般组合证明。"""

import argparse
import hashlib
import importlib.util
import json
import platform
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parents[5]
ENUMERATOR = ROOT / "01_topics/checks/a232622-screening/check_tilings.py"
HISTORY = ENUMERATOR.with_name("report.json")
spec = importlib.util.spec_from_file_location("historical_tilings", ENUMERATOR)
historical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(historical)


def canonical(pairs):
    return tuple(sorted(tuple(sorted(pair)) for pair in pairs))


def transform(matching, width, flip_rows=False, flip_cols=False):
    def cell_image(cell):
        row, col = divmod(cell, width)
        return (2 - row if flip_rows else row) * width + (
            width - 1 - col if flip_cols else col)

    return canonical((cell_image(a), cell_image(b)) for a, b in matching)


def block(kind, k):
    """论文坐标定义的独立实现；行和列在程序内从 0 起算。"""
    assert k >= 1 and kind in {"A", "B", "C"}
    width = 2 * k
    if kind == "C":
        assert k == 1
        return 2, canonical((2*r, 2*r+1) for r in range(3))
    pairs = [(0, width), (width-1, 2*width-1)]
    pairs.extend((2*width+c, 2*width+c+1) for c in range(0, width, 2))
    pairs.extend((r*width+c, r*width+c+1)
                 for r in (0, 1) for c in range(1, width-1, 2))
    matching = canonical(pairs)
    if kind == "B":
        matching = transform(matching, width, flip_rows=True)
    return width, matching


def check_cover(matching, width):
    cells = [cell for pair in matching for cell in pair]
    assert sorted(cells) == list(range(3 * width))
    for a, b in matching:
        ar, ac = divmod(a, width)
        br, bc = divmod(b, width)
        assert abs(ar-br) + abs(ac-bc) == 1


def cut_columns(matching, width):
    crossed = set()
    for a, b in matching:
        ar, ac = divmod(a, width)
        br, bc = divmod(b, width)
        if ar == br:
            crossed.add(min(ac, bc) + 1)
    return [j for j in range(1, width) if j not in crossed]


def factor(matching, width):
    if width == 0:
        assert matching == ()
        return ()
    boundaries = [0] + cut_columns(matching, width) + [width]
    word = []
    for start, stop in zip(boundaries, boundaries[1:]):
        length = stop - start
        assert length % 2 == 0
        pairs = []
        for a, b in matching:
            ar, ac = divmod(a, width)
            br, bc = divmod(b, width)
            if start <= ac < stop:
                assert start <= bc < stop
                pairs.append((ar*length+ac-start, br*length+bc-start))
        local = canonical(pairs)
        labels = [(kind, length//2) for kind in ("A", "B")]
        if length == 2:
            labels.append(("C", 1))
        matches = [label for label in labels if block(*label)[1] == local]
        assert len(matches) == 1, (length, local, matches)
        word.append(matches[0])
    return tuple(word)


def compose(word):
    width = 2 * sum(k for _, k in word)
    offset = 0
    pairs = []
    for label in word:
        length, matching = block(*label)
        for a, b in matching:
            ar, ac = divmod(a, length)
            br, bc = divmod(b, length)
            pairs.append((ar*width+ac+offset, br*width+bc+offset))
        offset += length
    return width, canonical(pairs)


def word_image(word, flip_rows, flip_cols):
    word = word[::-1] if flip_cols else word
    if flip_rows:
        swap = {"A": "B", "B": "A", "C": "C"}
        word = tuple((swap[kind], k) for kind, k in word)
    return word


def local_transitions():
    """直接把一个待补列放满，生成输出掩码；不使用正文的转移表。"""
    result = {}
    for incoming in range(8):
        outputs = []

        def visit(occupied, outgoing):
            if occupied == 7:
                outputs.append(outgoing)
                return
            row = next(r for r in range(3) if not occupied & (1 << r))
            visit(occupied | (1 << row), outgoing | (1 << row))
            if row < 2 and not occupied & (1 << (row+1)):
                visit(occupied | (1 << row) | (1 << (row+1)), outgoing)

        visit(incoming, 0)
        assert len(outputs) == len(set(outputs))
        result[incoming] = sorted(outputs)
    expected = {0:[1,4,7], 1:[0,6], 2:[5], 3:[4],
                4:[0,3], 5:[2], 6:[1], 7:[0]}
    assert result == expected
    return result


def coefficients(expr, variable, count):
    expansion = sp.series(expr, variable, 0, count).removeO().expand()
    values = [expansion.coeff(variable, i) for i in range(count)]
    assert all(v.is_Integer for v in values)
    return [int(v) for v in values]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0 <= args.max_n <= 8:
        parser.error("穷举检查限定 0 <= max-n <= 8")
    started = time.perf_counter()
    transitions = local_transitions()
    x, z = sp.symbols("x z")
    F = x + 2*x/(1-x)
    D = 1/(1-F)
    H = 1/(1-x)
    V = (1+F)/(1-F.subs(x, x**2))
    R = (1+x)/(1-F.subs(x, x**2))
    derived = (D+H+V+R)/4
    target = (-1+3*x+4*x**2-10*x**3+4*x**5-x**6) / (
        (x-1)*(x**2-4*x+1)*(x**4-4*x**2+1))
    assert sp.cancel(derived-target) == 0
    mathar_26 = (1/(1+z)+1/(1-z))/8 + (
        1+2*z**2-z**6)/(2*(1-4*z**4+z**8)) + (
        1-z**2)/(4*(1-4*z**2+z**4))
    assert sp.cancel(derived.subs(x, z**2)-mathar_26) == 0
    denominator = sp.expand((1-x)*(1-4*x+x**2)*(1-4*x**2+x**4))
    den_coeffs = [int(denominator.coeff(x, i)) for i in range(8)]
    assert den_coeffs == [1,-5,1,19,-19,-1,5,-1]
    expected_fixed = [coefficients(f, x, args.max_n+1) for f in (D,H,V,R)]
    expected_orbits = coefficients(target, x, args.max_n+1)
    known_prefix = [1,2,5,14,46,156,561,2037,7525]
    assert expected_orbits == known_prefix[:args.max_n+1]
    templates = [("C", 1)] + [(kind,k) for k in range(1,args.max_n+1)
                              for kind in ("A","B")]
    for label in templates:
        width, matching = block(*label)
        check_cover(matching, width)
        assert not cut_columns(matching, width)
        assert transform(matching, width, flip_cols=True) == matching
        assert transform(matching, width, flip_rows=True) == compose(
            word_image((label,), True, False))[1]

    rows = []
    primitive_seen = {k:set() for k in range(1,args.max_n+1)}
    for n in range(args.max_n+1):
        width = 2*n
        fixed = [0,0,0,0]
        orbits = set()
        words = set()
        total = 0
        for matching in historical.tilings(width):
            check_cover(matching, width)
            word = factor(matching, width)
            assert compose(word) == (width, matching)
            assert word not in words
            words.add(word)
            if n > 0 and len(word) == 1:
                primitive_seen[n].add(matching)
            images = []
            for i, (fr,fc) in enumerate(((False,False),(True,False),
                                         (False,True),(True,True))):
                actual = transform(matching, width, fr, fc)
                predicted = compose(word_image(word,fr,fc))[1]
                assert actual == predicted
                images.append(actual)
                fixed[i] += actual == matching
            orbits.add(min(images))
            total += 1
        assert fixed == [values[n] for values in expected_fixed]
        assert len(orbits) == expected_orbits[n]
        assert sum(fixed) == 4*len(orbits)
        rows.append({"n":n, "board":[3,width], "tilings_checked":total,
                     "fixed_counts_identity_rowflip_colflip_halfturn":fixed,
                     "orbit_count":len(orbits), "all_factorizations_rebuilt":True,
                     "all_four_word_actions_match_cell_actions":True})
    for k, found in primitive_seen.items():
        expected = {block("A",k)[1],block("B",k)[1]}
        if k == 1:
            expected.add(block("C",1)[1])
        assert found == expected

    history = json.loads(HISTORY.read_text(encoding="utf-8"))
    assert hashlib.sha256(ENUMERATOR.read_bytes()).hexdigest() == history["source_sha256"]
    for row, old in zip(rows, history["rows"]):
        assert row["fixed_counts_identity_rowflip_colflip_halfturn"] == old[
            "fixed_counts_identity_rowflip_colflip_halfturn"]
        assert row["orbit_count"] == old["orbits"]
    report = {
        "date_beijing":datetime.now(timezone(timedelta(hours=8))).isoformat(),
        "command":"python " + " ".join(sys.argv), "cwd":str(Path.cwd()),
        "python":sys.version, "platform":platform.platform(), "sympy":sp.__version__,
        "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "enumerator_path":str(ENUMERATOR.relative_to(ROOT)),
        "enumerator_sha256":hashlib.sha256(ENUMERATOR.read_bytes()).hexdigest(),
        "historical_report_sha256":hashlib.sha256(HISTORY.read_bytes()).hexdigest(),
        "random_seed":None, "range_n":[0,args.max_n], "rows":rows,
        "tilings_checked_total":sum(row["tilings_checked"] for row in rows),
        "primitive_counts_by_half_width":{str(k):len(v) for k,v in primitive_seen.items()},
        "transition_table_bit0_top_row":transitions,
        "symbolic_checks":{
            "derived_equals_oeis_rational_function":True,
            "derived_x_equals_mathar_eq26_after_x_z_squared":True,
            "denominator_coefficients_ascending":den_coeffs,
            "normalized_numerator":str(sp.Poly(sp.cancel(derived*denominator),x).as_expr()),
            "initial_values":expected_orbits,
            "method":"exact SymPy rational cancellation and polynomial expansion"},
        "matches_historical_report":True,
        "elapsed_seconds":time.perf_counter()-started,
        "limitations":[
            "铺法枚举复用历史脚本；不是两个独立穷举实现。",
            "本轮新执行逐个分解和四种对称作用检查；历史报告未覆盖这些检查。",
            "有限枚举只覆盖所列 n；一般结论依赖 proof.md 的组合论证。",
            "精确代数只验证输入表达式的恒等式，不验证其组合解释。",
            "未运行形式化证明，不检验文献新颖性。"],
    }
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"range":report["range_n"],"tilings_checked_total":report[
        "tilings_checked_total"],"orbit_counts":expected_orbits,"all_checks_passed":True,
        "elapsed_seconds":report["elapsed_seconds"]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
