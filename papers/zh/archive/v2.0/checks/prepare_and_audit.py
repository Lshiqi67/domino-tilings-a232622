"""Audit the Chinese manuscript and generate its coefficient table without modifying historical reports."""
from pathlib import Path
import datetime
import hashlib
import json
import platform
import re
import sys

import sympy as sp
from sympy.parsing.sympy_parser import (
    parse_expr, standard_transformations, implicit_multiplication_application,
)

PAPER = Path(__file__).resolve().parents[1]
PROBLEM = PAPER.parents[1] / 'research/02_problems/P002-domino-orbit-counting'
CHECKS = PROBLEM / "attempts/A002-half-board-transfer/checks"
x, t = sp.symbols("x t")


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def polynomial(source, symbol=x):
    value = source.replace("^", "**").replace(" ", "")
    assert re.fullmatch(r"[0-9x+\-*()]+", value), value
    return parse_expr(
        value,
        local_dict={"x": symbol},
        transformations=standard_transformations + (implicit_multiplication_application,),
    )


def matrix_blocks(source):
    return [
        sp.Matrix([[int(n.strip()) for n in row.strip().split("&")]
                   for row in block.strip().split(r"\\")])
        for block in re.findall(r"\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}",
                                source, flags=re.S)
        if re.fullmatch(r"[0-9&\\\s+\-]+", block)
    ]


def coefficients(num, den, count):
    values = []
    for n in range(count):
        rhs = num[n] if n < len(num) else 0
        rhs -= sum(den[j] * values[n-j]
                   for j in range(1, min(n, len(den)-1)+1))
        assert den[0] == 1
        values.append(rhs)
    return values


def main():
    symbolic = read_json(CHECKS / "symbolic-report.json")
    certificate = read_json(CHECKS / "five-row-certificate.json")
    for name, digest in symbolic["source_hashes"].items():
        assert sha(CHECKS / name) == digest, name
    assert sha(CHECKS / "five_row_certificate.py") == certificate["source_sha256"]
    assert sha(CHECKS / "transfer_core.py") == certificate["core_sha256"]

    five_text = (PAPER / "sections/five-row.tex").read_text(encoding="utf-8")
    cert_text = (PAPER / "sections/certificate.tex").read_text(encoding="utf-8")
    M = matrix_blocks(five_text)[0]
    B, C = matrix_blocks(cert_text)
    assert M == sp.Matrix(certificate["M"])
    assert B == sp.Matrix(certificate["B"])
    assert C == sp.Matrix(certificate["C"])
    assert M == C * B

    ns = {}
    for index, raw in re.findall(r"n_([0-3])=\(([^)]*)\)\^\{\\trans\}", cert_text):
        ns[int(index)] = sp.Matrix([int(v) for v in raw.split(",")])
    assert len(ns) == 4
    N = sum((ns[j]*t**j for j in range(4)), sp.zeros(6, 1))
    raw_N = re.search(r"N\(t\)&?=\\bigl\((.*?)\\bigr\)\^\{\\trans\}", five_text, re.S)
    assert raw_N
    printed_N = sp.Matrix([polynomial(row.strip().replace("t", "x"), t)
                           for row in raw_N[1].replace(r"\ ", " ").strip().split(",")])
    assert all(sp.expand(v) == 0 for v in printed_N-N)
    P = 1-15*t+32*t**2-15*t**3+t**4
    e = sp.eye(6)[:, 0]
    assert (sp.eye(6)-t*M)*N-P*e == sp.zeros(6, 1) or all(
        sp.expand(v) == 0 for v in (sp.eye(6)-t*M)*N-P*e
    )
    assert all(sp.cancel(N[i]/P - sp.sympify(certificate["solution_column"][i])) == 0
               for i in range(6))

    terminals = {}
    for kind, parity, raw in re.findall(
            r"w_\{([vr]),([eo])\}&?=\(([^)]*)\)", five_text):
        terminals[kind+parity] = sp.Matrix([[int(v) for v in raw.split(",")]])
    assert len(terminals) == 4
    mapping = {
        "ve": "even_vertical_reflection_terminal",
        "vo": "odd_vertical_reflection_terminal",
        "re": "even_halfturn_terminal",
        "ro": "odd_halfturn_terminal",
    }
    for key, report_key in mapping.items():
        assert list(terminals[key]) == certificate[report_key]
    f = N / P
    computed = {
        "D": f[0].subs(t, x),
        "H": (1-x)/(1-3*x+x*x),
        "V": ((terminals["ve"]+x*terminals["vo"])*f.subs(t, x*x))[0],
        "R": ((terminals["re"]+x*terminals["ro"])*f.subs(t, x*x))[0],
    }
    five = next(r for r in symbolic["results"] if r["height"] == 5)
    parsed = {}
    for kind, num, den in re.findall(
            r"([DHVR])_5\(x\)&=\\frac\{([^{}]+)\}\{([^{}]+)\}", five_text):
        denominator = P.subs(t, x*x if den == "P(x^2)" else x) if den.startswith("P(") else polynomial(den)
        parsed[kind] = polynomial(num) / denominator
    assert set(parsed) == set(computed)
    for kind in parsed:
        assert sp.cancel(parsed[kind]-computed[kind]) == 0, kind
        assert sp.cancel(parsed[kind]-sp.sympify(five["functions"][kind]["expression"])) == 0
    A5 = sp.cancel(sum(parsed.values())/4)
    assert sp.cancel(A5-sp.sympify(five["functions"]["A"]["expression"])) == 0

    intro = (PAPER / "sections/introduction.tex").read_text(encoding="utf-8")
    main_match = re.search(r"=\\frac\{(1-3x[^{}]+)\}\s*\{([^{}]+)\}", intro)
    assert main_match
    A3 = polynomial(main_match[1])/polynomial(main_match[2])
    three = next(r for r in symbolic["results"] if r["height"] == 3)
    assert sp.cancel(A3-sp.sympify(three["functions"]["A"]["expression"])) == 0

    data = five["functions"]["A"]
    num, den = data["numerator_ascending"], data["denominator_ascending"]
    values = coefficients(num, den, 101)
    assert values[:13] == five["orbit_prefix_n0_to12"]
    sys.path.insert(0, str(CHECKS))
    from transfer_core import fixed_counts
    for n in range(101):
        result = fixed_counts(5, n)
        # fixed_counts returns the four fixed-point counts [e, h, v, rho].
        assert sum(result) % 4 == 0
        assert values[n] == sum(result)//4

    lines = [
        r"\begin{table}[htbp]", r"\centering",
        r"\caption{五行通分多项式的系数及初值；$b_{14}=0$。}\label{tab:five-coeff}",
        r"\begin{tabular}{rrrr}", r"\toprule",
        r"$j$ & $b_j$ & $q_j$ & $a_5(j)$\\", r"\midrule",
    ]
    for j in range(15):
        b = num[j] if j < len(num) else 0
        val = str(values[j]) if j < 14 else r"\text{由递推得}"
        lines.append(f"{j} & {b} & {den[j]} & {val}" + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}"]
    (PAPER / "generated").mkdir(exist_ok=True)
    (PAPER / "generated/five-table.tex").write_text("\n".join(lines)+"\n", encoding="utf-8")

    report = {
        "date_beijing": datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=8))).isoformat(),
        "command": "python papers/zh/checks/prepare_and_audit.py (from the repository root)",
        "python": sys.version, "sympy": sp.__version__, "platform": platform.platform(),
        "random_seed": None,
        "checks": {
            "original_source_hashes_match": True,
            "manuscript_M_B_C_match_original_certificate": True,
            "manuscript_coefficient_vector_certificate_exact": True,
            "terminal_vectors_match": True,
            "four_five_row_functions_in_manuscript_exact": True,
            "main_three_row_formula_exact": True,
            "five_row_coefficients_vs_integer_matrix_n0_to100": True,
        },
        "a5_initial_14": values[:14],
        "source_sha256": {str(p.relative_to(PAPER)).replace("\\", "/"): sha(p)
                          for p in sorted(PAPER.rglob("*.tex")) if "archive" not in p.parts},
        "script_sha256": sha(Path(__file__)),
        "limits": "Checks manuscript transcription and exact algebra, not exhaustive tiling enumeration, independent review, or bibliographic priority.",
    }
    (PAPER / "checks/manuscript-audit.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "a5_initial_14": values[:14]}, ensure_ascii=False))


if __name__ == "__main__":
    main()
