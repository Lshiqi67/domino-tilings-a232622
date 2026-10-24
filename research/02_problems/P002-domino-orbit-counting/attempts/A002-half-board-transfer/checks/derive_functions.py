"""从有限矩阵求精确有理函数，并输出可复核的线性方程证书。"""

import hashlib
import json
import platform
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

import sympy as sp

from transfer_core import fixed_counts, profiles, reverse_mask, transitions

x = sp.symbols("x")


def matrix(height):
    table = transitions(height)
    return sp.Matrix(len(table), len(table), lambda p,q: int(q in table[p]))


def reachable(M):
    seen = {0}
    todo = [0]
    while todo:
        p = todo.pop()
        for q in range(M.cols):
            if M[p,q] and q not in seen:
                seen.add(q)
                todo.append(q)
    return sorted(seen)


def resolvent_row(M):
    states = reachable(M)
    reduced = M.extract(states,states)
    K = sp.eye(len(states))-x*reduced
    row = K.inv(method="DM")[0,:]
    row = row.applyfunc(sp.cancel)
    residual = row*K-sp.eye(len(states))[0,:]
    assert all(sp.cancel(value) == 0 for value in residual)
    cert = {"states":states,"matrix":[[int(v) for v in reduced.row(j)]
                                      for j in range(reduced.rows)],
            "resolvent_row":[str(v) for v in row],
            "identity_checked":"row * (I-x*M) = e0", "all_residuals_zero":True}
    return states,row,cert


def describe(expr):
    expr = sp.cancel(expr)
    num,den = sp.fraction(expr)
    norm = den.subs(x,0)
    num,den = sp.Poly(num/norm,x),sp.Poly(den/norm,x)
    assert all(v.is_Integer for v in num.all_coeffs()+den.all_coeffs())
    return {"expression":str(expr),"latex":sp.latex(expr),
            "numerator_ascending":[int(num.nth(i)) for i in range(num.degree()+1)],
            "denominator_ascending":[int(den.nth(i)) for i in range(den.degree()+1)],
            "denominator_factored":str(sp.factor(den.as_expr()))}


def coeffs(record,count):
    numerator = record["numerator_ascending"]
    denominator = record["denominator_ascending"]
    values = []
    for n in range(count):
        values.append((numerator[n] if n<len(numerator) else 0)-sum(
            denominator[j]*values[n-j] for j in range(1,min(n+1,len(denominator)))))
    return values


def derive(height):
    T = matrix(height)
    even_states,even_row,even_cert = resolvent_row(T*T)
    states,row,half_cert = resolvent_row(T)
    small = matrix(height//2)
    _,hrow,hcert = resolvent_row(small*small)
    D,H = even_row[0],hrow[0]
    V = sum(row)
    R = sum(row[j] for j,s in enumerate(states) if reverse_mask(s,height)==s)
    A = sp.cancel((D+H+V+R)/4)
    functions = {name:describe(value) for name,value in zip("DHVRA",(D,H,V,R,A))}
    for name,index in zip("DHVR",range(4)):
        assert coeffs(functions[name],101) == [fixed_counts(height,n)[index] for n in range(101)]
    assert coeffs(functions["A"],101) == [sum(fixed_counts(height,n))//4 for n in range(101)]
    if height == 3:
        target = (-1+3*x+4*x**2-10*x**3+4*x**5-x**6)/(
            (x-1)*(x*x-4*x+1)*(x**4-4*x*x+1))
        assert sp.cancel(A-target)==0
    return {"height":height,"functions":functions,
            "certificates":{"ordinary":even_cert,"half_board":half_cert,"rowflip":hcert},
            "coefficient_checks_n":[0,100],
            "orbit_prefix_n0_to12":coeffs(functions["A"],13)}


def main():
    start = time.perf_counter()
    data = [derive(m) for m in [3,5]]
    # 文献表 12 第二列，列数 2,4,...,10；只作事后比较，不参与推导。
    assert data[1]["orbit_prefix_n0_to12"][:6] == [1,5,33,329,3818,46878]
    files = [Path(__file__),Path(__file__).with_name("transfer_core.py")]
    report = {"date_beijing":datetime.now(timezone(timedelta(hours=8))).isoformat(),
              "command":"python "+" ".join(sys.argv),"cwd":str(Path.cwd()),
              "python":sys.version,"sympy":sp.__version__,"platform":platform.platform(),
              "source_hashes":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
              "random_seed":None,"results":data,"elapsed_seconds":time.perf_counter()-start,
              "limitations":"精确矩阵证书核验输入模型的有理式；一般组合双射另在 proof.md 证明。并未以数列拟合公式；不核验新颖性。"}
    Path(__file__).with_name("symbolic-report.json").write_text(
        json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    for row in data:
        print(json.dumps({"height":row["height"],"functions":row["functions"],
                          "orbit_prefix":row["orbit_prefix_n0_to12"]},ensure_ascii=False))
    print(json.dumps({"elapsed_seconds":report["elapsed_seconds"],"all_checks_passed":True}))


if __name__ == "__main__":
    main()
