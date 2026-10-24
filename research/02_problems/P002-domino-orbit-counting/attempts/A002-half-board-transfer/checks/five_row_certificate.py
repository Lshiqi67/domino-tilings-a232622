"""五行公式的六维精确证书，可直接乘矩阵逐项核查。"""
import hashlib
import json
import sys
from pathlib import Path
from datetime import datetime, timedelta, timezone
import sympy as sp
from transfer_core import transitions, reverse_mask

t,x=sp.symbols('t x')
T=transitions(5)
seen={0}; pending=[0]
while pending:
    p=pending.pop()
    for q in T[p]:
        if q not in seen: seen.add(q); pending.append(q)
orbits=[]; remaining=set(seen)
while remaining:
    p=min(remaining); orbit=sorted({p,reverse_mask(p,5)})
    orbits.append(orbit); remaining.difference_update(orbit)
E=[o for o in orbits if o[0].bit_count()%2==0]
O=[o for o in orbits if o[0].bit_count()%2==1]
B=sp.Matrix([[sum(int(target[0] in T[p]) for p in source) for source in E] for target in O])
C=sp.Matrix([[sum(int(target[0] in T[p]) for p in source) for source in O] for target in E])
M=C*B
e0=sp.eye(6)[:,0]
f=((sp.eye(6)-t*M).inv(method='DM')*e0).applyfunc(sp.cancel)
assert all(sp.cancel(v)==0 for v in (sp.eye(6)-t*M)*f-e0)
ve=sp.Matrix([[len(o) for o in E]])
re=sp.Matrix([[int(len(o)==1) for o in E]])
vo=sp.Matrix([[len(o) for o in O]])*B
ro=sp.Matrix([[int(len(o)==1) for o in O]])*B
derived={'D':f[0].subs(t,x),'V':((ve+x*vo)*f.subs(t,x*x))[0],
         'R':((re+x*ro)*f.subs(t,x*x))[0]}
full=json.loads(Path(__file__).with_name('symbolic-report.json').read_text(encoding='utf-8'))
five=next(row for row in full['results'] if row['height']==5)
for name,expr in derived.items():
    assert sp.cancel(expr-sp.sympify(five['functions'][name]['expression']))==0
report={'date_beijing':datetime.now(timezone(timedelta(hours=8))).isoformat(),
        'command':'python '+' '.join(sys.argv),'python':sys.version,'sympy':sp.__version__,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'core_sha256':hashlib.sha256(Path(__file__).with_name('transfer_core.py').read_bytes()).hexdigest(),
        'random_seed':None,'even_state_orbits':E,'odd_state_orbits':O,
        'B':B.tolist(),'C':C.tolist(),'M':M.tolist(),
        'solution_column':[str(v) for v in f],
        'even_vertical_reflection_terminal':list(ve),'odd_vertical_reflection_terminal':list(vo),
        'even_halfturn_terminal':list(re),'odd_halfturn_terminal':list(ro),
        'exact_residual_zero':True,'agrees_with_full_matrix':True}
# SymPy 整数在 JSON 中转为 Python 整数；表达式已转字符串。
Path(__file__).with_name('five-row-certificate.json').write_text(
    json.dumps(report,ensure_ascii=False,indent=2,default=int)+'\n',encoding='utf-8')
print(json.dumps({'solution_column':report['solution_column'],'all_checks_passed':True},ensure_ascii=False))
