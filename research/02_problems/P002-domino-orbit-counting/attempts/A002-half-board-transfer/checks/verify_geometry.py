"""新写格点精确覆盖枚举器，交叉检查半棋盘公式；不导入 A001 枚举器。"""

import hashlib
import json
import platform
import sys
import time
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path

from transfer_core import (fixed_counts, profiles, reverse_mask,
                           three_row_closed_counts, three_row_orbit_types)


def canonical(edges):
    return tuple(sorted(tuple(sorted(edge)) for edge in edges))


def matchings(height,width):
    """列优先编号；每步选剩余可用邻居最少的格子，枚举其配对。"""
    count = height*width
    neighbors = []
    for cell in range(count):
        col,row = divmod(cell,height)
        adjacent = []
        if row: adjacent.append(cell-1)
        if row+1<height: adjacent.append(cell+1)
        if col: adjacent.append(cell-height)
        if col+1<width: adjacent.append(cell+height)
        neighbors.append(sum(1<<j for j in adjacent))

    def visit(remaining,edges):
        if not remaining:
            yield canonical(edges)
            return
        selected,available,best = None,None,5
        pending = remaining
        while pending:
            bit = pending & -pending
            cell = bit.bit_length()-1
            choices = neighbors[cell] & remaining
            degree = choices.bit_count()
            if degree==0:
                return
            if degree<best:
                selected,available,best = cell,choices,degree
            pending ^= bit
        while available:
            bit = available & -available
            other = bit.bit_length()-1
            yield from visit(remaining ^ (1<<selected) ^ bit,edges+((selected,other),))
            available ^= bit

    yield from visit((1<<count)-1,())


def inspect(height,n):
    width = 2*n
    maps = []
    for fr,fc in ((False,False),(True,False),(False,True),(True,True)):
        maps.append(tuple((width-1-c if fc else c)*height+(height-1-r if fr else r)
                          for c in range(width) for r in range(height)))
    fixed = [0]*4
    orbit_stabilizers = {}
    half_keys = {2:set(),3:set()}
    profiles_seen = {2:[0]*(1<<height),3:[0]*(1<<height)}
    total = 0
    for matching in matchings(height,width):
        total += 1
        images = [canonical((mapping[a],mapping[b]) for a,b in matching) for mapping in maps]
        is_fixed = [image==matching for image in images]
        for index in range(4): fixed[index] += is_fixed[index]
        stab = sum((1<<j) for j,value in enumerate(is_fixed) if value)
        assert stab in {1,3,5,9,15}
        representative = min(images)
        if representative in orbit_stabilizers:
            assert orbit_stabilizers[representative]==stab
        orbit_stabilizers[representative] = stab
        for index in (2,3):
            if not is_fixed[index]: continue
            internal = tuple((a,b) for a,b in matching if a//height<n and b//height<n)
            crossing = [(a,b) for a,b in matching if a//height<n<=b//height]
            stub = 0
            for a,b in crossing:
                assert b-a==height and a//height==n-1
                stub |= 1<<(a%height)
            key = (internal,stub)
            assert key not in half_keys[index]
            half_keys[index].add(key)
            profiles_seen[index][stub] += 1
            mirrored = [(maps[index][a],maps[index][b]) for a,b in internal]
            center = [(height*(n-1)+r,height*n+r) for r in range(height) if stub&(1<<r)]
            assert canonical(list(internal)+mirrored+center)==matching
            if index==3: assert reverse_mask(stub,height)==stub
    predicted = fixed_counts(height,n)
    assert fixed==predicted,(height,n,fixed,predicted)
    q = profiles(height,n)
    assert profiles_seen[2]==list(q)
    assert profiles_seen[3]==[value if reverse_mask(s,height)==s else 0 for s,value in enumerate(q)]
    assert sum(fixed)==4*len(orbit_stabilizers)
    labels = {1:"trivial",3:"rowflip_only",5:"colflip_only",9:"halfturn_only",15:"full_group"}
    counts = Counter(labels[value] for value in orbit_stabilizers.values())
    types = {label:counts[label] for label in labels.values()}
    if height==3:
        assert fixed==three_row_closed_counts(n)
        assert types==three_row_orbit_types(n)
    return {"height":height,"n":n,"board":[height,width],"ordinary":total,
            "fixed_counts_identity_rowflip_colflip_halfturn":fixed,
            "orbits":len(orbit_stabilizers),"orbit_types":types,
            "half_board_profile_bijections_checked":True}


def main():
    start=time.perf_counter()
    cases={1:8,3:8,5:4,7:2}
    rows=[inspect(m,n) for m,limit in cases.items() for n in range(limit+1)]
    for n in range(101):
        assert fixed_counts(3,n)==three_row_closed_counts(n)
        assert sum(three_row_orbit_types(n).values())==sum(fixed_counts(3,n))//4
    root=Path(__file__).resolve().parents[5]
    old=root/'02_problems/P002-domino-orbit-counting/attempts/A001-irreducible-blocks/checks/report.json'
    history=json.loads(old.read_text(encoding='utf-8'))
    for row,prior in zip([r for r in rows if r['height']==3],history['rows']):
        assert row['ordinary']==prior['tilings_checked']
        assert row['orbits']==prior['orbit_count']
        assert row['fixed_counts_identity_rowflip_colflip_halfturn']==prior[
            'fixed_counts_identity_rowflip_colflip_halfturn']
    files=[Path(__file__),Path(__file__).with_name('transfer_core.py')]
    report={"date_beijing":datetime.now(timezone(timedelta(hours=8))).isoformat(),
            "command":"python "+" ".join(sys.argv),"cwd":str(Path.cwd()),
            "python":sys.version,"platform":platform.platform(),"random_seed":None,
            "source_hashes":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
            "exhaustive_ranges_max_n_by_height":cases,"rows":rows,
            "ordinary_tilings_enumerated_total":sum(r['ordinary'] for r in rows),
            "three_row_matrix_vs_closed_forms_n":[0,100],
            "historical_comparison_report_sha256":hashlib.sha256(old.read_bytes()).hexdigest(),
            "independent_enumerator":"new column-major minimum-remaining-degree grid matching recursion; no imports from A001",
            "elapsed_seconds":time.perf_counter()-start,
            "limitations":["完全枚举仅覆盖列出的棋盘；n<=100 的比较是公式/矩阵计算，不是全铺法枚举。",
                           "新枚举器与旧代码实现不同，但仍由同一研究助手编写，非独立作者审稿。",
                           "任意奇数高度定理依赖 proof.md 的一般双射；未作形式化或新颖性验证。"]}
    Path(__file__).with_name('geometry-report.json').write_text(
        json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({"ranges":cases,"tilings_enumerated":report['ordinary_tilings_enumerated_total'],
                      "all_checks_passed":True,"elapsed_seconds":report['elapsed_seconds']},ensure_ascii=False))
    print(json.dumps([r for r in rows if r['height']==3],ensure_ascii=False))


if __name__=='__main__': main()
