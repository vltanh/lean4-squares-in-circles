#!/usr/bin/env python3
"""Finite exact regressions, not a universal packing proof or Lean check."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, platform, random


def blocks(n: int, edges: list[tuple[int,int]]) -> tuple[list[set[int]],bool]:
    adj=[[] for _ in range(n)]
    for u,v in edges:
        adj[u].append(v); adj[v].append(u)
    tin={}; low={}; stack=[]; result=[]; clock=0
    def dfs(v: int, parent: int) -> None:
        nonlocal clock
        tin[v]=low[v]=clock; clock+=1
        for w in adj[v]:
            if w==parent:
                continue
            if w not in tin:
                stack.append((v,w)); dfs(w,v); low[v]=min(low[v],low[w])
                if low[w]>=tin[v]:
                    members=set()
                    while True:
                        edge=stack.pop(); members.update(edge)
                        if edge==(v,w):
                            break
                    result.append(members)
            elif tin[w]<tin[v]:
                stack.append((v,w)); low[v]=min(low[v],tin[w])
    dfs(0,-1)
    return result,len(tin)==n


def make_cells() -> list[dict]:
    cells=[]
    for m in range(1,5):
        for ks in combinations_with_replacement(range(3,10),m):
            reserve=sum(k-1 for k in ks)
            if reserve>8:
                continue
            for b in range(9-reserve):
                n=1+b+reserve
                closed=(ks==(3,) and b==0)
                cells.append({"id":f"C{m}."+"".join(map(str,ks))+f".b{b}",
                              "cyclic_block_sizes":list(ks),"bridges":b,
                              "component_bodies":n,"other_physical_squares":9-n,
                              "sharp_status":"CLOSED_HAND_IN_WINDOW" if closed else "OPEN"})
    assert len(cells)==58
    assert len({tuple(c['cyclic_block_sizes']) for c in cells})==21
    assert sum(c['sharp_status'].startswith('CLOSED') for c in cells)==1
    return cells


def qcap_checks() -> dict:
    identities=0; squares=0; tilted=0; boundary=0
    for j in range(21):
        r=F(j,50); a=(1-r*r)/(1+r*r); b=2*r/(1+r*r)
        assert a>=b>=0 and a*a+b*b==1
        w=a+b; d=a-b; h=w/2
        assert w-w*w/2==F(1,2)-(w-1)**2/2; identities+=1
        assert (h+b*(d+F(1,2)))/a==F(1,2)+b+a*b/(1+b); identities+=1
        assert a*a*(1+2*b)**2-(1+b)**2==2*b*(1+b)*(1-2*b*b); identities+=1
        assert a*(1+2*b)>=1+b; identities+=1
        if b:
            assert (h-a*(d-F(1,2)))/b==F(3,2)+b*(a-b)/(1+a); identities+=1
        for ix in range(21):
            for iy in range(21):
                x=h+F(ix,20); y=h+F(iy,20)
                t=a*x+b*y; z=-b*x+a*y
                radius=(t+F(1,2))**2+(abs(z)+F(1,2))**2
                if radius>F(17,4):
                    continue
                margins=(F(1,2)-abs(w-t),F(1,2)-abs(d-z))
                assert min(margins)>=0
                if b:
                    assert min(margins)>0; tilted+=1
                    eps=min(margins)/(4*w)
                else:
                    eps=min(F(3,2)-x,F(3,2)-y,F(1,4))/2
                    boundary+=int(min(margins)==0)
                assert eps>0
                px=py=1-eps
                assert abs(a*px+b*py-t)<F(1,2)
                assert abs(-b*px+a*py-z)<F(1,2)
                squares+=1
    # A rotated square and two disjoint quadrant squares above the theorem radius.
    a,b=F(4,5),F(3,5); x=y=F(7,10)
    t=a*x+b*y; z=-b*x+a*y
    assert (t+F(1,2))**2+(abs(z)+F(1,2))**2<=F(17,4)
    assert abs(a+b-t)<F(1,2) and abs(a-b-z)<F(1,2)
    assert (F(3,2)+F(1,2))**2+(F(1,2)+F(1,2))**2==5
    # False 45-degree center-angle bound: two touching aligned squares.
    x=F(5,4); y=F(1,2)
    assert (x+F(1,2))**2+(y+F(1,2))**2==F(65,16)<F(17,4)
    cosine=(x*x-y*y)/(x*x+y*y)
    assert cosine==F(21,29) and 2*cosine*cosine>1
    return {"exact_identity_checks":identities,"admissible_quadrant_square_samples":squares,
            "tilted_samples_with_strict_point_containment":tilted,
            "axis_aligned_boundary_samples":boundary,
            "negative_control_two_quadrant_squares_at_q":5,
            "negative_control_45_degree_bound":{"centers":[["5/4","1/2"],["5/4","-1/2"]],
                "q":"65/16","angle_cosine":"21/29","angle_strictly_below_45_degrees":True}}


def test_graphs(cells: list[dict]) -> dict:
    allowed={(tuple(c['cyclic_block_sizes']),c['bridges']):c['component_bodies'] for c in cells}
    count=0; seen=set(); rng=random.Random(20261023)
    def check(n: int, ed: list[tuple[int,int]]) -> None:
        nonlocal count
        bs,connected=blocks(n,ed)
        if not connected or len(ed)<n:
            return
        ks=tuple(sorted(len(b) for b in bs if len(b)>=3))
        bridge=sum(len(b)==2 for b in bs)
        assert ks and n==1+bridge+sum(k-1 for k in ks)
        assert allowed[(ks,bridge)]==n
        seen.add((ks,bridge)); count+=1
    for n in range(3,6):
        pairs=list(combinations(range(n),2))
        for mask in range(1<<len(pairs)):
            check(n,[e for i,e in enumerate(pairs) if (mask>>i)&1])
    for n in range(6,10):
        pairs=list(combinations(range(n),2))
        for trial in range(400):
            numerator=2+(trial%6)
            check(n,[e for e in pairs if rng.randrange(10)<numerator])
    # Every integer cell has at least one abstract graph witness: cliques sharing
    # a single articulation, followed by a bridge path. No physical feasibility claim.
    for cell in cells:
        ed=[]; next_vertex=1
        for size in cell['cyclic_block_sizes']:
            vs=[0]+list(range(next_vertex,next_vertex+size-1)); next_vertex+=size-1
            ed.extend(combinations(vs,2))
        last=0
        for _ in range(cell['bridges']):
            ed.append((last,next_vertex)); last=next_vertex; next_vertex+=1
        assert next_vertex==cell['component_bodies']
        check(next_vertex,list(ed))
    assert len(seen)==58
    assert F(625,162)<F(6241,1600)
    return {"finite_connected_cyclic_graph_checks":count,"distinct_cells_exercised":len(seen),
            "method":"All simple graphs through five vertices; deterministic samples above five; one abstract witness per cell. Not a universal proof or physical feasibility test."}


def p_center_relaxation() -> dict:
    roots=[(F(-3,2),F(0)),(F(-1,2),F(-193,1000)),(F(1,2),F(186,1000)),(F(3,2),F(0))]
    cs=[(F(x,1000),F(y,1000)) for x,y in [(887,1204),(-128,1353),(-1094,1003),(-552,-1212),(555,-1189)]]
    radial=[F(9,4)-x*x-y*y for x,y in cs]
    clearance=[]
    for x,y in cs:
        for a,b in roots:
            dx=max(abs(x-a)-F(1,2),F(0)); dy=max(abs(y-b)-F(1,2),F(0))
            clearance.append(dx*dx+dy*dy-F(1,4))
    separation=[(x-u)**2+(y-v)**2-1 for (x,y),(u,v) in combinations(cs,2)]
    assert min(radial)>0 and min(clearance)>0 and min(separation)>0
    return {"root_sliders":["-193/1000","186/1000"],
            "extra_centers":[[str(x),str(y)] for x,y in cs],
            "min_center_radius_squared_slack":str(min(radial)),
            "min_obstacle_distance_squared_slack":str(min(clearance)),
            "min_pair_distance_squared_slack":str(min(separation)),
            "scope":"Exact feasible center/inscribed-disk relaxation for P plus five. NOT a physical unit-square packing. Full square supports are essential."}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit',default='LOCAL_UNCOMMITTED')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=datetime.now(timezone.utc).isoformat()
    cells=make_cells(); q=qcap_checks(); graph=test_graphs(cells); relaxation=p_center_relaxation()
    raw=Path(__file__).read_bytes()
    result={"status":"PASS","started_utc":start,"finished_utc":datetime.now(timezone.utc).isoformat(),
            "python":platform.python_version(),"source_commit":args.source_commit,
            "source_sha256":hashlib.sha256(raw).hexdigest(),
            "source_git_blob_sha1":hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
            "quadrant":q,"cyclic_inventory":{"profiles":21,"cells":58,"closed_cells":1,"open_cells":57,**graph},
            "P_center_relaxation_negative_control":relaxation,
            "scope":"Finite exact checks only. No universal n=9 proof, full audit, Lean compilation or CI."}
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__':
    main()
