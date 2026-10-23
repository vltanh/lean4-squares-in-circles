"""Exact fixed-point interval exclusion of the six axis-aligned cases."""
from itertools import combinations
from math import isqrt
from collections import Counter
import json
import argparse
from pathlib import Path

SCALE = 10**8
Q_NUM, Q_DEN = 49013, 10000
GRID = {(i,j) for i in (-1,0,1) for j in (-1,0,1)} | {(-2,0),(2,0),(0,-2),(0,2)}
HOLES = [((0,0),(1,1)),((0,0),(1,0)),((0,0),(2,0)),
         ((1,0),(0,1)),((1,0),(0,2)),((2,0),(0,2))]

def ceil_sqrt(n):
    if n < 0:
        raise ValueError('negative radicand')
    r = isqrt(n)
    return r if r*r == n else r+1

def problem(holes):
    cells=sorted(GRID-set(holes)); fixed=[]; choices=[]
    for i,j in combinations(range(11),2):
        a,b=cells[i],cells[j]; dx,dy=b[0]-a[0],b[1]-a[1]
        if abs(dx)>=2 or abs(dy)>=2:
            continue
        def edge(k,d):
            return (i*2+k,j*2+k) if d>0 else (j*2+k,i*2+k)
        if dx==0:
            fixed.append(edge(1,dy))
        elif dy==0:
            fixed.append(edge(0,dx))
        else:
            choices.append((edge(0,dx),edge(1,dy)))
    bounds=[[(2*k-1)*SCALE//2,(2*k+1)*SCALE//2] for p in cells for k in p]
    return cells,fixed,choices,bounds

def propagate(bounds,edges,choices):
    bounds=[p.copy() for p in bounds];edges=edges.copy();choices=choices.copy()
    for iteration in range(10000):
        changed=False
        for i in range(11):
            for coord,other in ((2*i,2*i+1),(2*i+1,2*i)):
                target=bounds[coord];op=bounds[other]
                amin=max(op[0],-op[1],0)
                radicand=Q_NUM*SCALE*SCALE//Q_DEN-(amin+SCALE//2)**2
                if radicand<0:
                    return {'closed':True,'reason':'disk-negative','square':i,'iteration':iteration,'radicand':radicand}
                h=ceil_sqrt(radicand)-SCALE//2
                lo=max(target[0],-h);hi=min(target[1],h)
                if lo>hi:
                    return {'closed':True,'reason':'disk-empty','coordinate':coord,'iteration':iteration,'lower':lo,'upper':hi}
                if lo>target[0] or hi<target[1]:changed=True
                target[:]=[lo,hi]
        for a,b in edges:
            lo=max(bounds[b][0],bounds[a][0]+SCALE)
            hi=min(bounds[a][1],bounds[b][1]-SCALE)
            if lo>bounds[b][1] or hi<bounds[a][0]:
                return {'closed':True,'reason':'edge-empty','edge':[a,b],'iteration':iteration,
                        'source_lower':bounds[a][0],'target_upper':bounds[b][1]}
            if lo>bounds[b][0] or hi<bounds[a][1]:changed=True
            bounds[b][0]=lo;bounds[a][1]=hi
        remaining=[]
        for e,f in choices:
            legal=[bounds[b][1]-bounds[a][0]>=SCALE for a,b in (e,f)]
            if not any(legal):
                return {'closed':True,'reason':'both-separators-empty','choice':[list(e),list(f)],'iteration':iteration,
                        'gaps':[bounds[b][1]-bounds[a][0] for a,b in (e,f)]}
            if all(legal):remaining.append((e,f))
            else:edges.append(e if legal[0] else f);changed=True
        choices=remaining
        if not changed:
            return {'closed':False,'bounds':bounds,'edges':edges,'choices':choices,'rounds':iteration+1}
    raise RuntimeError('Propagation iteration limit: no certificate claimed')

def search(bounds,edges,choices,stats):
    stats['nodes']+=1
    result=propagate(bounds,edges,choices)
    if result['closed']:
        stats['leaves']+=1
        return result
    bounds,edges,choices=result['bounds'],result['edges'],result['choices']
    if not choices:
        raise RuntimeError('Unresolved geometric leaf: no certificate claimed')
    choice=min(choices,key=lambda pair:sum(bounds[b][1]-bounds[a][0]-SCALE for a,b in pair))
    choices.remove(choice)
    return {'split':[list(e) for e in choice],
            'children':[search(bounds,edges+[edge],choices,stats) for edge in choice]}

def generate():
    cases=[]
    for holes in HOLES:
        cells,edges,choices,bounds=problem(holes)
        stats=Counter()
        tree=search(bounds,edges,choices,stats)
        cases.append({'holes':[list(p) for p in holes],'cells':[list(p) for p in cells],
                      'initial_binary_pairs':len(choices),'stats':dict(stats),'tree':tree})
    return {'schema':'eleven-axis-exclusion-v1','q_num':Q_NUM,'q_den':Q_DEN,'scale':SCALE,
            'scope':'No eleven axis-aligned unit squares pack q<=49013/10000.',
            'cases':cases}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', type=Path)
    parser.add_argument('--check', type=Path)
    args=parser.parse_args()
    data=generate()
    if args.check and json.loads(args.check.read_text()) != data:
        raise SystemExit('Stored exclusion tree differs from exact generation')
    for case in data['cases']:
        print(case['holes'],case['stats'])
    if args.write:
        args.write.write_text(json.dumps(data,indent=2)+'\n')
