#!/usr/bin/env python3
"""Independent dyadic-quadratic verification of every joint-angle table leaf.

Radius bounds come from integer bisection of r^2+w*r=4. Coverage is checked
by prefix-free paths and exact Kraft sums, separately from the primary
recursive verifier. There is no optimizer or floating-point arithmetic.
"""
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
from math import isqrt
import json

ROOT=Path(__file__).resolve().parent
SCALE=2**48

@lru_cache(maxsize=50000)
def rad(w):
    lo,hi=SCALE,2*SCALE
    def below(k):
        return k*k*w.denominator+k*SCALE*w.numerator<=4*SCALE*SCALE*w.denominator
    assert below(lo) and not below(hi)
    while hi-lo>1:
        mid=(lo+hi)//2
        if below(mid):lo=mid
        else:hi=mid
    assert below(lo) and not below(hi)
    return Q(lo,SCALE),Q(hi,SCALE)

def sc(t):return 2*t/(1+t*t),(1-t*t)/(1+t*t)
root2_lo=Q(isqrt(2*SCALE*SCALE),SCALE)
assert root2_lo**2<2<(root2_lo+Q(1,SCALE))**2

def endpoint(alpha,t,d):
    sb,cb=sc(t)
    if alpha is None:
        l,h=rad(abs(sb)+abs(cb));a=(h if sb>=0 else l)*sb-Q(1,2)
    else:
        sa,ca=sc(alpha);l,h=rad(abs(sa)+abs(ca))
        width=(abs(sb*ca+cb*sa)+abs(cb*ca-sb*sa))/2
        a=(h if sb>=0 else l)*sb-width
    sd,cd=sc(d)
    if t<=d:
        sn,cs=sd*cb-cd*sb,cd*cb+sd*sb
        assert sn>=0 and cs>0
        return a+rad(sn+cs)[1]*sn-Q(1,2)
    return a-root2_lo*(sb*cd-cb*sd)-Q(1,2)

meta=json.loads((ROOT/'loaded_joint_angle_certificate.json').read_text())
groups={}
for line in (ROOT/'loaded_joint_angle_leaves.tsv').read_text().splitlines():
    if not line or line.startswith('#'):continue
    i,side,task,seg,path,margin=line.split('\t')
    key=int(i),side,int(task),int(seg)
    groups.setdefault(key,[]).append(('' if path=='-' else path,int(margin)))
expected=set();checked=0
for row in meta['rows']:
    i=row['i'];ta,tb=Q(i,800),Q(i+1,800)
    good,bad=Q(row['good']),Q(row['bad'])
    tg,tb_gap=2*good/(1-good*good),2*bad/(1-bad*bad)
    assert 45*(1-tg*tb_gap)<tg+tb_gap
    own=0
    for side,d in [('G',good),('B',bad)]:
        al,ah=(-tb,-ta) if side=='G' else (ta,tb)
        domains=[(al,Q(-2,7),Q(1)),(ah,Q(-2,7),Q(1))]
        for l,h in [(-ah,-al),((1-ah)/(1+ah),(1-al)/(1+al))]:
            l,h=max(l,Q(-2,7)),min(h,Q(1))
            if l<h:domains.append((None,l,h))
        for task,(alpha,l,h) in enumerate(domains):
            cuts={l,h}
            possible=[Q(0),d]
            if alpha is not None:possible += [-alpha,(1-alpha)/(1+alpha)]
            cuts.update(x for x in possible if l<x<h);cuts=sorted(cuts)
            for seg,(a,b) in enumerate(zip(cuts,cuts[1:])):
                key=i,side,task,seg;expected.add(key);rows=groups[key]
                paths=sorted(path for path,_ in rows)
                assert len(paths)==len(set(paths))
                assert all(not y.startswith(x) for x,y in zip(paths,paths[1:]))
                assert sum((Q(1,2**len(p)) for p in paths),Q(0))==1
                for path,margin in rows:
                    lo,hi=a,b
                    for bit in path:
                        mid=(lo+hi)/2
                        if bit=='0':hi=mid
                        elif bit=='1':lo=mid
                        else:raise AssertionError('Invalid path')
                    bound=max(endpoint(alpha,lo,d),endpoint(alpha,hi,d))+4*(hi-lo)**2
                    assert margin>0 and bound+Q(margin,10**9)<=0
                    checked+=1;own+=1
    assert own==row['leaves']
assert expected==set(groups)
assert checked==meta['leaf_count']==28000
print('PASS: all28000 leaf inequalities by dyadic quadratic bisection; independent prefix/Kraft coverage; all332 angle sums.')
