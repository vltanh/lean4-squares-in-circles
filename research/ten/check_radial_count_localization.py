#!/usr/bin/env python3
"""Exact integer certificate of two radial counts, conditional on four inner centres."""
from array import array
from math import isqrt
from functools import lru_cache
from collections import Counter
import json
from pathlib import Path

D=20*2**15
D2=D*D
CASES=json.loads(Path(__file__).with_name('radial_count_certificate.json').read_text())
PRIMITIVES={}
for j in range(1,29):
    M=j*D//20
    lo=array('q',[0]);hi=array('q',[0]);previous=M
    for k in range(1,M+1):
        h=isqrt(M*M-k*k)
        lo.append(lo[-1]+h);hi.append(hi[-1]+previous+1);previous=h
    PRIMITIVES[M]=(lo,hi)
print('Integer primitive tables ready.',flush=True)

@lru_cache(maxsize=100000)
def rectangle_cdf(M,x,y):
    sign=(1 if x>=0 else -1)*(1 if y>=0 else -1)
    x=min(abs(x),M);y=min(abs(y),M)
    if x*x+y*y<=M*M:l=u=x*y
    else:
        lo,hi=PRIMITIVES[M]
        l=int(lo[x])+int(lo[y])-int(hi[M])
        u=int(hi[x])+int(hi[y])-int(lo[M])
    return (l,u) if sign>0 else (-u,-l)

@lru_cache(maxsize=100000)
def square_cdf(M,a,b):
    if b>a:return square_cdf(M,b,a)
    l=u=0
    for sx,sy,s in [(1,1,1),(-1,1,-1),(1,-1,-1),(-1,-1,1)]:
        ll,uu=rectangle_cdf(M,a+sx*(D//2),b+sy*(D//2))
        if s>0:l+=ll;u+=uu
        else:l-=uu;u-=ll
    return l,u

for case in CASES:
    weights=case['weights_per_thousand'];alpha,beta,gamma=case['targets_per_thousand']
    m=case['branch_count'];cut=case['cut_numerator']*D//case['cut_denominator']
    assert len(weights)==28 and all(w>=0 for w in weights)
    assert (alpha<=beta if m==1 else alpha>=beta)
    assert 22*sum(w*(2*j+1) for j,w in enumerate(weights)) < 7*400*(m*alpha+(4-m)*beta+6*gamma)
    jumps=[(j*D//20,weights[j-1]-(weights[j] if j<28 else 0)) for j in range(1,29)]
    jumps=[(M,c) for M,c in jumps if c]
    def score_lower(a0,a1,b0,b1):
        ans=0
        for M,c in jumps:
            ans+=c*(square_cdf(M,a1,b1)[0] if c>0 else square_cdf(M,a0,b0)[1])
        return ans
    counts=Counter();depths=Counter();stack=[(0,2*D,0,2*D,0)]
    while stack:
        a0,a1,b0,b1,depth=stack.pop()
        if b0>a1:counts['outside_symmetry_wedge']+=1;continue
        if 2*((a0+D//2)**2+(b0+D//2)**2)>9*D2:
            counts['outside_containing_disk']+=1;continue
        qlo=a0*a0+b0*b0;qhi=a1*a1+b1*b1
        targets=[]
        if qlo<=cut*cut:targets.append(alpha)
        if qhi>=cut*cut and qlo<=D2:targets.append(beta)
        if qhi>=D2:targets.append(gamma)
        target=max(targets)
        lower=score_lower(a0,a1,b0,b1)
        if lower>=target*D2:
            counts['certified']+=1;depths[depth]+=1;continue
        if depth>=18:
            raise AssertionError(('uncertified',case['cut_numerator'],m,a0,a1,b0,b1,lower,target*D2))
        am=(a0+a1)//2;bm=(b0+b1)//2
        assert 2*am==a0+a1 and 2*bm==b0+b1
        stack.extend([(a0,am,b0,bm,depth+1),(am,a1,b0,bm,depth+1),
                      (a0,am,bm,b1,depth+1),(am,a1,bm,b1,depth+1)])
    print('PASS cut',case['cut_numerator'],'/20 branch',m,dict(counts),'depths',dict(sorted(depths.items())),flush=True)
    square_cdf.cache_clear();rectangle_cdf.cache_clear()
print('All four exact certificates passed.',flush=True)
