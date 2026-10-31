"""Exact integer certificate for NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md.

The geometric normalization and the three analytic reductions are proved in
that manuscript. Every arithmetic acceptance decision below uses integers.
Run directly with Python 3; there are no nonstandard dependencies.
Status: accepted after two independent full-source and arithmetic reviews;
see the manuscript and NINE_RADIUS_TWO_MEASURE_INDEPENDENT_CHECK.py.
"""
from functools import lru_cache
from math import isqrt, gcd
from collections import Counter
import hashlib
import json

Q=1<<56
B=5*(1<<24)
WEIGHTS=((1,10,714),(1,1,3858),(11,10,2424),(27,20,1709))
ATOM=292

def up(n,d):
    return -((-n)//d)

@lru_cache(None)
def atan_small(x):
    assert 0<=x<=Q//2
    xxlo=x*x//Q;xxhi=up(x*x,Q)
    pl=ph=x;lo=hi=0
    for k in range(16):
        tl=pl//(2*k+1);th=up(ph,2*k+1)
        if k%2:lo-=th;hi-=tl
        else:lo+=tl;hi+=th
        pl=pl*xxlo//Q;ph=up(ph*xxhi,Q)
    # Sixteen terms end in a negative term; the next positive term bounds
    # the alternating remainder.  pl,ph now enclose x^33.
    hi+=up(ph,33)
    return lo,hi

def atan_base_fraction(n,d):
    return atan_small(n*Q//d)[0],atan_small(up(n*Q,d))[1]

A5=atan_base_fraction(1,5);A239=atan_base_fraction(1,239)
PI_LO=16*A5[0]-4*A239[1]
PI_HI=16*A5[1]-4*A239[0]
assert 3*Q<PI_LO<PI_HI<4*Q

@lru_cache(None)
def atan_fixed(x):
    assert 0<=x<=Q
    if x<=Q//2:return atan_small(x)
    vl=(Q-x)*Q//(Q+x);vh=up((Q-x)*Q,Q+x)
    al=atan_small(vl)[0];ah=atan_small(vh)[1]
    return PI_LO//4-ah,up(PI_HI,4)-al

@lru_cache(None)
def asin_fraction(n,d):
    assert d>0
    if n<=0:return 0,0
    if n>=d:return PI_LO//2,up(PI_HI,2)
    tl=n*Q//d;th=up(n*Q,d)
    sl2=max(0,Q-up(th*th,Q));sh2=max(0,Q-tl*tl//Q)
    sl=isqrt(sl2*Q);sh=isqrt(sh2*Q)+1
    ql=tl*Q//(Q+sh);qh=min(Q,up(th*Q,Q+sl))
    return 2*atan_fixed(ql)[0],2*atan_fixed(qh)[1]

def asin_coord(x,rn,rd):
    n=x*rd;d=B*rn;g=gcd(n,d)
    return asin_fraction(n//g,d//g)

def acos_coord(x,rn,rd):
    lo,hi=asin_coord(x,rn,rd)
    return PI_LO//2-hi,up(PI_HI,2)-lo

def rect_arc_lower(xlo,xhi,ylo,yhi,rn,rd):
    total=0
    for sx in (1,-1):
        xl=max(0,xlo if sx==1 else -xhi)
        xh=xhi if sx==1 else -xlo
        if xh<=xl:continue
        for sy in (1,-1):
            yl=max(0,ylo if sy==1 else -yhi)
            yh=yhi if sy==1 else -ylo
            if yh<=yl:continue
            upper_lo=min(acos_coord(xl,rn,rd)[0],asin_coord(yh,rn,rd)[0])
            lower_hi=max(acos_coord(xh,rn,rd)[1],asin_coord(yl,rn,rd)[1])
            total+=max(0,upper_lo-lower_hi)
    return total

def charge_margin(box):
    al,ah,bl,bh=box
    origin=(ah<B and bh<B)
    score=0
    for rn,rd,w in WEIGHTS:
        score+=w*rect_arc_lower(ah-B,al,bh-B,bl,rn,rd)
    return score-(1000-ATOM*origin)*2*PI_HI

def verify():
    # These five roots cover the residual domains after the manuscript's
    # analytic inner-square, vertical-translation, strip, and outward moves.
    roots=[
        ('line',9*B//10,B,B//2,B//2,0),
        ('line',B,11*B//10,B//2,B//2,0),
        ('corner',9*B//10,11*B//10,9*B//10,11*B//10,0),
        ('middle',11*B//10,27*B//20,B,27*B//20,0),
        ('outer',0,0,B//2,3*B//2,0),
    ]
    stack=roots[:];counts=Counter();depths=Counter();minimum=None
    digest=hashlib.sha256()
    while stack:
        typ,al,ah,bl,bh,dep=stack.pop()
        if typ=='outer':
            # Actual b is at most sqrt(2); retain equality.
            empty=bl*bl>2*B*B
            if not empty:
                # a=sqrt(4-b^2). Integer square roots round outward.
                al=isqrt(4*B*B-bh*bh)
                ah=isqrt(4*B*B-bl*bl)+1
        else:
            empty=typ!='line' and (bl>ah or al*al+bl*bl>4*B*B)
        box=(al,ah,bl,bh)
        if empty:
            counts[typ+'_empty']+=1;kind='E';margin=0
        else:
            margin=charge_margin(box)
            if margin>=0:
                counts[typ+'_charged']+=1;kind='C'
                minimum=margin if minimum is None else min(minimum,margin)
            else:
                if typ!='outer' and ah-al>=bh-bl:
                    mid=(al+ah)//2
                    assert al<mid<ah,('unresolved',typ,box,margin)
                    stack.append((typ,mid,ah,bl,bh,dep+1))
                    stack.append((typ,al,mid,bl,bh,dep+1))
                else:
                    mid=(bl+bh)//2
                    assert bl<mid<bh,('unresolved',typ,box,margin)
                    stack.append((typ,al,ah,mid,bh,dep+1))
                    stack.append((typ,al,ah,bl,mid,dep+1))
                counts[typ+'_split']+=1
                continue
        depths[dep]+=1
        digest.update((typ+':'+kind+':'+','.join(map(str,box))+'\\n').encode())
    charged=sum(v for k,v in counts.items() if k.endswith('_charged'))
    empty=sum(v for k,v in counts.items() if k.endswith('_empty'))
    split=sum(v for k,v in counts.items() if k.endswith('_split'))
    assert charged+empty==split+len(roots)
    assert ATOM+sum(w for _,_,w in WEIGHTS)==8997
    assert ATOM+714>1000
    assert 7*PI_HI<22*Q
    # Independent exact checks of the manuscript's simple strip constants.
    from fractions import Fraction as F
    x=F(47,100)
    assert F(5,11)-(x-x**3/6+x**5/120)==F(21887804923,13200000000000)>0
    assert F(3858,6000)+F(2424,1000)*F(47,100)*F(7,22)-1==F(189,34375)>0
    result={
        'scale':Q,'coordinate_denominator':B,
        'pi_lower_integer':PI_LO,'pi_upper_integer':PI_HI,
        'weight_total':[8997,1000],
        'counts':dict(sorted(counts.items())),
        'charged_leaves':charged,'empty_leaves':empty,'splits':split,
        'maximum_depth':max(depths),
        'minimum_charged_margin_integer':minimum,
        'leaf_sha256':digest.hexdigest(),
    }
    print(json.dumps(result,sort_keys=True),flush=True)
    return result


if __name__=='__main__':
    verify()

