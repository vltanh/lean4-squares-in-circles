"""Two fixed critical-point charges for the radius-two measure's inner line.

See NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md. The whole continuous
line reduces to these two fixed boxes by its exact derivative signs. This
self-contained standard-library checker uses only exact integer/rational
arithmetic. It does not change or import the accepted 208-leaf verifier.

The interval primitives below are the separately reviewed outward-rounded
primitives from NINE_RADIUS_TWO_MEASURE_CERTIFICATE.py, reproduced here so
this two-point check can be run independently as a standalone file.
Status: accepted after full analytic-source and exact-arithmetic reviews;
see the source's root and separate C6 reviews and the five-point assembly.
"""
from functools import lru_cache
from math import isqrt, gcd
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

def verify():
    from fractions import Fraction as F
    H=lambda a:3858**2*(a-F(9,10))*(F(11,10)-a)-714**2*(1-a*a)
    assert H(F(927,1000))==F(-68424471,31250)<0
    assert H(F(928,1000))==F(14285817,15625)>0
    a_star=F(9*2424**2+11*714**2,10*(2424**2-714**2))
    assert a_star==F(324943,298110)
    assert F(1)<a_star<F(11,10)
    fixed=[
        ('left',927*B//1000,up(928*B,1000),WEIGHTS[:2]),
        ('right',a_star.numerator*B//a_star.denominator,
             up(a_star.numerator*B,a_star.denominator),WEIGHTS[:3]),
    ]
    rows=[]
    for name,al,ah,weights in fixed:
        bl=bh=B//2
        origin=(ah<B and bh<B)
        score=sum(w*rect_arc_lower(ah-B,al,bh-B,bl,rn,rd)
                  for rn,rd,w in weights)
        margin=score-(1000-ATOM*origin)*2*PI_HI
        assert margin>0,(name,margin)
        rows.append({'name':name,'box':[al,ah,bl,bh],
                     'circle_radii':[[rn,rd] for rn,rd,_ in weights],
                     'origin_atom':origin,'margin_integer':margin})
    assert rows[0]['margin_integer']==1153182092959159440
    assert rows[1]['margin_integer']==2475502032000671400
    result={'charged_fixed_boxes':2,'scale':Q,'coordinate_denominator':B,
            'pi_lower_integer':PI_LO,'pi_upper_integer':PI_HI,
            'right_critical_point':[a_star.numerator,a_star.denominator],
            'rows':rows}
    print(json.dumps(result,sort_keys=True),flush=True)
    return result


if __name__=='__main__':
    verify()
