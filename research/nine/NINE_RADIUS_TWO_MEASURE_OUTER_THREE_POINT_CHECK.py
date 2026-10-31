"""Three fixed charges and one tangent enclosure for the radius-two outer curve.

See NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md. Continuous
monotonicity and strong convexity reduce the entire curve to these fixed
checks. This self-contained standard-library checker uses exact integers
and rational arithmetic, with no adaptive subdivision or sampled premise.
The accepted 208-leaf verifier is neither imported nor changed.

Interval-angle primitives are reproduced from the independently reviewed
NINE_RADIUS_TWO_MEASURE_CERTIFICATE.py. Status: accepted after full analytic-source and exact-arithmetic reviews;
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
    # Complete fixed tangent at b=13/12: rational squared bounds only.
    b=F(13,12);w=b-1
    a0,a1=F(1681,1000),F(1682,1000)
    t10,t11=F(731,1000),F(733,1000)
    t20,t21=F(863,1000),F(864,1000)
    v10,v11=F(996,1000),F(997,1000)
    v20,v21=F(1096,1000),F(1097,1000)
    u0,u1=F(805,1000),F(806,1000)
    v30,v31=F(1347,1000),F(1348,1000)
    for rad,lo,hi in [
        (4-b*b,a0,a1),(1-w*w,v10,v11),
        (F(121,100)-w*w,v20,v21),
        (F(729,400)-b*b,u0,u1),(F(729,400)-w*w,v30,v31),
    ]:
        assert 0<lo<hi and lo*lo<rad<hi*hi
    assert t10*t10<1-(a1-1)**2
    assert 1-(a0-1)**2<t11*t11
    assert t20*t20<F(121,100)-(a1-1)**2
    assert F(121,100)-(a0-1)**2<t21*t21
    derivative_lo=(3858*(b/(a1*t11)-1/v10)
                    +2424*(b/(a1*t21)-1/v20)
                    +1709*(1/u1-1/v30))
    derivative_hi=(3858*(b/(a0*t10)-1/v11)
                    +2424*(b/(a0*t20)-1/v21)
                    +1709*(1/u0-1/v31))
    assert -40<derivative_lo<derivative_hi<0
    assert derivative_lo==F(-1254291053647768750,34246309814693847)
    assert derivative_hi==F(-798076820624315593050,62929379411568326209)
    assert PI_LO>3*Q
    # The continuous source proves total second derivative>1/30.
    assert F(4800,19683)-F(250,2197)-F(1,8)==F(585083,115316136)>0
    assert F(1709,16000)*F(7,22)-F(1,30)==F(689,1056000)>0
    assert F(201,200)-F(1,1500)==1+F(13,3000)
    # Three fixed common rectangles: b=1/2, b=13/12, a=b=sqrt(2).
    bb=B//2;aa=isqrt(4*B*B-bb*bb)
    bl=13*B//12;bh=up(13*B,12)
    middle=(isqrt(4*B*B-bh*bh),isqrt(4*B*B-bl*bl)+1,bl,bh)
    diagonal=isqrt(2*B*B)
    boxes=[('left',(aa,aa+1,bb,bb)),('tangent',middle),
           ('diagonal',(diagonal,diagonal+1,diagonal,diagonal+1))]
    rows=[]
    for name,box in boxes:
        al,ah,bl,bh=box
        score=sum(ww*rect_arc_lower(ah-B,al,bh-B,bl,rn,rd)
                  for rn,rd,ww in WEIGHTS[1:])
        # Charge>201/200=1005/1000; no origin atom is present.
        margin=score-1005*2*PI_HI
        assert margin>0,(name,box,margin)
        rows.append({'name':name,'box':list(box),'margin_integer':margin})
    assert [row['margin_integer'] for row in rows]==[
        2486115696770948576,1716983502928824028,336341375099883104]
    result={'charged_fixed_boxes':3,'fixed_derivative_enclosures':1,
        'charge_target':[201,200],'uniform_outer_charge_exceeds':[3013,3000],
        'scale':Q,'coordinate_denominator':B,
        'derivative_raw_lower':[derivative_lo.numerator,derivative_lo.denominator],
        'derivative_raw_upper':[derivative_hi.numerator,derivative_hi.denominator],
        'rows':rows}
    print(json.dumps(result,sort_keys=True),flush=True)
    return result


if __name__=='__main__':
    verify()
