"""Exact rational lower bounds for circle arcs in axis rectangles."""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt

if not __debug__:
    raise RuntimeError("Run without -O: certificate comparisons use assertions.")

SQRT_SCALE=10**14

def sqrt_bounds(x):
    assert x>=0
    n=x.numerator*SQRT_SCALE*SQRT_SCALE//x.denominator
    k=isqrt(n)
    lo=F(k,SQRT_SCALE)
    hi=lo if lo*lo==x else F(k+1,SQRT_SCALE)
    assert lo*lo<=x<=hi*hi
    return lo,hi

def atan_bounds(x,n=18):
    assert 0<=x<=F(1,2)
    term=x;s=F(0)
    for j in range(n):
        s += term/(2*j+1) if j%2==0 else -term/(2*j+1)
        term *= x*x
    next_term=term/(2*n+1)
    return (s,s+next_term) if n%2==0 else (s-next_term,s)

p0,p1=atan_bounds(F(1,5),30)
r0,r1=atan_bounds(F(1,239),10)
PI_LO=16*p0-4*r1
PI_HI=16*p1-4*r0
assert F(3141592653589793,10**15)<PI_LO<PI_HI<F(22,7)

@lru_cache(maxsize=None)
def asin_bounds(z):
    assert 0<=z<=1
    if z==0:return F(0),F(0)
    if z==1:return PI_LO/2,PI_HI/2
    if z>F(3,4):
        lo,hi=sqrt_bounds(1-z*z)
        low=asin_bounds(lo)[0]
        high=asin_bounds(hi)[1]
        return PI_LO/2-high,PI_HI/2-low
    lo,hi=sqrt_bounds(1-z*z)
    tlo=z/(1+hi);thi=z/(1+lo)
    assert thi<F(1,2)
    return 2*atan_bounds(tlo)[0],2*atan_bounds(thi)[1]

def acos_bounds(z):
    lo,hi=asin_bounds(z)
    return PI_LO/2-hi,PI_HI/2-lo

def rectangle_arc_lower(rect,radius):
    """Closed rectangle arc measure; boundary membership changes no length."""
    if rect[0][0]>rect[0][1] or rect[1][0]>rect[1][1]:return F(0)
    total=F(0)
    for sx in (-1,1):
        for sy in (-1,1):
            intervals=[]
            for (lo,hi),sign in zip(rect,(sx,sy)):
                if sign<0:lo,hi=-hi,-lo
                intervals.append((max(lo,F(0)),min(hi,radius)))
            (lx,ux),(ly,uy)=intervals
            if lx>ux or ly>uy:continue
            upper_lower=min(acos_bounds(lx/radius)[0],asin_bounds(uy/radius)[0])
            lower_upper=max(acos_bounds(ux/radius)[1],asin_bounds(ly/radius)[1])
            total+=max(F(0),upper_lower-lower_upper)
    return total

RADII=(F(3,10),F(3,5),F(5,4))
WEIGHTS=(F(3,100),F(17,40),F(109,200))
assert sum(WEIGHTS)==1

def weighted_lower(box):
    rect=[(hi-F(1,2),lo+F(1,2)) for lo,hi in box]
    return sum(w*rectangle_arc_lower(rect,r) for w,r in zip(WEIGHTS,RADII))
