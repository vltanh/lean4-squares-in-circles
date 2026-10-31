"""Independent Fraction / 2**-48 square-root audit of the complete
eight-panel upper-circle middle certificate. No author interval code imported.
"""
from fractions import Fraction as F
from math import isqrt

GRID = 1 << 48

class Interval:
    def __init__(self, lo, hi=None):
        self.lo=F(lo)
        self.hi=self.lo if hi is None else F(hi)
        assert self.lo<=self.hi
    def __add__(a,b):
        b=box(b);return Interval(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return Interval(-a.hi,-a.lo)
    def __sub__(a,b):return a+-box(b)
    def __rsub__(a,b):return box(b)+-a
    def __mul__(a,b):
        b=box(b)
        x=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return Interval(min(x),max(x))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=box(b);assert b.lo>0
        return a*Interval(1/b.hi,1/b.lo)
    def square(a):
        vals=[a.lo*a.lo,a.hi*a.hi]
        return Interval(0 if a.lo<=0<=a.hi else min(vals),max(vals))
    def sqrt(a):
        assert a.lo>=0
        def down(x):
            n=isqrt((x.numerator*GRID*GRID)//x.denominator)
            assert F(n,GRID)**2<=x<F(n+1,GRID)**2
            return n
        lo=down(a.lo);hi=down(a.hi)
        if F(hi,GRID)**2<a.hi:hi+=1
        return Interval(F(lo,GRID),F(hi,GRID))

def box(x):return x if isinstance(x,Interval) else Interval(x)

def run():
    floors=[]
    for i in range(8):
        d=Interval(1,F(61,60))
        b=Interval(F(-1,2)+F(i,8),F(-1,2)+F(i+1,8))
        a=(d.square()+F(1,4)-b.square()).sqrt()
        h=((d+1).square()+F(1,4)-(1-b).square()).sqrt()
        k=h-a
        ratio=(a/2+d*b)/(d*a-b/2)
        gap=k*(1-b)-h*(1-k)*ratio
        assert gap.lo>0
        floor=(gap.lo.numerator*GRID)//gap.lo.denominator
        floors.append(floor)
        print(i,"positive lower numerator over",GRID,":",floor)
    print("uniform lower bound",F(min(floors),GRID))
    return floors

if __name__=="__main__":run()

