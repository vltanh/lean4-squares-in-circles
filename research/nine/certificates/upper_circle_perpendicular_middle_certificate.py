"""Exact eight-panel certificate for an upper-circle loaded middle tip.

Every operation is an outward rational integer enclosure on a 2**-40
lattice. The eight closed B panels cover [-1/2,1/2] exactly, while
one closed d interval covers [1,61/60]. No numerical sample or tolerance
is used. See S_LEAF_C5_OWNED_EAST_STRICT_MIDDLE_UPPER_CORNER_EXCLUSION.md.
"""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt

D = 1 << 40

def floorq(q):
    return q.numerator // q.denominator

def ceilq(q):
    return -((-q.numerator) // q.denominator)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi
    @staticmethod
    def rational(q):
        q = Q(q)
        return I(floorq(q*D), ceilq(q*D))
    @staticmethod
    def range(lo, hi):
        return I(floorq(Q(lo)*D), ceilq(Q(hi)*D))
    def __add__(a,b):
        b=cv(b); return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-cv(b)
    def __rsub__(a,b):return cv(b)+-a
    def __mul__(a,b):
        b=cv(b)
        v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(v)//D,-((-max(v))//D))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=cv(b)
        if b.lo<=0:raise ArithmeticError('nonpositive interval divisor')
        return a*I((D*D)//b.hi,-((-(D*D))//b.lo))
    def __rtruediv__(a,b):return cv(b)/a
    def sq(a):
        lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
        hi=max(a.lo*a.lo,a.hi*a.hi)
        return I(lo//D,-((-hi)//D))
    def sqrt(a):
        if a.hi<0:raise ArithmeticError('negative square root')
        lo=isqrt(max(0,a.lo)*D)
        v=a.hi*D; hi=isqrt(v)
        if hi*hi<v:hi+=1
        return I(lo,hi)
    def intersect(a,b):
        return I(max(a.lo,b.lo),min(a.hi,b.hi))
    def empty(a):return a.lo>a.hi
    def above(a,q):return Q(a.lo,D)>q
    def below(a,q):return Q(a.hi,D)<q

def cv(x):return x if isinstance(x,I) else I.rational(x)

def run():
    rows=[]
    for i in range(8):
        d=I.range(1,Q(61,60))
        B=I.range(Q(-1,2)+Q(i,8),Q(-1,2)+Q(i+1,8))
        R2=(d+1).sq()+Q(1,4)
        A=(d.sq()+Q(1,4)-B.sq()).sqrt()
        H=(R2-(1-B).sq()).sqrt()
        k=H-A
        ratio=(A/2+d*B)/(d*A-B/2)
        gap=k*(1-B)-H*(1-k)*ratio
        assert gap.lo>0,(i,gap.lo)
        rows.append(gap.lo)
    print('lattice denominator',D)
    print('eight exact lower numerators',rows)
    print('uniform exact positive lower bound',str(Q(min(rows),D)))
    return rows

if __name__=='__main__':run()
