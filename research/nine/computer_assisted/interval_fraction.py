"""Small exact rational interval arithmetic with dyadic square-root bounds."""
from fractions import Fraction as F
from math import isqrt

class I:
    def __init__(self,lo,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi
        else: self.lo,self.hi=F(lo),F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,o):
        o=I(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o);p=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o); assert o.lo>0 or o.hi<0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return I(o)/self
    def sq(self):
        return I(0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
    def abs(self):
        return I(0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def sqrt(self,bits=44):
        assert self.lo>=0
        d=1<<bits
        lo=isqrt((self.lo.numerator*d*d)//self.lo.denominator)
        hi=isqrt((self.hi.numerator*d*d)//self.hi.denominator)+1
        return I(F(lo,d),F(hi,d))
    def serialize(self):return [str(self.lo),str(self.hi)]
    def floats(self):return [float(self.lo),float(self.hi)]

def norm(v):return (v[0].sq()+v[1].sq()).sqrt()
def dot(v,w):return v[0]*w[0]+v[1]*w[1]
def cross(v,w):return v[0]*w[1]-v[1]*w[0]

