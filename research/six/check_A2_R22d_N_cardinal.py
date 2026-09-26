#!/usr/bin/env python3
"""Exact scalar checker for the sharper N-cardinal angle bound in R22-d.

In the normalized frame c_y >= 0.  A north-cardinal helper therefore has
required north-side cap depth at least 1/2.  The exact Q0 cap-depth profile is
strictly below 1/2 at theta = 203/1000, while that point is still on the cap
branch.  Since the established cap-depth profile is decreasing on [0,2/5],
this proves |theta_N| < 203/1000.
"""
from fractions import Fraction as F
from math import factorial, isqrt

Q0 = F(142559, 50000)
T = F(203, 1000)

class I:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi
    def __add__(self, o):
        o = iv(o); return I(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__
    def __neg__(self): return I(-self.hi, -self.lo)
    def __sub__(self, o): return self + (-iv(o))
    def __rsub__(self, o): return iv(o) - self
    def __mul__(self, o):
        o = iv(o)
        z = (self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi)
        return I(min(z), max(z))
    __rmul__ = __mul__

def iv(x): return x if isinstance(x, I) else I(x)

def sqrt_bounds(x: F, bits=120):
    scale = 1 << (2*bits)
    k = isqrt((x.numerator*scale)//x.denominator)
    while F(k*k, scale) > x: k -= 1
    while F((k+1)*(k+1), scale) <= x: k += 1
    return I(F(k,1<<bits), F(k+1,1<<bits))

def sinb(x, n=14):
    x=F(x)
    terms=[(F(-1) if k&1 else F(1))*x**(2*k+1)/F(factorial(2*k+1))
           for k in range(n+2)]
    a=sum(terms[:n+1],F(0)); b=a+terms[n+1]
    return I(min(a,b),max(a,b))

def cosb(x, n=14):
    x=F(x)
    terms=[(F(-1) if k&1 else F(1))*x**(2*k)/F(factorial(2*k))
           for k in range(n+2)]
    a=sum(terms[:n+1],F(0)); b=a+terms[n+1]
    return I(min(a,b),max(a,b))

R = sqrt_bounds(Q0)
K = sqrt_bounds(Q0-F(1,4)) - 1
s = sinb(T)
c = cosb(T)

# Still on the cap branch at T.
assert (R*s).hi < F(1,2)

# B_Q0(T) = (sqrt(Q0-1/4)-1) cos T - (1/2) sin T < 1/2.
depth = K*c - s/2
assert depth.hi < F(1,2), depth.hi

print("R*sin(203/1000) <", float((R*s).hi))
print("B_Q0(203/1000) <", float(depth.hi))
print("R22-d N-cardinal bound: |n| < 203/1000 PASS")
