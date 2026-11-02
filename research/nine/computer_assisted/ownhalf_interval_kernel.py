"""Producer-only 64-bit outward integer arithmetic, copied unchanged from the previously used kernel.
Acceptance uses a separate standalone Fraction reconstruction.
"""
from fractions import Fraction as F
from math import isqrt

BITS = 64
SCALE = 1 << BITS
DIM = 4


def ceil_ratio(a, b):
    assert b > 0
    return -((-a) // b)


class I:
    """Closed interval; lo and hi are integer numerators over SCALE."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, I):
            assert hi is None
            self.lo, self.hi = lo.lo, lo.hi
        elif isinstance(lo, int) and (hi is None or isinstance(hi, int)):
            self.lo = lo * SCALE
            self.hi = (lo if hi is None else hi) * SCALE
        else:
            low = F(lo)
            high = low if hi is None else F(hi)
            self.lo = low.numerator * SCALE // low.denominator
            self.hi = ceil_ratio(high.numerator * SCALE, high.denominator)
        assert self.lo <= self.hi

    @classmethod
    def raw(cls, lo, hi):
        assert isinstance(lo, int) and isinstance(hi, int) and lo <= hi
        answer = object.__new__(cls)
        answer.lo, answer.hi = lo, hi
        return answer

    def __add__(self, other):
        if isinstance(other, int):
            n = other * SCALE
            return I.raw(self.lo + n, self.hi + n)
        other = other if isinstance(other, I) else I(other)
        return I.raw(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I.raw(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -(other if isinstance(other, I) else I(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            a, b = self.lo * other, self.hi * other
            return I.raw(min(a, b), max(a, b))
        other = other if isinstance(other, I) else I(other)
        if self.lo == self.hi == 0 or other.lo == other.hi == 0:
            return I.raw(0, 0)
        candidates = (
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi,
        )
        return I.raw(min(candidates) // SCALE,
                     ceil_ratio(max(candidates), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if isinstance(other, int):
            assert other != 0
            if other < 0:
                return (-self) / (-other)
            return I.raw(self.lo // other, ceil_ratio(self.hi, other))
        other = other if isinstance(other, I) else I(other)
        assert other.lo > 0 or other.hi < 0
        if other.hi < 0:
            return (-self) / (-other)
        numerators = (self.lo * SCALE, self.hi * SCALE)
        low = min(a // b for a in numerators for b in (other.lo, other.hi))
        high = max(ceil_ratio(a, b) for a in numerators for b in (other.lo, other.hi))
        return I.raw(low, high)

    def __rtruediv__(self, other):
        return I(other) / self

    def sq(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        high = max(self.lo**2, self.hi**2)
        return I.raw(low // SCALE, ceil_ratio(high, SCALE))

    def abs(self):
        low = 0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))
        return I.raw(low, max(abs(self.lo), abs(self.hi)))

    def sqrt(self):
        assert self.lo >= 0
        low = isqrt(self.lo * SCALE)
        radicand = self.hi * SCALE
        high = isqrt(radicand)
        if high**2 < radicand:
            high += 1
        return I.raw(low, high)

    def fractions(self):
        return F(self.lo, SCALE), F(self.hi, SCALE)


def mn(*xs):
    return I.raw(min(v.lo for v in xs),min(v.hi for v in xs))


def mx(*xs):
    return I.raw(max(v.lo for v in xs),max(v.hi for v in xs))


def frame(t):
    ends=[]
    for q in (I.raw(t.lo,t.lo),I.raw(t.hi,t.hi)):
        a=1/(1+q.sq()).sqrt();b=q*a
        ends.append((a,b,(1+q)*a/2,(1-q)*a/2))
    lo,hi=ends
    return (I.raw(hi[0].lo,lo[0].hi),I.raw(lo[1].lo,hi[1].hi),
            I.raw(lo[2].lo,hi[2].hi),I.raw(hi[3].lo,lo[3].hi))

