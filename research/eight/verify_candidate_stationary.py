#!/usr/bin/env python3
"""Exact stationary-root enclosure for the reconstructed eight-square family.

Standard-library verification only. All interval operations round OUTWARD to
a fixed dyadic lattice using integer arithmetic. The rational preconditioner
is arbitrary data whose required properties are checked, not an oracle.

This proves existence/uniqueness in ROOTBOX of F=F_y=F_z=0. It is NOT a global
lower bound for eight arbitrary squares. No Lean or CI execution is involved.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import isqrt

BITS = 110
SCALE = 1 << BITS


def ceildiv(a: int, b: int) -> int:
    return -((-a) // b)


class Interval:
    """Closed interval [lo/SCALE, hi/SCALE]."""
    __slots__ = ('lo', 'hi')

    def __init__(self, a=0, b=None):
        if isinstance(a, Interval):
            self.lo, self.hi = a.lo, a.hi
            return
        aa, bb = Q(a), Q(a if b is None else b)
        if aa > bb:
            raise ValueError('Reversed endpoints')
        self.lo = aa.numerator * SCALE // aa.denominator
        self.hi = ceildiv(bb.numerator * SCALE, bb.denominator)

    @staticmethod
    def raw(lo: int, hi: int):
        if lo > hi:
            raise ValueError('Reversed dyadic endpoints')
        out = object.__new__(Interval)
        out.lo, out.hi = lo, hi
        return out

    def __add__(self, other):
        other = Interval(other)
        return Interval.raw(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval.raw(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -Interval(other)

    def __rsub__(self, other):
        return Interval(other) + -self

    def __mul__(self, other):
        other = Interval(other)
        products = (self.lo*other.lo, self.lo*other.hi,
                    self.hi*other.lo, self.hi*other.hi)
        return Interval.raw(min(products)//SCALE,
                            ceildiv(max(products), SCALE))

    __rmul__ = __mul__

    def inv(self):
        if self.lo <= 0 <= self.hi:
            raise ValueError('Division interval includes zero')
        return Interval.raw(SCALE*SCALE//self.hi,
                            ceildiv(SCALE*SCALE, self.lo))

    def __truediv__(self, other):
        return self * Interval(other).inv()

    def __rtruediv__(self, other):
        return Interval(other) * self.inv()

    def __pow__(self, n: int):
        if not isinstance(n, int):
            raise TypeError('Only integer powers are supported')
        if n < 0:
            return self.inv() ** (-n)
        if n == 0:
            return Interval(1)
        if n == 2:
            values = (self.lo*self.lo, self.hi*self.hi)
            lo = 0 if self.lo <= 0 <= self.hi else min(values)//SCALE
            return Interval.raw(lo, ceildiv(max(values), SCALE))
        return (self*self)**(n//2) * (self if n % 2 else Interval(1))

    def sqrt(self, clip=False):
        if self.hi < 0 or (self.lo < 0 and not clip):
            raise ValueError('Radicand domain not established')
        lo = isqrt(max(0, self.lo)*SCALE)
        hi = isqrt(self.hi*SCALE)
        return Interval.raw(lo, hi if hi*hi == self.hi*SCALE else hi+1)

    def absmax(self):
        return Q(max(abs(self.lo), abs(self.hi)), SCALE)

    def lower(self):
        return Q(self.lo, SCALE)

    def upper(self):
        return Q(self.hi, SCALE)


I = Interval


class Jet:
    """Value, three first derivatives, and a 3x3 Hessian enclosure."""
    __slots__ = ('v', 'g', 'h')

    def __init__(self, value, gradient=None, hessian=None):
        self.v = I(value)
        self.g = [I(0) for _ in range(3)] if gradient is None else gradient
        self.h = ([[I(0) for _ in range(3)] for _ in range(3)]
                  if hessian is None else hessian)

    @classmethod
    def variable(cls, value, index):
        out = cls(value)
        out.g[index] = I(1)
        return out

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Jet) else Jet(value)

    def __add__(self, other):
        b = Jet.coerce(other)
        return Jet(self.v+b.v, [self.g[i]+b.g[i] for i in range(3)],
                   [[self.h[i][j]+b.h[i][j] for j in range(3)] for i in range(3)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, [-x for x in self.g],
                   [[-x for x in row] for row in self.h])

    def __sub__(self, other):
        return self + -Jet.coerce(other)

    def __rsub__(self, other):
        return Jet.coerce(other) + -self

    def __mul__(self, other):
        b = Jet.coerce(other)
        return Jet(self.v*b.v,
                   [self.g[i]*b.v+self.v*b.g[i] for i in range(3)],
                   [[self.h[i][j]*b.v+self.g[i]*b.g[j]+self.g[j]*b.g[i]
                     +self.v*b.h[i][j] for j in range(3)] for i in range(3)])

    __rmul__ = __mul__

    def unary(self, value, first, second):
        return Jet(value, [first*x for x in self.g],
                   [[first*self.h[i][j]+second*self.g[i]*self.g[j]
                     for j in range(3)] for i in range(3)])

    def inv(self):
        return self.unary(self.v.inv(), -self.v**(-2), 2*self.v**(-3))

    def __truediv__(self, other):
        return self * Jet.coerce(other).inv()

    def __rtruediv__(self, other):
        return Jet.coerce(other) * self.inv()

    def __pow__(self, n):
        if n == 0:
            return Jet(1)
        if n == 1:
            return self
        return self.unary(self.v**n, n*self.v**(n-1), n*(n-1)*self.v**(n-2))

    def sqrt(self):
        value = self.v.sqrt()
        return self.unary(value, 1/(2*value), -1/(4*self.v*value))


def residual(q, y, z):
    """The fifth-corner squared-radius defect; z=tan(t/2)."""
    x1 = (q-y*y).sqrt()
    x2 = (q-(y+2)**2).sqrt()
    y3 = (q-(x2-3)**2).sqrt()
    y4 = y3-2
    x4 = -(q-y4*y4).sqrt()
    c, s = (1-z*z)/(1+z*z), 2*z/(1+z*z)
    h1 = c*x1+s*y-2-c
    h2 = -s*x4+c*y4-1-s
    return h1*h1+h2*h2-q


def jet(box):
    return residual(*(Jet.variable(I(*bounds), k) for k, bounds in enumerate(box)))


CENTER = list(map(Q, ['3.91553413751747532652',
                     '-0.92065667800760613175',
                     '0.06189741100766035970']))
RADIUS = Q(1, 10**16)
ROOTBOX = [(x-RADIUS, x+RADIUS) for x in CENTER]
PRECONDITIONER = [
    list(map(Q, ['-0.270621', '0', '0'])),
    list(map(Q, ['-0.226289', '0.416268', '0.226498'])),
    list(map(Q, ['-0.129681', '0.226498', '0.180945']))]


def verify_root():
    at_center = jet([(x, x) for x in CENTER])
    on_box = jet(ROOTBOX)
    H = [at_center.v, at_center.g[1], at_center.g[2]]
    DH = [on_box.g, on_box.h[1], on_box.h[2]]
    C = PRECONDITIONER
    error = [[I(int(i == j))-sum((C[i][k]*DH[k][j] for k in range(3)), I(0))
              for j in range(3)] for i in range(3)]
    norm = max(sum(error[i][j].absmax() for j in range(3)) for i in range(3))
    correction = [
        -sum((C[i][j]*H[j] for j in range(3)), I(0))
        +sum((error[i][j]*I(-RADIUS, RADIUS) for j in range(3)), I(0))
        for i in range(3)]
    determinant = sum(C[0][j]*(C[1][(j+1)%3]*C[2][(j+2)%3]
                              -C[1][(j+2)%3]*C[2][(j+1)%3]) for j in range(3))
    if determinant == 0 or norm >= Q(1, 100):
        raise AssertionError('Contraction/preconditioner verification failed')
    if not all(v.lower() > -RADIUS and v.upper() < RADIUS for v in correction):
        raise AssertionError('Fixed-point image not strictly inside ROOTBOX')
    print('VERIFIED: nonsingular rational preconditioner; contraction norm < 1/100.')
    print('VERIFIED: T(x)=x-C H(x) maps ROOTBOX strictly into itself.')
    print('Hence exactly one root of F=F_y=F_z=0 lies in ROOTBOX.')
    print('ROOTBOX centers:', list(map(str, CENTER)))
    print('Each coordinate radius:', RADIUS)
    print('This is candidate isolation, NOT unrestricted eight-square optimality.')
    return on_box


if __name__ == '__main__':
    verify_root()
