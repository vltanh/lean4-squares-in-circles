"""Interval geometry from the supplied normalization certificate package.

Default backend: python-flint Arb, 64-bit working precision. The independent
rational replay installs its explicitly named compatibility backend before
importing this module; it is not an Arb run.

Integration hardening: float interval endpoints are enlarged by one ulp before
conversion. This preserves exact rational/algebraic boundary coverage when a
caller obtains an endpoint through a nearest-rounded Python float.
"""
import math
from flint import arb, ctx
ctx.prec = 64
ZERO = arb(0)
ONE = arb(1)
HALF = arb(1) / 2
PI = arb.pi()
Q0 = arb(142559) / 50000
R0 = Q0.sqrt()
RHO0 = (Q0 - arb(1) / 4).sqrt() - HALF
C0 = RHO0 - 1


def iv(lo, hi):
    """An enclosure of [lo, hi], conservatively widened for float endpoints."""
    if isinstance(lo, float):
        if not math.isfinite(lo):
            raise ValueError('finite interval endpoint required')
        lo = math.nextafter(lo, -math.inf)
    if isinstance(hi, float):
        if not math.isfinite(hi):
            raise ValueError('finite interval endpoint required')
        hi = math.nextafter(hi, math.inf)
    return arb(lo).union(arb(hi))


def lo(x): return float(x.lower())
def hi(x): return float(x.upper())
def neg(x): return x < 0
def pos(x): return x > 0
def nonneg(x): return x >= 0
def possibly_nonneg(x): return not (x < 0)


def amax(*xs):
    m = xs[0]
    for x in xs[1:]: m = m.max(x)
    return m


def amin(*xs):
    m = xs[0]
    for x in xs[1:]: m = m.min(x)
    return m


class SqBox:
    """An exterior chart (phi,a,b); n=(cos phi,sin phi), P=a*n+b*nperp."""
    __slots__ = ('phi','a','b','c','s','u','P1','P2','w')

    def __init__(self, phi, a, b):
        self.phi, self.a, self.b = phi, a, b
        self.s, self.c = phi.sin_cos()
        self.u = abs(b)
        self.P1 = a*self.c - b*self.s
        self.P2 = a*self.s + b*self.c
        self.w = (abs(self.c)+abs(self.s))/2

    def contain_gap(self, Q=Q0):
        return (self.a+HALF)**2 + (self.u+HALF)**2 - Q

    def chart_gap(self):
        return self.a-self.u

    def separators(self, cx, cy):
        """Seven remaining directed SAT margins; the eighth is impossible
        under a>=1/2 and O in the open central square (T2)."""
        c,s,a,b,w = self.c,self.s,self.a,self.b,self.w
        cn = cx*c+cy*s
        ct = -cx*s+cy*c
        return {
            'OWN': a-HALF-cn-w,
            'SEC+': b-HALF-ct-w,
            'SEC-': ct-HALF-w-b,
            'CE': self.P1-w-cx-HALF,
            'CW': cx-HALF-self.P1-w,
            'CN': self.P2-w-cy-HALF,
            'CS': cy-HALF-self.P2-w,
        }

    def pin_margin(self, q1, q2):
        qn = q1*self.c+q2*self.s
        qt = -q1*self.s+q2*self.c
        return HALF-abs(qn-self.a).max(abs(qt-self.b))


R_PIN = arb(9)/10


def pin_xy(num, den):
    s,c = (PI*num/den).sin_cos()
    return R_PIN*c,R_PIN*s


PINS = {'E':(R_PIN,ZERO), 'N':(ZERO,R_PIN),
        'W':pin_xy(11,12), 'D':pin_xy(5,4), 'S':pin_xy(19,12)}


def label(a, u):
    """The genuine three-branch Seven label; no axial assumption."""
    return amin(5*u/4, PI/6+(u-HALF)/3+3*(1-a)/4, PI/4)
