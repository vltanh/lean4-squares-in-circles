#!/usr/bin/env python3
"""Exact interval primitives for the n=6 normalization repair.

This module is deliberately independent of every conclusion of the
normalization theorem.  It contains only arithmetic used to audit scalar
inequalities and future N0-based box checks:

* a rational Machin enclosure of pi;
* directed fixed-point intervals;
* Taylor enclosures for sine and cosine;
* directed square roots; and
* the rational candidate ceiling Q0 = 142559/50000.

It must not contain the 23/200 core bound, exterior a/b bounds, sector names,
pins, or central-separator choices.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt

BITS = 50
SCALE = 1 << BITS
Q0 = Q(142559, 50000)


def floor_div(a: int, b: int) -> int:
    assert b > 0
    return a // b


def ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a) // b)


def atan_bounds(x: Q, terms: int = 18) -> tuple[Q, Q]:
    """Alternating-series enclosure for atan(x), 0 <= x <= 1."""
    assert 0 <= x <= 1
    total = Q(0)
    for k in range(terms):
        term = x ** (2 * k + 1) / Q(2 * k + 1)
        total += term if k % 2 == 0 else -term
    nxt = x ** (2 * terms + 1) / Q(2 * terms + 1)
    return (total, total + nxt) if terms % 2 == 0 else (total - nxt, total)


def pi_bounds() -> tuple[Q, Q]:
    """Machin: pi = 16 atan(1/5) - 4 atan(1/239)."""
    a5 = atan_bounds(Q(1, 5))
    a239 = atan_bounds(Q(1, 239))
    return 16 * a5[0] - 4 * a239[1], 16 * a5[1] - 4 * a239[0]


PI_Q_LO, PI_Q_HI = pi_bounds()


@dataclass(frozen=True)
class FI:
    """Closed directed interval with endpoints in units of 2^-BITS."""

    lo: int
    hi: int

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError((self.lo, self.hi))

    @staticmethod
    def integer(n: int) -> "FI":
        return FI(n * SCALE, n * SCALE)

    @staticmethod
    def frac(x: Q) -> "FI":
        return FI(
            floor_div(x.numerator * SCALE, x.denominator),
            ceil_div(x.numerator * SCALE, x.denominator),
        )

    @staticmethod
    def bounds(a: Q, b: Q) -> "FI":
        assert a <= b
        return FI(
            floor_div(a.numerator * SCALE, a.denominator),
            ceil_div(b.numerator * SCALE, b.denominator),
        )

    def __neg__(self) -> "FI":
        return FI(-self.hi, -self.lo)

    def __add__(self, other: "FI | Q | int") -> "FI":
        other = fi(other)
        return FI(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __sub__(self, other: "FI | Q | int") -> "FI":
        return self + (-fi(other))

    def __rsub__(self, other: "FI | Q | int") -> "FI":
        return fi(other) - self

    def __mul__(self, other: "FI | Q | int") -> "FI":
        other = fi(other)
        xs = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return FI(floor_div(min(xs), SCALE), ceil_div(max(xs), SCALE))

    __rmul__ = __mul__

    def div_int(self, n: int) -> "FI":
        assert n != 0
        if n < 0:
            return (-self).div_int(-n)
        return FI(floor_div(self.lo, n), ceil_div(self.hi, n))

    def abs(self) -> "FI":
        if self.lo <= 0 <= self.hi:
            return FI(0, max(-self.lo, self.hi))
        return FI(min(abs(self.lo), abs(self.hi)), max(abs(self.lo), abs(self.hi)))

    def sq(self) -> "FI":
        a = self.abs()
        return a * a

    def width(self) -> int:
        return self.hi - self.lo

    def as_float_pair(self) -> tuple[float, float]:
        return self.lo / SCALE, self.hi / SCALE


def fi(x: FI | Q | int) -> FI:
    if isinstance(x, FI):
        return x
    if isinstance(x, Q):
        return FI.frac(x)
    if isinstance(x, int):
        return FI.integer(x)
    raise TypeError(type(x))


ZERO = FI.integer(0)
ONE = FI.integer(1)
PI = FI.bounds(PI_Q_LO, PI_Q_HI)
Q0_FI = FI.frac(Q0)


def sqrt_fi(x: FI) -> FI:
    if x.lo < 0:
        raise ValueError("sqrt of interval crossing negative values")
    lo = isqrt(x.lo * SCALE)
    if lo * lo > x.lo * SCALE:
        lo -= 1
    hi = isqrt(x.hi * SCALE)
    if hi * hi < x.hi * SCALE:
        hi += 1
    return FI(lo, hi)


def _abs_power(x: FI, n: int) -> FI:
    y = ONE
    a = x.abs()
    for _ in range(n):
        y = y * a
    return y


def _remainder_bound(x: FI, n: int) -> int:
    p = _abs_power(x, n)
    return ceil_div(p.hi, factorial(n))


@lru_cache(maxsize=1_000_000)
def sin_point(lo: int, hi: int) -> FI:
    x = FI(lo, hi)
    x2 = x * x
    term = x
    total = term
    for k in range(1, 21):
        term = (term * x2).div_int((2 * k) * (2 * k + 1))
        total = total - term if k % 2 else total + term
    rem = _remainder_bound(x, 43)
    return FI(total.lo - rem, total.hi + rem)


@lru_cache(maxsize=1_000_000)
def cos_point(lo: int, hi: int) -> FI:
    x = FI(lo, hi)
    x2 = x * x
    term = ONE
    total = term
    for k in range(1, 22):
        term = (term * x2).div_int((2 * k - 1) * (2 * k))
        total = total - term if k % 2 else total + term
    rem = _remainder_bound(x, 44)
    return FI(total.lo - rem, total.hi + rem)


def _k_pi_over_two(k: int) -> FI:
    return (FI.frac(Q(k, 2)) * PI)


def _overlaps(x: FI, y: FI) -> bool:
    return not (x.hi < y.lo or y.hi < x.lo)


@lru_cache(maxsize=500_000)
def sin_interval(lo: int, hi: int) -> FI:
    x = FI(lo, hi)
    if x.width() >= 2 * PI.lo:
        return FI(-SCALE, SCALE)
    a = sin_point(lo, lo)
    b = sin_point(hi, hi)
    low, high = min(a.lo, b.lo), max(a.hi, b.hi)
    for k in range(-9, 10, 2):
        c = _k_pi_over_two(k)
        if _overlaps(x, c):
            value = SCALE if k % 4 == 1 else -SCALE
            low, high = min(low, value), max(high, value)
    return FI(max(-SCALE, low), min(SCALE, high))


@lru_cache(maxsize=500_000)
def cos_interval(lo: int, hi: int) -> FI:
    x = FI(lo, hi)
    if x.width() >= 2 * PI.lo:
        return FI(-SCALE, SCALE)
    a = cos_point(lo, lo)
    b = cos_point(hi, hi)
    low, high = min(a.lo, b.lo), max(a.hi, b.hi)
    for j in range(-5, 6):
        c = FI.frac(Q(j)) * PI
        if _overlaps(x, c):
            value = SCALE if j % 2 == 0 else -SCALE
            low, high = min(low, value), max(high, value)
    return FI(max(-SCALE, low), min(SCALE, high))


def check_candidate_below_q0() -> dict[str, str]:
    """Pure rational proof that the chosen algebraic root lies below Q0."""
    h_lo = Q(70710678, 10**8)
    h_hi = Q(70710679, 10**8)
    s_up = Q(84246, 10**6)
    assert h_lo * h_lo < Q(1, 2) < h_hi * h_hi
    coeff_h = -s_up * Q(1940, 267) + Q(432, 712)
    const = s_up * s_up - s_up * Q(1466, 267) + Q(327, 712)
    assert coeff_h < 0
    poly_upper = const + coeff_h * h_lo
    assert poly_upper < 0
    q_at_s_up = 2 * s_up * s_up + 4 * s_up + Q(5, 2)
    assert q_at_s_up < Q0
    return {
        "pi_width": str(PI_Q_HI - PI_Q_LO),
        "quadratic_at_s_upper": str(poly_upper),
        "q0_minus_q_at_s_upper": str(Q0 - q_at_s_up),
    }


def self_test() -> None:
    import math

    report = check_candidate_below_q0()
    for z in (Q(0), Q(1, 10), Q(1), Q(3)):
        x = FI.frac(z)
        s = sin_point(x.lo, x.hi).as_float_pair()
        c = cos_point(x.lo, x.hi).as_float_pair()
        zz = float(z)
        assert s[0] <= math.sin(zz) <= s[1]
        assert c[0] <= math.cos(zz) <= c[1]
    assert PI_Q_LO < Q(22, 7)
    assert PI_Q_HI > Q(333, 106)
    print("n=6 normalization exact core: PASS")
    for key, value in report.items():
        print(f"{key}: {value}")


if __name__ == "__main__":
    self_test()
