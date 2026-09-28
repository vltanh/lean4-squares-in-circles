#!/usr/bin/env python3
"""Exact rational interval primitives for the n=6 normalization repair.

This module is deliberately independent of the old already-normalized verifier.
It provides only the arithmetic needed by discovery/replay from the N0 boundary:
Machin bounds for pi, Taylor bounds for sin/cos, rational sqrt brackets, and the
candidate ceiling Q0.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import factorial, isqrt
from typing import Tuple

Interval = Tuple[Q, Q]
Q0 = Q(142559, 50000)
CORE = Q(23, 200)


def atan_bounds(x: Q, terms: int = 18) -> Interval:
    assert 0 <= x <= 1
    s = Q(0)
    for k in range(terms):
        term = x ** (2 * k + 1) / Q(2 * k + 1)
        s += term if k % 2 == 0 else -term
    nxt = x ** (2 * terms + 1) / Q(2 * terms + 1)
    return (s, s + nxt) if terms % 2 == 0 else (s - nxt, s)


def pi_bounds() -> Interval:
    a5 = atan_bounds(Q(1, 5))
    a239 = atan_bounds(Q(1, 239))
    return 16 * a5[0] - 4 * a239[1], 16 * a5[1] - 4 * a239[0]


PI = pi_bounds()


def sin_point_bounds(x: Q, m: int = 24) -> Interval:
    s = Q(0)
    for k in range(m + 1):
        term = x ** (2 * k + 1) / Q(factorial(2 * k + 1))
        s += term if k % 2 == 0 else -term
    rem = abs(x) ** (2 * m + 2) / Q(factorial(2 * m + 2))
    return s - rem, s + rem


def cos_point_bounds(x: Q, m: int = 24) -> Interval:
    s = Q(0)
    for k in range(m + 1):
        term = x ** (2 * k) / Q(factorial(2 * k))
        s += term if k % 2 == 0 else -term
    rem = abs(x) ** (2 * m + 1) / Q(factorial(2 * m + 1))
    return s - rem, s + rem


def sqrt_bounds(x: Q, bits: int = 80) -> Interval:
    assert x >= 0
    scale = 1 << bits
    n = (x.numerator * scale * scale) // x.denominator
    a = isqrt(n)
    lo = Q(a, scale)
    hi = Q(a + 1, scale)
    assert lo * lo <= x <= hi * hi
    return lo, hi


def candidate_radial_bounds() -> Interval:
    lo, hi = sqrt_bounds(Q0 - Q(1, 4))
    return lo - Q(1, 2), hi - Q(1, 2)


def self_test() -> None:
    plo, phi = PI
    assert plo < Q(22, 7)
    assert phi > Q(333, 106)
    for x in (Q(0), Q(1, 10), Q(1), Q(3)):
        slo, shi = sin_point_bounds(x)
        clo, chi = cos_point_bounds(x)
        assert slo <= shi and clo <= chi
    rlo, rhi = candidate_radial_bounds()
    assert rlo < rhi
    assert rhi - 1 < CORE
    print("normalization exact arithmetic: PASS")
    print("pi width:", PI[1] - PI[0])
    print("rho(Q0):", rlo, rhi)
    print("23/200 - (rho_hi-1):", CORE - (rhi - 1))


if __name__ == "__main__":
    self_test()
