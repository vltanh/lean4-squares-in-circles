#!/usr/bin/env python3
"""Exact scalar checks for the N16 central-core normalization lemma.

This is an arithmetic cross-check for the hand reduction in HAND_PROOF.md.
It does not search the normalized 17-dimensional state and it assumes none of
N16--N22.  The only inputs are the N0 candidate ceiling Q0, the genuine Seven
marker-arc half-width 801/1600, and the scalar endpoint inequalities displayed
in the N16 proof.

Run:
    python research/six/check_normalization_core.py
"""
from fractions import Fraction as Q

from n6_normalization_interval import (
    CORE,
    PI,
    Q0,
    candidate_radial_bounds,
    cos_interval,
    scale_interval,
    sin_interval,
    sqrt_bounds,
)

W0 = Q(801, 1600)


def piq(q: Q):
    return scale_interval(q, PI)


def a_upper(q: Q) -> Q:
    """Upper bound for a from label lambda=q*pi and lambda <= 5 b/4."""
    lam_lo = piq(q)[0]
    B = Q(1, 2) + Q(4, 5) * lam_lo
    return sqrt_bounds(Q0 - B * B, bits=120)[1] - Q(1, 2)


def main() -> None:
    rho = candidate_radial_bounds()

    # Positive-coordinate cardinal support: x >= 23/200 beats rho-1.
    core = CORE - (rho[1] - 1)
    assert core > Q(1, 500)

    # Low window, negative marker sign: the only tight north/primary endpoint
    # has phi=pi/2 and lambda=pi/8.
    low_neg = 1 - a_upper(Q(1, 8))
    assert low_neg > Q(1, 50)

    # Low window, positive marker sign: north support is tight at phi=3pi/8.
    th = piq(Q(3, 8))
    s = sin_interval(th)
    c = cos_interval(th)
    low_pos = Q(1, 2) + Q(1, 2) * (s[0] + c[0]) - rho[1] * s[1]
    assert low_pos > Q(1, 10)

    # Middle window, positive marker sign: tight at phi=5pi/12 and y=2/25.
    th = piq(Q(5, 12))
    s = sin_interval(th)
    c = cos_interval(th)
    mid_pos = (
        Q(2, 25)
        + Q(1, 2)
        + Q(1, 2) * (s[0] + c[0])
        - rho[1] * s[1]
    )
    assert mid_pos > Q(1, 10)

    # Middle window, negative marker sign: phi=pi/2, lambda=pi/12.
    mid_neg = Q(27, 25) - a_upper(Q(1, 12))
    assert mid_neg > Q(1, 25)

    # Own-primary containment defect in the low and middle windows.
    primary_lm = Q(323, 200) ** 2 + Q(1, 4) - Q0
    assert primary_lm > Q(7, 1000)

    # Own-primary containment defect in the high window.  At the only tight
    # endpoint phi=7pi/12, x=1/2, y=3/20, the central support is
    # (13/20) sin(phi).
    th = piq(Q(7, 12))
    s = sin_interval(th)
    h_lo = Q(13, 20) * s[0]
    primary_high = (1 + h_lo) ** 2 + Q(1, 4) - Q0
    assert primary_high > Q(1, 25)

    # The low-window south-cardinal marker-arc endpoint.
    th = (piq(Q(7, 24))[0] - W0, piq(Q(7, 24))[1] - W0)
    s = sin_interval(th)
    south = Q(21, 50) - s[1]
    assert south > Q(3, 200)

    # Any own-secondary separator would have to put the whole marker arc
    # beyond the central supporting line.  The smallest projection of that
    # arc is bounded above by sin(pi/4-W0).
    th = (piq(Q(1, 4))[0] - W0, piq(Q(1, 4))[1] - W0)
    s = sin_interval(th)
    assert s[1] < Q(29, 100)

    # Lowest central support for an own-secondary normal in the low window.
    c = cos_interval(piq(Q(1, 24)))
    assert Q(21, 50) * c[0] > Q(2, 5)

    # Marker-arc endpoints used to eliminate west-cardinal separation stay
    # strictly in the right half-plane in all three windows.
    assert W0 > piq(Q(1, 12))[1]
    assert W0 < piq(Q(5, 24))[0]

    print("normalization core scalar checks: PASS")
    for name, value in (
        ("core", core),
        ("low negative", low_neg),
        ("low positive", low_pos),
        ("middle positive", mid_pos),
        ("middle negative", mid_neg),
        ("primary low/middle", primary_lm),
        ("primary high", primary_high),
        ("south arc", south),
    ):
        print(f"{name}: {float(value):.12f}")


if __name__ == "__main__":
    main()
