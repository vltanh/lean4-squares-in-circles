#!/usr/bin/env python3
"""Exact scalar checks for N17 side-nearestness and the affine marker.

This checker assumes only the N16 core conclusion and candidate-radius
containment.  It contains no sector, pin, or central-separator assumptions.
"""
from fractions import Fraction as Q

from n6_normalization_interval import CORE, PI, Q0, candidate_radial_bounds


def main() -> None:
    r = Q(1, 2) - CORE  # 77/200

    # If u >= 1/2, the closest point of the exterior square is a corner.
    # Writing x=a-1/2,y=u-1/2, disjointness from the central core gives
    # x^2+y^2 > r^2 and x+y > r.  Its far corner therefore exceeds Q0.
    corner_floor = r * r + 2 * r + 2
    assert corner_floor - Q0 > Q(3, 50)

    # Thus u<1/2 and the nearest distance is a-1/2.  The strict core gives
    # a > 1/2+r = 177/200.
    a0 = Q(1, 2) + r
    assert a0 == Q(177, 200)

    # Candidate containment gives a <= rho(Q0) < 223/200.
    rho = candidate_radial_bounds()[1]
    assert rho < Q(223, 200)

    # With a>177/200, candidate containment forces u<117/250.
    assert Q0 - (a0 + Q(1, 2)) ** 2 < Q(121, 125) ** 2
    assert Q(121, 125) - Q(1, 2) == Q(117, 250)

    # The axial label lies below the cap term.
    assert Q(5, 4) * Q(117, 250) < PI[0] / 4

    # It also lies below the side term.  In X=a+1/2,Y=u+1/2 coordinates,
    # axial<=side is 9X+11Y <= 2*pi+17.  If 9X+11Y >= 231/10,
    # containment fails for X>=277/200.  The resulting quadratic is
    # increasing from the left endpoint and already positive there.
    X0 = Q(277, 200)
    M = Q(231, 10)
    q0 = X0 * X0 + (M - 9 * X0) ** 2 / Q(121) - Q0
    dq0 = 2 * X0 - Q(18, 121) * (M - 9 * X0)
    assert q0 > Q(1, 1000)
    assert dq0 > 1
    assert M < 17 + 2 * PI[0]

    print("normalization side-nearest scalar checks: PASS")
    for name, value in (
        ("corner margin", corner_floor - Q0),
        ("rho margin", Q(223, 200) - rho),
        ("tie quadratic", q0),
    ):
        print(f"{name}: {float(value):.12f}")


if __name__ == "__main__":
    main()
