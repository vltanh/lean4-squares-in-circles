#!/usr/bin/env python3
"""Exact rational endpoint checks for the SS/SD leaf-pair connected-block proof.

Standard library only. These checks supplement the hand argument; they do
not certify geometry, exhaustiveness, dependencies, or independent review.
No floating-point arithmetic, coefficient table, Lean compilation, or CI.
"""
from fractions import Fraction as F


def main() -> None:
    q0, qmax = F(6241, 1600), F(1105, 256)
    reserves = {
        "d > 91/100": q0-F(1,4)-F(191,100)**2,
        "d < 61/60": F(121,60)**2-(qmax-F(1,4)),
        "sqrt(2) < 283/200": F(283,200)**2-2,
        "adjacent-vertex a > 3/4": F(91,100)**2-F(1,4)-F(3,4)**2,
        "adjacent-vertex a < 1": 1-(F(61,60)**2-F(1,4)),
        "sqrt(5)/4 < 14/25": F(14,25)**2-F(5,16),
        "side-vertex Y > 8/9": 2*F(9,10)-1-F(8,9)**2,
        "side-vertex negative-x bound < 1/4": F(1,4)**2-F(1,100)-F(1,81),
        "side-vertex positive-x bound < 1/4": F(1,4)-F(161,720),
        "opposite-vertex b > 11/20": F(9,10)**2-F(1,2)-F(11,20)**2,
        "1/sqrt(2) < 3/4": F(3,4)**2-F(1,2),
        "opposite-vertex bound < 14/25": F(14,25)-F(19,55),
        "side-side bound < 14/25": F(14,25)**2-F(2,100),
        "r < 7/10: upper R < 21/10": F(21,10)**2-qmax,
        "r < 7/10: sqrt(2) > 7/5": 2-F(7,5)**2,
        "SD top side support < 1/2": F(1,4)-F(11,25)**2-F(1,10)**2,
        "sqrt(2) > 24/17": 2-F(24,17)**2,
        "lower-radius sqrt < 153/80": F(153,80)**2-(q0-F(1,4)),
        "coupled SD radius reserve": F(341,680)-F(1,2),
        "1/sqrt(2) > 7/10": F(1,2)-F(7,10)**2,
        "SD right vertex support < 14/25": F(14,25)**2-F(709,2500),
        "SD left vertex Y > 7/9": F(91,100)**2-F(11,25)**2-F(7,9)**2,
        "SD left vertex negative x < 1/2": F(1,4)-F(11,25)**2-F(2,9)**2,
        "SD left vertex positive x < 14/25": F(14,25)-F(137,252),
    }
    assert F(79,40)-F(283,200) == F(14,25)
    assert F(9,80)+F(1,9) == F(161,720)
    assert F(3,4)-F(11,20) == F(1,5)
    assert F(19,100)/F(11,20) == F(19,55)
    assert reserves["sqrt(5)/4 < 14/25"] == F(11,10000)
    assert -F(5,4)+F(79,20)*F(24,17)-F(153,40) == F(341,680)
    assert F(9,28)+F(2,9) == F(137,252)
    assert reserves["SD right vertex support < 14/25"] == F(3,100)
    assert reserves["SD left vertex positive x < 14/25"] == F(103,6300)
    for name, reserve in reserves.items():
        if reserve <= 0:
            raise AssertionError(f"Failed strict comparison: {name}: {reserve}")
        print(f"PASS {name}: exact squared/scalar reserve {reserve}")
    print(f"PASS: {len(reserves)} strict reserves and nine exact identities.")
    print("Independent geometric and dependency review is NOT certified.")


if __name__ == "__main__":
    main()
