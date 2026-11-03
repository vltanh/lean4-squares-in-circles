#!/usr/bin/env python3
"""Exact scalar checks for the conditional deep-B left-lower hand lemma."""
from fractions import Fraction as F
import json


def main():
    rho = F(91, 60)
    p_lower, p_upper, q_lower = F(27, 64), F(31, 60), F(2, 3)
    assert 0 < p_lower < p_upper < q_lower < rho
    assert -rho + 1 == -p_upper
    assert F(5, 64) - F(1, 2) == -p_lower
    case_one = p_upper**2 + (rho - q_lower)**2
    case_two = (1 + p_lower)**2 + q_lower**2 - rho**2
    assert case_one == F(1781, 1800) < 1
    assert case_two == F(50963, 307200) > 0
    print(json.dumps({
        "status": "PASS",
        "scope": "Exact rational constants; complete geometric case union is in the hand manuscript.",
        "case_one_squared_distance_upper": str(case_one),
        "case_one_unit_distance_reserve": str(1 - case_one),
        "case_two_circle_excess": str(case_two),
    }, indent=2))


if __name__ == "__main__":
    main()
