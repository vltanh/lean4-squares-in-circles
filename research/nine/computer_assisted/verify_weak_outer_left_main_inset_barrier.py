#!/usr/bin/env python3
"""Exact constants for the unchanged-original A inset barrier hand proof."""
from fractions import Fraction as F
import json


def verify():
    Q = F(1105, 256)
    r_upper = F(133, 64)
    assert r_upper*r_upper > Q
    assert r_upper-F(3, 2) == F(37, 64)
    assert 1/(4*F(37, 64)) == F(16, 37)
    assert 4-r_upper == F(123, 64)
    assert F(7, 2)-r_upper == F(91, 64)
    vertical = F(32, 37)-F(3, 40)
    assert vertical > 0
    reserve = F(123, 64)**2+vertical**2-Q
    assert reserve == F(151929, 140185600) > 0
    right = -F(91, 60)+F(16, 37)
    left = -F(91, 64)-F(16, 37)
    assert right == -F(2407, 2220)
    assert left < -F(11, 10) < right
    return {
        "status": "PASS",
        "claim": "Original A contains the fixed vertical segment x=-11/10, |y|<=3/40 in its interior",
        "outside_corner_squared_reserve": str(reserve),
        "right_horizontal_reserve": str(right+F(11, 10)),
        "left_horizontal_reserve": str(-F(11, 10)-left),
        "whole_mask_closed": False,
        "lean_lake_ci_run": False,
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
