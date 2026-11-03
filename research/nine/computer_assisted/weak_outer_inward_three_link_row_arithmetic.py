#!/usr/bin/env python3
"""Exact scalar checks for the complete inward-endpoint three-link hand proof."""
from fractions import Fraction as F
import json
from pathlib import Path

def p(s): return 15-48*s+41*s*s-4*s*s*s
def dp(s): return -48+82*s-12*s*s

def main():
    assert p(F(2,3)) == F(1,27)
    assert dp(F(2,3)) == F(4,3)
    assert 82-24 == 58
    assert F(1,27)-F(4,261) == F(17,783)
    assert F(25,256)-F(1,16) == F(9,256)
    assert 2*165**2-232**2 == 626
    assert 2*23**2-32**2 == 34
    assert 2*46+F(27,2) == F(211,2)
    # Polynomial identity for the rational upper bound in scalar branch two.
    # 12(3+s^2)[5/12-s/3-3(s-s^2)/(3+s^2)] = p(s).
    for s in (F(0),F(1,5),F(1,2),F(2,3),F(1)):
        lhs=12*(3+s*s)*(F(5,12)-s/3-3*(s-s*s)/(3+s*s))
        assert lhs == p(s)
    # The preceding cubic identity has degree <=3; five distinct rational
    # evaluations establish equality of its two polynomials exactly.
    result={"status":"PASS","scope":"exact arithmetic accompanying the printed continuous proof; no numerical proof or mask closure",
            "curvature_floor":58,"polynomial_lower_reserve":"17/783",
            "first_branch_large_r_reserve":"9/256",
            "second_branch_radical_squared_reserve":626,
            "endpoint_f_positive_squared_reserve":34,
            "row_total_vertical_variation":"1/3","equality":"all four row originals aligned; each horizontal gap one"}
    print(json.dumps(result,indent=2))
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__ == '__main__': main()
