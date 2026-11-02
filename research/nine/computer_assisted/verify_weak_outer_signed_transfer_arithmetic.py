#!/usr/bin/env python3
"""Exact arithmetic for the continuous signed transfer hand proof.

This verifies printed constants and the half-angle polynomial identity;
the manuscript supplies all geometry and continuous-domain coverage.
No Lean, Lake, CI, optimizer, or sampled proof is used.
"""
from fractions import Fraction as F
import json


def verify():
    a, b, k, T, V = F(46), F(27, 2), F(207, 16), F(211, 4), F(5, 8)
    assert (a-k)/a == F(23, 32)
    # Common numerator after alpha=(1-z^2)/(1+z^2):
    # alpha*23/32 + z*(1-alpha) - V.
    numerator = [F(23,32)-V, F(0), -F(23,32)-V, F(2)]
    assert [32*x for x in numerator] == [3, 0, -43, 64]
    # sqrt(2)-1 < 5/12 < 43/96, so p' is nonpositive.
    assert F(17,12)**2 > 2
    assert F(5,12) < F(43,96)
    # At z=sqrt(2)-1, p=406 sqrt(2)-574.
    # z^2=3-2sqrt(2); z^3=5sqrt(2)-7.
    assert 64*5+43*2 == 406
    assert -64*7-43*3+3 == -574
    assert 2*203**2-287**2 == 49
    assert 119**2-2*84**2 == 49
    assert F(3,2)+F(7,32) == F(55,32)
    assert (F(55,32)**2)/2 < F(3,2)**2
    assert 1+V == F(13,8)
    assert 2+V == F(21,8)
    assert F(1,8)**2 < F(1,8)  # 1/(2sqrt(2)) > 1/8.
    assert F(31,30)**2 < 2
    assert F(1,8) > F(7,20)**2  # 1/(2sqrt(2)) > 7/20.
    assert F(59,60)+F(7,20) == F(4,3)
    assert a+b-T == b/2
    assert (a+b)/2+a/2 == T
    assert (a+b)*F(133,64)-T-(a+b) == F(1459,128)
    assert F(1459,128)/b == F(1459,1728) < 1
    assert F(91,60)-F(4,3) == F(11,60) < 1
    assert 2*a+b == 2*T
    return {
        'status': 'PASS',
        'scope': 'Exact arithmetic for the continuous hand proof; not whole-mask closure',
        'transverse_threshold': str(V),
        'half_angle_integer_polynomial': [3, 0, -43, 64],
        'middle_endpoint_squared_reserve': 49,
        'last_endpoint_squared_reserve': 49,
        'right_endpoint_horizontal_difference_upper': str(F(1459,1728)),
        'whole_mask_closed': False,
    }


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
