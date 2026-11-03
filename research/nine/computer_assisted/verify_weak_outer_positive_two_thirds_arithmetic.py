#!/usr/bin/env python3
"""Exact scalar checks for the positive-D 2/3 transfer manuscript."""
from fractions import Fraction as F
import json


def verify():
    V=F(2,3);T=F(1,3)
    assert F(133,64)+F(1,60)==F(2011,960)
    assert V*V<F(1,2)
    assert F(2011,960)+V*T==F(6673,2880)
    assert 21120**2-10*6673**2==765110>0
    assert F(1,8)>F(1,6)**2
    assert F(23,32)>F(1,2)
    assert 207**2-10*64**2==1889>0
    assert 1-T/2==F(5,6)
    assert F(23,32)+T/2==F(85,96)
    assert 2+V*T==F(20,9)
    assert F(11,3)+F(5,6)*3+F(85,96)==F(677,96)
    assert 6093**2-10*1920**2==260649>0
    assert F(5,6)+F(85,96)==F(55,32)
    assert F(19,6)**2>10 and F(10,7)**2>2
    assert F(22,19)+F(77,64)-F(20,9)==F(1519,10944)>0
    assert F(529,16)/46==F(23,32)
    return {
        'status':'PASS',
        'scope':'Exact constants for complete positive-D hand transfer; not whole-mask closure',
        'transverse_threshold':str(V),
        'all_owned_normal_slope_upper':str(T),
        'normal_slope_squared_reserve':765110,
        'small_D_slope_squared_reserve':1889,
        'large_D_first_endpoint_squared_reserve':260649,
        'large_D_diagonal_endpoint_rational_reserve':'1519/10944',
        'whole_mask_closed':False,
        'lean_lake_ci_run':False,
    }


if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
