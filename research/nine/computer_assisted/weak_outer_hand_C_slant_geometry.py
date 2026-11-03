#!/usr/bin/env python3
"""Exact scalar checks for slant-to-bottom-region and inset-clearance geometry."""
from fractions import Fraction as F
import json


def main():
    q=F(1105,256);rho=F(91,60);lo,hi=F(29,60),F(4,5)
    assert F(133,64)**2-q==F(9,4096)>0
    horizontal_reserve=(hi-F(5,64))**2-F(1,2)
    assert horizontal_reserve==F(2161,102400)>0
    k=F(133,64)-F(101,432)
    assert k==F(3187,1728)<2
    assert F(11,60)**2<F(1,2)
    height=-F(7,32)-F(7,8)*lo
    assert height==-F(77,120)
    assert -F(5,8)-height==F(1,60)>0
    def f(p):return p*p+(rho-F(7,32)-F(7,8)*p)**2
    reserves=(1-f(lo),1-f(hi))
    assert reserves==(F(11,14400),F(23,9216))
    assert all(r>0 for r in reserves)
    outer=(1+lo)**2+F(5,8)**2-rho*rho
    assert outer==F(93,320)>0
    print(json.dumps({
        "status":"PASS",
        "scope":"Exact scalar constants; the complete geometric case argument is in the hand manuscript.",
        "x_C_upper_squared_reserve":str(horizontal_reserve),
        "height_reserve":str(F(1,60)),
        "bottom_disk_endpoint_reserves":[str(r) for r in reserves],
        "outward_H_circle_excess":str(outer),
        "inset_horizontal_K":str(k),
    },indent=2))


if __name__=='__main__':main()
