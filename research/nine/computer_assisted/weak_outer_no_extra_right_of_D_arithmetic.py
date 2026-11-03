#!/usr/bin/env python3
"""Exact hand-table arithmetic for the no-extra-right-of-D routing lemma."""
from fractions import Fraction as F
from pathlib import Path
import json

def main():
    rho=F(91,60)
    assert rho-F(4,3)==F(11,60)
    assert 1-F(11,60)**2-F(49,50)**2==F(539,90000)
    assert F(29,60)+F(49,50)==F(439,300)
    assert F(49,50)-F(47,120)==F(353,600)
    assert F(439,300)**2+F(353,600)**2-rho**2==F(67393,360000)
    assert F(29,40)**2+F(4,3)**2-rho**2==F(1,320)
    assert rho-F(317,432)==F(1691,2160)
    assert 1-F(1691,2160)**2-F(3,5)**2==F(126503,4665600)
    assert F(17,40)+F(3,5)-F(29,40)==F(3,10)
    assert F(49,50)+F(3,5)==F(79,50)
    assert -F(77,120)+F(31,30)==F(47,120)
    assert rho-F(5,4)==F(4,15)
    assert 1-F(4,15)**2-F(24,25)**2==F(41,5625)
    assert F(31,30)-F(24,25)==F(11,150)
    assert 1-F(11,150)**2-F(49,50)**2==F(77,2250)
    assert F(439,300)**2+F(341,600)**2-rho**2==F(11813,72000)
    assert F(5,4)**2+F(7,8)**2-rho**2==F(401,14400)
    assert 1-F(1691,2160)**2-F(31,50)**2==F(316559,116640000)
    assert F(17,40)+F(31,50)-F(7,8)==F(17,100)
    assert F(24,25)+F(31,50)==F(79,50)
    assert 1-F(3,5)**2==F(4,5)**2
    assert rho+F(17,64)==F(1711,960)
    assert rho+F(115,432)==F(3851,2160)
    assert F(9,5)-F(1711,960)==F(17,960)
    assert F(9,5)-F(3851,2160)==F(37,2160)
    data={"status":"PASS","scope":"exact fractions in the printed original-center routing argument; finite DG upper-gap input separately required",
          "separation_reserve":"539/90000","lower_center_reserve":"67393/360000",
          "outer_height_reserve":"1/320","G_separation_reserve":"126503/4665600",
          "wrong_G_order_reserve":"3/10","DG_upper_threshold":"79/50",
          "stronger_extra_x_upper_bound":"5/4",
          "stronger_D_separation_reserve":"41/5625",
          "stronger_lower_center_reserve":"11813/72000",
          "stronger_height_reserve":"401/14400",
          "stronger_G_separation_reserve":"316559/116640000",
          "F_low_variation_lower_bound":"3/5",
          "left_F_span_reserve":"17/960",
          "right_F_span_reserve":"37/2160"}
    print(json.dumps(data,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
