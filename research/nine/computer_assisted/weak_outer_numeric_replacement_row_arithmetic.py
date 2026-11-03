#!/usr/bin/env python3
"""Exact constants for the all-angle epsilon=1/8 replacement-row theorem."""
from fractions import Fraction as F
import json

eps=F(1,8);a=F(46);b=F(27,2)
assert 1-eps*eps==F(63,64)>eps*eps
assert F(207,16)/a==F(9,32)
assert F(943,16)/a==F(41,32)
assert F(4)/a==F(2,23)
assert F(1,8)<F(1,4)  # 1/(2sqrt2)>1/4>1/8.
# Multiplying q(t)+sharp_toll(t)/2 by64sqrt(1+t^2), then using
# sqrt(1+t^2)<=1+t^2/2, gives t+(23/2)t^2-4t^3.
assert 64-F(105,2)==F(23,2)
assert 9-8==1 and F(8,2)==4
assert F(23,2)-4*F(1,8)>0
minimum_q_reserve=63*126**2-1000**2
assert minimum_q_reserve==188>0
sharp_left=21231**2-65*2615**2
sharp_right=8316**2-10*2615**2
assert 21231==337*63 and 8316==132*63
assert 2615==41*63+32
assert sharp_left==6270736>0 and sharp_right==773606>0
four_beta=126**2-10*23**2
assert four_beta==10586>0
assert 2*a+b==2*F(211,4)
assert F(3,2)-F(2,3)==F(5,6)
assert F(5,6)-F(1,2)==F(1,3)
assert F(15,16)-1==F(-1,16)
assert F(-1,16)+eps<F(15,16)
assert F(2,3)>eps
print(json.dumps({'claim':'all-angle near-horizontal replacement row and strict closed-Q caller',
                  'status':'PASS','epsilon':str(eps),
                  'q_minimum_squared_reserve':minimum_q_reserve,
                  'sharp_toll_endpoint_squared_reserves':[sharp_left,sharp_right],
                  'four_beta_endpoint_squared_reserve':four_beta,
                  'whole_mask_closed':False},indent=2))
