"""Exact rational audit of the low-floor central/right-shoulder hand proof.

The geometric quantifiers and all separator signs are covered in the
companion manuscript. This independently replays every scalar reserve.
Standard library only; no Lean or CI.
"""
from fractions import Fraction as F
import json

l,u,rho=F(29,60),F(13,12),F(91,60)
g=F(7,20);J=F(23,150);A0=F(18911,59520)
cL=A0-F(1,10);v0=F(223,372);G=F(17,100)
A=u+J-g
B=F(17,16)-A0-g
AH=A-F(1,2)
BH=F(17,16)-v0-g
assert A == F(133,150)
assert AH == F(29,75)
assert G == J+F(1,60)
assert -F(119,310)+F(59,60) == v0
assert -F(119,310)+F(15,31) == F(1,10)
assert F(7,16)-g+F(1,2) == F(47,80)
assert F(17,24)-F(1,2) == F(5,24)
# The identity 1-(1-t/3)^2(1+t^2)=t(6-10t+6t^2-t^3)/9.
p=[F(0),F(2,3),-F(10,9),F(2,3),-F(1,9)]
q=[F(1),-F(2,3),F(1,9)]
r=[F(0)]*5
for i,x in enumerate(q):
    for j,y in enumerate([F(1),F(0),F(1)]):r[i+j]+=x*y
r[0]-=1
assert [-x for x in r] == p
m=F(4,5)
polynomial_endpoint=6-10*m+6*m*m-m**3
checks={
    'fixed_proxy_contained':F(1,8)-g*g,
    'central_above_zero':v0-F(7,16),
    'left_downward_axis_gap':v0-F(47,80),
    'left_inward_axis_gap':cL-F(1,6),
    'left_upward_axis_assignment':cL-G,
    'horizontal_left_forbids_wrong_right_axis':F(2,3)-G,
    'central_floor_coefficient':cL-F(3,14),
    'oblique_tangent_upper_bound':F(4,5)*cL-G,
    'horizontal_tangent_upper_bound':F(81,164)-(l+J)**2,
    'a_linear_lower_bound_polynomial':polynomial_endpoint,
    'a_linear_lower_bound_polynomial_monotonicity':10-12*m,
    'horizontal_gap_oblique':F(19,21)-A,
    'horizontal_gap_horizontal':1-A,
    'right_vertical_radius_bound':F(36,25)**2-(rho*rho-l*l),
    'right_positive_vertical_gap':F(17,20)-F(36,25)+v0,
    'right_negative_vertical_gap':g-F(5,24),
    'h_upper_bound':F(17,24)**2-F(1,2),
    'support_maximum_at_x_upper':rho*rho/(1+m*m)-u*u,
    'right_projection_square_root':F(17,16)**2-(rho*rho-u*u),
    'oblique_cauchy_reserve':1-A*A-B*B,
    'horizontal_cauchy_reserve':F(1,4)-AH*AH-BH*BH,
}
assert checks['left_downward_axis_gap'] == F(89,7440)
assert checks['horizontal_gap_oblique'] == F(19,1050)
assert checks['right_projection_square_root'] == F(43,19200)
assert checks['a_linear_lower_bound_polynomial'] == F(166,125)
assert all(v>0 for v in checks.values())
print(json.dumps({'result':'PASS','scope':'complete scalar audit for the companion original-square hand proof','positive_reserves':{k:str(v) for k,v in checks.items()}},indent=2))
