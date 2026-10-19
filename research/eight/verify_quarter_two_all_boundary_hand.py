"""Exact replay of the finite comparisons in the full jump-two hand row."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


def atan_partial(x,m):
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(m+1)),F(0))


def sin_partial(x,m):
    return sum(((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(m+1)),F(0))


def cos_partial(x,m):
    return sum(((-1)**j*x**(2*j)/factorial(2*j) for j in range(m+1)),F(0))


Q,p,q,K,h=F(9789,2500),F(13,200),F(203,200),F(73,10),F(291,250)
gamma=F(163,200)
pi_lower=16*atan_partial(F(1,5),5)-4*atan_partial(F(1,239),2)
assert pi_lower>F(6283,2000)
assert (F(141,100)+F(1,2))**2<Q-F(1,4)<(F(283,200)+F(1,2))**2
assert (F(9,10)+F(1,2))**2>Q/2
assert F(6,5)**2<2<F(36,25)**2
assert F(707,500)**2<2
core_upper=K*(F(7,12)-F(6707,12000))+h*F(6707,12000)
assert core_upper==F(1243231,1500000)<F(83,100)
assert -F(9,100)+p*F(141,100)>0
assert -F(9,100)+(p+q)*F(9,10)==F(441,500)
assert F(13,5)<5*F(6283,2000)/6
assert 1-F(7,10)**2/2>F(3,4)
assert F(7,4)**2>3
assert sin_partial(F(7,10),2)<F(13,20)
assert F(57,40)**2>2
assert F(2,5)*F(57,40)-F(1,2)==F(7,100)
assert h*F(7,100)<F(41,500)
assert -F(9,100)+p*F(283,200)+q*F(7,100)<F(41,500)
assert F(85,144)<F(16,25)
assert F(43,30)**2>2
assert F(1,6)-F(1,4)<0
B_upper=(F(1,12)+F(13,10)*F(7,8)-F(1,4))/F(5,4)
assert B_upper==F(233,300)<F(39,50)
outer_clipped_upper=-F(9,100)+p*F(9,5)+(q-p)*F(39,50)
assert outer_clipped_upper==F(96,125)
assert K-1>0 and F(13,20)-h<0
derivative_lower=1-F(3,50)*F(13,20)-F(53,50)*F(7,8)
assert derivative_lower==F(67,2000)>0
assert Q*((p+1)**2+q*q)<F(73,25)**2
assert sin_partial(F(7,10),3)>F(644,1000)
assert cos_partial(F(7,10),4)<F(765,1000)
base_phi_lower=F(6283,2000)-F(7,10)
costs={
 'nonnegative_marker_sign_pattern':base_phi_lower-F(441,500),
 'angle_at_least_thirteen_fifths':F(13,5)-2*F(441,500),
 'source_secondary_target_outer':base_phi_lower-F(41,500)-F(441,500),
 'source_negative_primary_core_outer':base_phi_lower-F(83,100)-F(96,125),
 'source_negative_primary_outer_core':base_phi_lower+F(163,100)-F(83,100)-F(73,25)
   -F(3,50)*F(765,1000)+F(21,20)*F(644,1000),
}
expected=[F(3119,2000),F(209,250),F(591,400),F(1687,2000),F(4759,5000)]
for (name,value),want in zip(costs.items(),expected):
    assert value==want>gamma
    print(name,value,'strict reserve',value-gamma)
out={'status':'PASS','scope':'all C/O signed jump-two source-axis branches',
     'core_label_upper':str(core_upper),'core_outer_target_B_upper':str(B_upper),
     'outer_core_derivative_lower':str(derivative_lower),
     'cost_bounds':{name:str(value) for name,value in costs.items()},
     'critical_outer_outer_dependency':'JUMP_TWO_OUTER_OPPOSITE_HAND_PROOF.md',
     'ring_axis_dependency':'cap and common-point backward-axis exclusion'}
Path(__file__).with_name('quarter_two_all_boundary_hand_arithmetic.json').write_text(
    json.dumps(out,indent=2)+'\n')
print('PASS: complete finite jump-two hand cover arithmetic.')
