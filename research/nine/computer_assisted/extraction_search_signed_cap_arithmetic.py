#!/usr/bin/env python3
"""Exact rational comparisons for the signed-cap independent hand proof.

This checks arithmetic only. The manuscript's concavity and monotonicity
arguments are the continuous-domain proof; no numerical grid is evidence.
"""
from fractions import Fraction as F
import json

a,b,k,T=F(46),F(27,2),F(207,16),F(211,4)
checks={}
def positive(name,value,expected=None):
    assert value>0,(name,value)
    if expected is not None: assert value==expected,(name,value,expected)
    checks[name]=str(value)

positive('signed_penalty_nonnegative_coefficient',a/2-k)
positive('radius_133_64',(F(133,64))**2-F(1105,256))
positive('radius_25_12',(F(25,12))**2-F(1105,256))
positive('positive_arc_F1_slope',F(23,48)**2+2*F(23,48)-1)
positive('L_b_small_above_18',b*b+k*k-2*b*k/F(16)-18**2,F(243,64))
positive('L_b_small_below_19',19**2-(b*b+k*k),F(2911,256))
positive('small_arc_s_above_99_100',1-F(1,16)**2-F(99,100)**2)
positive('small_arc_D_reserve',18+b*k*F(99,100)/19-b-k,F(40311,60800))
positive('5_7_above_1_sqrt2',F(5,7)**2-F(1,2))
positive('large_arc_s_above_69_100',1-F(5,7)**2-F(69,100)**2)
positive('AMGM_left_root_reserve',b*k*F(99,100)-F(657,50)**2,F(20007,80000))
positive('AMGM_left_endpoint',2*F(657,50)+k/F(32)-b-k,F(3159,12800))
positive('AMGM_right_root_reserve',b*k*F(69,100)-F(439,40)**2,F(199,3200))
positive('AMGM_right_endpoint',2*F(439,40)+k*F(5,14)-b-k,F(149,1120))
hprime=F(133,64)*k*(a/(a-k)-b/(b+k))
assert hprime==F(142443,6016)
positive('negative_arc_tangent_slope',24-hprime)
positive('negative_arc_base_reserve',T+a+b+k-F(133,64)*(a+b),F(197,128))
positive('negative_arc_L_above_24',b*b+k*k+2*b*k*F(7,10)-24**2,F(23229,1280))
positive('negative_arc_L_derivative_below_8',8-b*k/24)
assert b*k/(b+k)==F(621,94)
positive('negative_arc_L_reciprocal_above_6',b*k/(b+k)-6)
positive('negative_arc_E_coefficient',(3*k-24)/2)
positive('negative_arc_N_coefficient',b/2+k-12)
positive('negative_arc_D_coefficient',k-10)
positive('1_sqrt2_above_7_10',F(1,2)-F(7,10)**2)
positive('negative45_positive_arc_end',(b+k/2)*F(7,10)-b,F(153,320))
positive('k_sq_below_168',168-k*k)
assert a*b==621
assert 1+F(168,621)==F(263,207)
positive('Cauchy_radical_bound',F(336,5)**2-(a+b)**2*F(263,207),F(369313,20700))
assert F(25,12)*F(336,5)==140
positive('negative45_middle_left_above_89',a+2*k+(b+k)*F(7,10)-89,F(221,160))
positive('sqrt47_above_34_5',47-F(34,5)**2)
positive('negative45_middle_right_above_89',a+k+k*F(35,12)*F(7,10)+b*F(34,5)/24-89,F(113,640))
positive('negative45_middle_reserve',T+89-140,F(7,4))
positive('negative45_final_arc_reserve',T-F(13,12)*(a+3*b/2)+F(7,10)*k*F(35,12),F(2839,384))
print(json.dumps({'status':'PASS','scope':'Exact rational comparisons only; continuous proof in manuscript.','checks':checks},indent=2))
