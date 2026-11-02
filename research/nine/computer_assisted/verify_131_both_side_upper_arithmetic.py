"""Exact rational arithmetic audit of the complete 131 both-side-upper
hand caller and its two elementary center-disk lemmas. No Lean or CI.
"""
from fractions import Fraction as F
import json
l,u,rho=F(29,60),F(13,12),F(91,60)
A,c=F(503,480),F(221,600);f=F(119,310)
V,H=F(23,60),F(97,120)
proxy_top=F(2,5)+F(15,31)-F(1,72)
assert -F(9,10)+F(59,60)==F(1,12)
assert H-F(1,12)==F(29,40)
assert l+F(1,5)==F(41,60)
assert u-F(1,5)==F(53,60)
assert l-F(1,5)==F(17,60)
assert f-(F(15,31)+F(1,2))==-F(3,5)
assert -V+F(59,60)==F(3,5)
assert -V+F(15,31)==F(1,10)+F(1,1860)
assert F(7,20)+F(11,20)==F(9,10)
assert F(7,20)+F(243,400)==F(383,400)
assert F(3,5)-V==F(13,60)
assert H-F(3,5)==F(5,24)
assert F(7,20)-F(1,60)==F(1,3)
assert proxy_top==F(9709,11160)
checks={
 'both_side_low_cone_span':2-F(49,40)**2,
 'low_side_strips_cover_central':F(49,80)-l,
 'high_side_bad_central_lower_order':1-F(53,60)**2-F(5,24)**2,
 'high_side_bad_central_left_arc':1-F(17,60)**2-F(21,25)**2,
 'high_side_bad_central_right_arc':1-F(53,60)**2-F(37,80)**2,
 'high_side_left_arc_root':F(36,25)**2-(rho*rho-l*l),
 'high_side_right_arc_root':F(17,16)**2-(rho*rho-u*u),
 'both_bad_upper_central_disk':1-F(41,60)**2-F(29,40)**2,
 'low_side_near_main_overlap':F(15,31)-F(31,240),
 'low_side_main_below_23_60':f-F(23,60),
 'verylow_side_is_zero':F(7,16)-f,
 'verylow_side_upper_central_above_v0':F(3,5)-F(223,372),
 'verylow_opposite_main_proxy_top':F(1,1860),
 'moderate_helper_above_endpoint_band':f-c,
 'moderate_helper_left_profile_endpoint':F(1,4)-(f-c)**2-(A-F(11,20))**2,
 'moderate_helper_right_profile_endpoint':F(1,4)-(F(3,5)-c)**2-(A-F(243,400))**2,
 'moderate_helper_F_below_band_endpoint':f-V,
 'moderate_helper_first_vertical_choice':(H-f)-(f-V),
 'moderate_helper_second_vertical_choice':F(13,60)-F(5,24),
 'moderate_helper_small_X_left_disk':1-F(9,10)**2-(H-f)**2,
 'moderate_helper_small_X_right_disk':1-F(383,400)**2-F(13,60)**2,
 'inset_halfwidth_above_7_20':F(1,8)-F(7,20)**2,
 'own_loss_delta_below_1_60':F(1,60)-F(331,20000),
 'raised_proxy_top':proxy_top-F(869,1000),
 'high_side_above_F_order':1-F(11,15)**2-F(5,24)**2,
 'physical_halfwidth_upper':F(17,24)**2-F(1,2),
}
assert checks['both_bad_upper_central_disk']==F(107,14400)
assert all(v>0 for v in checks.values())
print(json.dumps({'result':'PASS','positive_reserves':{k:str(v) for k,v in checks.items()}},indent=2))
