"""Exact rational arithmetic audit of the complete normalized (1,4,0)
three-upper/one-lower central caller. No Lean or CI.
"""
from fractions import Fraction as F
import json
l,u,rho=F(29,60),F(13,12),F(91,60)
assert F(3,5)-F(59,60)==-F(23,60)
assert -F(3,5)+F(59,60)==F(23,60)
assert F(3,5)-F(23,60)==F(13,60)
assert -F(139,120)+F(59,60)==-F(7,40)
assert F(3,5)+F(7,40)==F(31,40)
assert l-F(7,10)==-F(13,60)
assert l-F(7,5)==-F(11,12)
assert F(1,10)+F(17,24)==F(97,120)
assert F(97,120)-F(27,40)==F(2,15)
assert u-F(13,60)==F(13,15)
assert F(11,12)-F(13,60)==F(7,10)
assert rho*rho-F(11,12)**2==F(73,50)
assert rho*rho-u*u==F(169,150)
checks={
 'opposite_low_central_disk':1-(2*l)**2-F(13,60)**2,
 'same_half_low_central_disk':1-l*l-F(31,40)**2,
 'half_width_replacement_premise':F(1,2)-l,
 'half_width_replacement_floor':F(2807,24000)-F(1,10),
 'far_shoulder_below_P_disk':1-F(13,15)**2-F(2,15)**2,
 'far_shoulder_left_root':F(49,40)**2-F(73,50),
 'far_shoulder_right_root':F(17,16)**2-F(169,150),
 'far_shoulder_left_arc_endpoint':1-F(7,10)**2-F(5,8)**2,
 'far_shoulder_right_arc_endpoint':1-F(13,15)**2-F(37,80)**2,
 'square_halfwidth_upper':F(17,24)**2-F(1,2),
 'high_far_shoulder':F(27,40)-F(3,5),
}
assert checks['opposite_low_central_disk']==F(67,3600)
assert checks['far_shoulder_below_P_disk']==F(52,225)
assert checks['far_shoulder_left_arc_endpoint']==F(191,1600)
assert checks['far_shoulder_right_arc_endpoint']==F(403,11520)
assert all(v>0 for v in checks.values())
print(json.dumps({'result':'PASS','positive_reserves':{k:str(v) for k,v in checks.items()}},indent=2))
