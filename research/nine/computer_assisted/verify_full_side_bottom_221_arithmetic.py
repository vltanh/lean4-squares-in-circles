"""Exact arithmetic audit of the two remaining scalar comparisons in the
complete full-side-bottom (2,2,1) hand caller. All other scalar/table inputs
have their named companion checkers; this script does not rerun them.
"""
from fractions import Fraction as F
import json
l,rho=F(29,60),F(91,60)
assert l-F(1,3) == F(3,20)
assert rho-F(3,5)-F(15,31) == F(161,372)
checks={
 'two_lower_central_original_disk_overlap':1-F(3,20)**2-F(161,372)**2,
 'positive_half_central_width':F(1,2)-l,
 'replacement_floor_above_one_tenth':F(2807,24000)-F(1,10),
}
assert all(v>0 for v in checks.values())
print(json.dumps({'result':'PASS','positive_reserves':{k:str(v) for k,v in checks.items()}},indent=2))
