#!/usr/bin/env python3
"""Exact scalar checks for the original A/B tangent bound; no solver."""
from fractions import Fraction as F
import json

Q=F(1105,256)
radius_reserve=F(133,64)**2-Q
assert radius_reserve==F(9,4096)>0
assert F(133,64)-F(3,2)==F(37,64)
angle_reserve=1504**2-37**2*1649
assert angle_reserve==4535>0
assert 1649==40**2+7**2 and 47==40+7 and 1504==47*32
print(json.dumps({'claim':'original A/B |tan(theta)|<7/40',
                  'status':'PASS','radius_squared_reserve':str(radius_reserve),
                  'angle_squared_integer_reserve':angle_reserve,
                  'whole_mask_closed':False},indent=2))
