#!/usr/bin/env python3
"""Exact new scalar comparisons for the negative-D v<=2/3 hand theorem."""
from fractions import Fraction as F
import json

T=F(13,40);V=F(2,3)
assert T*V==F(13,60)
assert 1+T*T==F(1769,1600)
assert 2+T+T*T==F(3889,1600)
assert F(2011,960)+F(13,60)==F(2219,960)
normal_reserve=93336**2-2219**2*1769
assert 93336==3889*24 and normal_reserve==1121887>0
assert F(1,2)>V*V
assert T/2-F(2,23)==F(139,1840)
assert T/2-F(139,1840)==F(2,23)
assert F(673,16)**2-1769==F(65,256)>0
assert 2-F(24,17)**2==F(2,289)>0
endpoint_reserve=F(3889,3365)-F(13,60)+F(24,391)-1
assert endpoint_reserve==F(6869,15788580)>0
print(json.dumps({'claim':'negative-D original001/00 exclusion for v<=2/3',
                  'status':'PASS','normal_squared_integer_reserve':normal_reserve,
                  'transfer_endpoint_rational_reserve':str(endpoint_reserve),
                  'whole_mask_closed':False},indent=2))
