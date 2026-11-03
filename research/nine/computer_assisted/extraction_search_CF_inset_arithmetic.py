#!/usr/bin/env python3
"""Exact constants for the original C/F inset vertical hand proof."""
from fractions import Fraction as F
import json

Q=F(1105,256)
kappa=F(92,27)
lam=1+kappa
assert lam==F(119,27)
assert F(46)/F(27,2)==kappa
assert F(211,4)==46+F(27,4)
assert lam*(F(133,64)-1)-F(1,2)==F(2449,576)
assert lam*lam-1==F(13432,729)
rows=[]
def positive(name,value,expected):
    assert value==expected and value>0
    rows.append({'name':name,'reserve':str(value)})
positive('radius upper bound',F(133,64)**2-Q,F(9,4096))
positive('unbuffered AMGM square comparison',
         F(13432,729)-F(2449,576)**2,F(1039063,2985984))
positive('one twenty-fifth horizontal reserve',
         F(13432,729)-(F(2449,576)+F(1,25))**2,
         F(11647591,1866240000))
assert F(91,60)-1==F(31,60)
assert F(1,2)-F(1,60)==F(29,60)
assert F(31,60)-F(29,60)==F(1,30)
positive('reverse horizontal gap with same reserve',
         F(1,2)-(F(1,30)+F(1,25))**2,F(11129,22500))
positive('vertical inset gap above seven tenths',F(1,2)-F(7,10)**2,F(1,100))
print(json.dumps({'status':'PASS','scope':'Exact hand-proof arithmetic; no new finite forest.',
                  'whole_mask_closed':False,'checks':rows},indent=2))
