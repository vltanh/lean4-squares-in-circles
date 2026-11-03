#!/usr/bin/env python3
"""Exact constants for the DG inset and C slant hand reduction.

This proves the printed rational comparisons, not the separate slant theorem.
"""
from fractions import Fraction as F
import json
Q=F(1105,256);rho=F(91,60);K=F(3187,1728)
rows=[]
def pos(name,x,expected=None):
    if expected is not None:assert x==expected
    assert x>0
    rows.append({'name':name,'reserve':str(x)})
assert K==F(133,64)-F(101,432)
pos('forward inset overlap',2-K,F(269,1728))
pos('reverse horizontal gap versus universal inset sum',F(1,2)-F(11,60)**2)
pos('C horizontal upper endpoint',(F(4,5)-F(5,64))**2-F(1,2),F(2161,102400))
assert rho-F(7,32)==F(623,480)
pos('C height from slant',F(7,32)+F(7,8)*F(29,60)-F(5,8),F(1,60))
for p,ww,res in [(F(29,60),F(7,8),F(11,14400)),(F(4,5),F(287,480),F(23,9216))]:
    w=rho-F(7,32)-F(7,8)*p
    assert w==ww
    pos('bottom circle endpoint '+str(p),1-p*p-w*w,res)
pos('rightward further-original radius contradiction',F(89,60)**2+F(5,8)**2-rho*rho,F(93,320))
pos('slant threshold reserve at aligned limiting triple',-F(7,32)-(-F(11,16)+F(7,8)*F(1,2)),F(1,32))
print(json.dumps({'status':'PASS','scope':'Exact arithmetic only; separate slant theorem still required.','checks':rows},indent=2))
