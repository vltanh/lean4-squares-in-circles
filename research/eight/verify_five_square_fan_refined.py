#!/usr/bin/env python3
"""Exact rational audit of refined five-square fan (not an n=8 proof oracle)."""
from fractions import Fraction as F
x=F(311,500)
cos6=1-x*x/2+x**4/24-x**6/720
assert cos6-F(13,16)==F(2409818510486639,11250000000000000000)>0
# Corner center-distance bounds for r>=117/200, s<=283/200.
vals=[r*r+s*s-F(13,8)*r*s for r in (F(117,200), F(1)) for s in (F(1),F(283,200))]
assert vals==[F(979,2500), F(319781,320000), F(3,8),F(14057,20000)]
assert max(vals)<1
T=F(88,63)-x
assert T==F(24407,31500)
assert F(31,40)-T==F(11,63000)>0
z=F(31,40)
sin5=z-z**3/6+z**5/120
assert F(7,10)-sin5==F(3082849,12288000000)>0
assert (F(33,40)**2)-(F(1689,2500))==F(201,40000)>0
assert (F(117,200)/F(3,4))>F(7,10)
print('PASS: refined five-square fan rational margin checks')
