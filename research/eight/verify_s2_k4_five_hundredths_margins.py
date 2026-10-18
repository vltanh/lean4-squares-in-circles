#!/usr/bin/env python3
"""Exact rational audit of high-cap polar and S2/k4 mixed-center margins.

These are arithmetic endpoint comparisons, not a sampled proof or Lean theorem.
The accompanying analytic argument justifies their continuous application.
"""
from fractions import Fraction as F

q_plus = F(9789,2500)
r_outer = F(283,200)
assert r_outer**2+r_outer+F(1,2)-q_plus == F(65,40000)
# sqrt3<7/4 and the far-side one-square envelope yield elevation >pi/3.
assert F(7,4)**2>3
assert (F(13,8)**2+F(8,7)**2)-q_plus == F(61049,1960000)>0
# The smaller of the two upper outer gaps is less than M.
# Using pi<22/7, M=13*pi/36+1/250 <57/50.
M=F(13,36)*F(22,7)+F(1,250)
assert M == F(8969,7875)
assert F(57,50)-M == F(17,15750)>0
# With r>=11/20 and outer s<=283/200, angular gap exceeds .57.
x=F(57,100)
c_bound=1-x*x/2+x**4/24-x**6/720
assert c_bound-F(21,25)==F(152055983639,80000000000000)>0
corners = [r*r+s*s-2*F(21,25)*r*s for r in (F(11,20), F(1)) for s in (F(1),r_outer)]
assert corners == [F(757,2000),F(199453,200000),F(8,25),F(25001,40000)]
assert all(x<1 for x in corners)
assert x>F(22,7)/6+F(3,500)
print('PASS: all rational far-cap and mixed-center margins')
