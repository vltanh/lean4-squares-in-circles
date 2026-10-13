#!/usr/bin/env python3
"""Exact rational margin audit for excluded negative S3/k3 outer ray."""
from fractions import Fraction as F
assert F(2041,10500)>F(19,100)
assert F(25,36)>F(69,100)
x=F(22,25)
cosupper=1-x*x/2+x**4/24
assert F(13,20)-cosupper==F(57247,4687500)>0
assert F(117,200)/F(13,20)==F(9,10)
x=F(77,100)
coslower=1-x*x/2+x**4/24-x**6/720
assert coslower-F(143,200)==F(2093489919911,720000000000000)>0
corners=[r*r+s*s-F(143,100)*r*s for r in (F(9,10),F(1)) for s in (F(1),F(283,200))]
assert corners==[F(523,1000),F(12389,12500),F(57,100),F(39151,40000)]
assert max(corners)<1
x=F(24,25)
cosupper=1-x*x/2+x**4/24
assert F(117,200)-cosupper==F(32533,3125000)>0
print('PASS: all S3/k3 negative outer-ray exclusion rational margins')
