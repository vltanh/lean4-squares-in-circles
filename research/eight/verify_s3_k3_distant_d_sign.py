#!/usr/bin/env python3
"""Exact rational margin audit for S3/k3 distant D center sign theorem."""
from fractions import Fraction as F
assert (F(8959,10500)-F(311,500)-F(157,150)) == -F(1427,1750)
assert F(1427,1750)-F(163,200)==F(3,7000)>0
z=F(163,200)
cu=1-z*z/2+z**4/24
assert F(117,170)-cu==F(1282540063,652800000000)>0
x=F(77,100)
cl=1-x*x/2+x**4/24-x**6/720
assert cl-F(717,1000)==F(653489919911,720000000000000)>0
v=[r*r+s*s-F(717,500)*r*s for r in [F(17,20),F(1)] for s in [F(1),F(283,200)]]
assert v==[F(1259,2500),F(1999963,2000000),F(283,500),F(194623,200000)]
assert max(v)<1
assert F(77,100)+F(163,200)-F(11,7)==F(19,1400)>0
assert F(1427,1750)+F(77,100)-F(11,7)==F(7,500)>0
assert F(13,10)*F(7,500)-F(9,500)==F(1,5000)>0
print('PASS: exact S3/k3 far-D negative-x margins')
