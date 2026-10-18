#!/usr/bin/env python3
"""Exact arithmetic audit of HUMAN_S3_K3_SMALL_UPPER_FORBIDDEN.md.

Verifies the displayed rational and radical endpoint comparisons;
the all-frame geometric reasoning is in the Markdown hand proof.
This is NOT a global n=8 classifier or Lean formalization.
"""
from fractions import Fraction as F

x=F(311,500)
tan_poly=x+x**3/3+2*x**5/15
assert tan_poly-F(357,500)==F(147034397551,234375000000000)>0
assert F(177,250)**2>F(1,2)
Y=F(23,200)+F(177,250)
assert Y==F(823,1000)
X=Y/F(357,500)-F(117,200)
assert X==F(40531,71400)>F(1,2)
margin=1-X**2-Y**2
assert margin==F(27523627,63724500000)>0
assert F(11,21)<x
assert F(8959,10500)<1
print("PASS: S3/k3 small-upper exact rational gate")
