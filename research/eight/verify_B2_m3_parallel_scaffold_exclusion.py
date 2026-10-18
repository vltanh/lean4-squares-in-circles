#!/usr/bin/env python3
"""Exact symbolic/rational audit of the m3 positive-stress parallel scaffold exclusion.

The hand theorem forces all four frames parallel and both endpoint
forces horizontal. With positive circle-vertex multipliers, both
endpoint centers then have zero transverse coordinate. This script
checks only the remaining two exact circle equations and area
contradiction, not those physical-geometric hypotheses.
"""
from fractions import Fraction as F

# c is the central square's horizontal center coordinate.
# A and B have horizontal centers c-1 and c+1 respectively.
# Their farthest true vertices have squared norms
#   (c-3/2)^2+1/4 and (c+3/2)^2+1/4.
# Equality of squared norms gives -6c=0.
f=lambda c: (c-F(3,2))**2+F(1,4)
g=lambda c: (c+F(3,2))**2+F(1,4)
for c in [F(-2,5),F(0),F(1,8),F(3,7)]:
    assert f(c)-g(c)==-6*c
assert f(F(0))==g(F(0))==F(5,2)
# For 8 disjoint unit squares, disk area pi R^2 >= 8;
# pi <22/7 implies R^2 > 8/(22/7) =28/11 >5/2.
assert F(8)/(F(22,7))==F(28,11)
assert F(28,11)-F(5,2)==F(1,22)>0
print("PASS: four-parallel m3 force scaffold would have R^2=5/2 < 28/11")
