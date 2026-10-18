#!/usr/bin/env python3
"""Exact fraction audit for HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md.

Checks the non-overlap cap center contradiction and true leaf
radial side-offset lower bound. The hand theorem, not this script,
proves the physical stress/leaf-normal structural reduction.
"""
from fractions import Fraction as F

q=F(9789,2500)
r0=F(283,200)

# Whole-square cap h>=4/5 has center transverse |x|<1/3
# and normal center y in [13/10,283/200).
assert F(5,6)**2-(q-F(9,5)**2)==F(106,5625)>0
assert r0-F(13,10)==F(23,200)>0

distance_upper=F(2,3)**2+F(23,200)**2
assert distance_upper==F(164761,360000)<1
assert 1-distance_upper==F(195239,360000)>0

# An actual leaf of a least-radius 8-square packing has
# b=sqrt(R^2-1/4)-1. The lower bound
# R>sqrt(2)+1/2 implies b>4/5.
assert F(31,25)**2<2
assert 2+F(31,25)==F(81,25)==F(9,5)**2

print("PASS: high-cap two-square contradiction and leaf-side offset b>4/5")
