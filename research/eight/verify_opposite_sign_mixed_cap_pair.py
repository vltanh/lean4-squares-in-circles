#!/usr/bin/env python3
"""Exact true-vertex replay of RATIONAL_OPPOSITE_SIGN_MIXED_CAP_PAIR.md.

A two-square geometric witness, not an eight-square configuration.
"""
from fractions import Fraction as F
from itertools import product

h=F(2,5)
p=(-F(3,10),F(9,10))
q=(F(4,5),F(9,10))
ep=(F(1),F(0)); fp=(F(0),F(1))
def vertices(x):
    return [(x[0]+F(a,2),x[1]+F(b,2))
            for a,b in product((-1,1),repeat=2)]
norm2=lambda v:v[0]**2+v[1]**2
vp,vq=vertices(p),vertices(q)
assert len(vp)==len(vq)==4
assert min(v[1] for v in vp)==h==min(v[1] for v in vq)
assert p[0]<0<q[0]
assert norm2(p)==F(9,10)<1<norm2(q)==F(29,20)
assert q[0]-p[0]-1==F(1,10)>0
assert max(norm2(v) for v in vp)==F(13,5)
assert max(norm2(v) for v in vq)==F(73,20)
assert F(9789,2500)-F(73,20)==F(166,625)>0
print("PASS: 2 true squares, 8 disk vertices, whole cap and strict SAT gap")
