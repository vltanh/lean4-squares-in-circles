#!/usr/bin/env python3
"""Exact rational rotated-square cap envelope counterexample at h=3/10."""
from fractions import Fraction as F
h=F(3,10);y=F(99,100);c=F(8319,11681);s=F(8200,11681)
assert c*c+s*s==1
p=(h+(c+s)/2,y)
assert p==(F(58819,58405),y)
verts=[(p[0]+F(i*c-j*s,2),p[1]+F(i*s+j*c,2))
       for i in (-1,1) for j in (-1,1)]
assert min(x for x,_ in verts)==h
ns=[x*x+t*t for x,t in verts]
assert max(ns)==F(5332904348861,1364457610000)
q=F(9789,2500)
axis=(1+h)**2+(y+F(1,2))**2
assert axis==F(39101,10000)
assert q-max(ns)==F(1953173771,272891522000)>0
assert axis-max(ns)==F(1130676,682228805)>0
assert h>F(7,24)
print('PASS: exact rational true-square cap-envelope counterexample at h=3/10')
