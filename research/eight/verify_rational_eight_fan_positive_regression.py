#!/usr/bin/env python3
"""EXACT positive regression for the global rational SAT owner cone checks.

Reconstructs the eight genuine rational unit squares A,B,C,D,E,T,H,G
of ANALYTIC_RATIONAL_CONSTRUCTION.md; verifies all 32 TRUE
disk vertices and all 28 SPECIFIED signed SAT owner projections
(never substitutes a different owner). Finally verifies the
owner-cycle/DAG checker does not spuriously reject this REAL packing.

Usage:
 python verify_rational_eight_fan_positive_regression.py \
    rational_eight_feasible_owner_word.json
"""
import json,sys
from fractions import Fraction as F
from itertools import product
from verify_rational_fan_sat_owner_word import frames,dot,check

r=F(1753659,1000000)
U=F(331179,200000)
u=F(11,12)
v=F(547767,1000000)
w=F(95073,50000)
c=F(255,257)
s=F(32,257)
h1=c*r-s*u-2-c
h2=s*w-c*v-1-s
P5=(h1*c-h2*s,h1*s+h2*c)
pH=(P5[0]+(c-s)/2,P5[1]+(s+c)/2)
centers=[
 (r-F(1,2),F(1,2)-u),
 (U-F(1,2),F(3,2)-u),
 (U-F(3,2),F(7,20)),
 (U-F(5,2),F(3,2)-v),
 (F(1,2)-w,F(1,2)-v),
 (U-F(3,2),F(27,20)),
 pH,
 (pH[0]+c,pH[1]+s)
]
with open(sys.argv[1]) as fd:cert=json.load(fd)
assert cert["frame_half_tangents"]==["0"]*6+["1/16"]*2
ef=frames(cert["frame_half_tangents"])
qplus=F(9789,2500)
assert len(ef)==len(centers)==8
for i,p in enumerate(centers):
    e,f=ef[i]
    for a,b in product((-1,1),repeat=2):
        vert=(p[0]+(a*e[0]+b*f[0])/2,
              p[1]+(a*e[1]+b*f[1])/2)
        assert dot(vert,vert)<=qplus,("vertex outside disk",i,a,b)

word=cert["owner_word"]
assert len(word)==28
pairs=set()
for i,j,owner,axis,sign in word:
    assert i<j and owner in (i,j) and (i,j) not in pairs
    pairs.add((i,j))
    n=ef[owner][0 if axis=="e" else 1]
    n=(sign*n[0],sign*n[1])
    difference=(centers[j][0]-centers[i][0],
                centers[j][1]-centers[i][1])
    H=lambda t:(abs(dot(n,ef[t][0]))+
                abs(dot(n,ef[t][1])))/2
    assert dot(n,difference)-H(i)-H(j)>=0,(
        "not a TRUE directed SAT owner",i,j)
assert len(pairs)==28
assert not check(cert)
print("PASS: all 8 genuine rational squares and 32 true disk vertices")
print("PASS: ALL 28 SELECTED true directed pair SAT normals")
print("PASS: all owner-cycle pruning tests correctly retain the packing")
