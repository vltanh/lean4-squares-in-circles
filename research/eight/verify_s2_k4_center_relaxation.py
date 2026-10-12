#!/usr/bin/env python3
"""Exact check of the S2/k4 CENTER-ONLY relaxation witness.

Important: it does not verify actual unit-square frames, disjointness,
or disk containment. It verifies only necessary center inequalities.
"""
from fractions import Fraction as F
from itertools import combinations

q=F(9789,2500)
hR=F(1,1000)
hU=F(293,1000)
hD=1-hU
raw=[
 ("R1","outer","1.11097","-0.87476"),
 ("R2","outer","1.32379","0.49704"),
 ("R3","inner","0.50311","-0.07805"),
 ("U1","inner","0.39160","0.91784"),
 ("U2","inner","-0.60297","0.79511"),
 ("D1","outer","-0.73315","-1.20911"),
 ("D2","outer","0.25226","-1.39134"),
 ("C","inner","-0.49900","-0.20700"),
]
coords={n:(F(x),F(y)) for n,_,x,y in raw}
assert coords["C"]==(hR-F(1,2),hU-F(1,2))
assert hR>0 and hU>F(7,24)
assert 4*(hU+F(1,2))**2<3   # hU < (sqrt(3)-1)/2

normsq={name:x*x+y*y for name,(x,y) in coords.items()}
for name,status,_,_ in raw:
 if status=="inner": assert normsq[name]<1, name
 else: assert normsq[name]>=1, name

all_pair_margins=[]
for i,j in combinations(coords,2):
 x,y=coords[i]
 a,b=coords[j]
 all_pair_margins.append((x-a)**2+(y-b)**2-1)
assert len(all_pair_margins)==28
assert min(all_pair_margins)==F(21156861,5000000000)>0

proj=[]
for name in ["R1","R2","R3"]:
 proj.append(coords[name][0]-(hR+F(1,2)))
for name in ["U1","U2"]:
 proj.append(coords[name][1]-(hU+F(1,2)))
for name in ["D1","D2"]:
 proj.append(-(hD+F(1,2))-coords[name][1])
assert min(proj)==F(211,100000)>0

for name,v in normsq.items():
 t=q-F(1,2)-v
 assert t>0 and t*t>v,(name,v,t*t-v)
assert 1-max(normsq[n] for n in ["R3","U1","U2","C"])>F(4,1000)
print("PASS: center-only necessary conditions; NOT a square packing")
