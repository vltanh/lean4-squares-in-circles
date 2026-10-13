#!/usr/bin/env python3
"""Rational replay of RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md.

This verifies actual square frames, ALL eight true disk vertices, both
whole-cap projection minima, and a positive genuine separating-axis gap.
Not a proof of the global n=8 problem.
"""
from fractions import Fraction as F

h = F(7,24)+F(1,500)
q_ceiling = F(9789,2500)
p = (F(1,1000),F(11,8))
u = (F(249,250),F(2381,3000))
ep = (F(399,401),F(-40,401))
fp = (F(40,401),F(399,401))
eu = (F(1),F(0))
fu = (F(0),F(1))

dot = lambda a,b: a[0]*b[0]+a[1]*b[1]
assert dot(ep,ep)==dot(fp,fp)==1
assert dot(ep,fp)==0
assert h == F(881,3000)
assert p[0]>0 and u[0]>0

def vertices(p,e,f):
    return [(p[0]+(i*e[0]+j*f[0])/2,p[1]+(i*e[1]+j*f[1])/2)
            for i in (-1,1) for j in (-1,1)]

vp=vertices(p,ep,fp)
vq=vertices(u,eu,fu)
assert len(vp)==len(vq)==4
assert min(z[1] for z in vp)==F(2655,3208)
assert min(z[1] for z in vq)==h
assert min(z[1] for z in vp)-h == F(80293,150375)>0

center_delta=(u[0]-p[0],u[1]-p[1])
gap=dot(ep,center_delta)-F(1,2)-(abs(dot(ep,eu))+abs(dot(ep,fu)))/2
assert gap==F(31,48120)>0

max_P=max(dot(v,v) for v in vp)
max_Q=max(dot(v,v) for v in vq)
assert max_P==F(780953513,200500000)
assert max_Q==F(7040861,1800000)
assert q_ceiling-max_P==F(4124287,200500000)>0
assert q_ceiling-max_Q==F(7219,1800000)>0
assert max_Q>max_P

print("PASS: 2 true unit-square frames, 8 exact disk vertices, "
      "positive strict same-sign cap, genuine SAT gap")
