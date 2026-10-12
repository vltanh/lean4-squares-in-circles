#!/usr/bin/env python3
"""Exact verifier for RATIONAL_PERPENDICULAR_CAP_COUNTEREXAMPLE.md.

No floating-point input, no black-box optimizer, and no claimed eight-square proof.
Verifies 20 actual vertex radii and all 10 pairwise nonoverlap certificates.
"""
from fractions import Fraction as F

Q = F(3911, 1000)
c, s = F(2499, 2501), F(100, 2501)
assert c*c + s*s == 1

sq = {
    "C": ((F(-49,100), F(-2,5)), (F(1),F(0)), (F(0),F(1))),
    "B": ((F(49,50), F(-161,200)), (c,s),(-s,c)),
    "M": ((F(51,100), F(1,5)), (F(1),F(0)), (F(0),F(1))),
    "T": ((F(51,100), F(6,5)), (F(1),F(0)), (F(0),F(1))),
    "D": ((F(-1,50), F(-7,5)), (F(1),F(0)), (F(0),F(1))),
}
dot = lambda v, w: v[0]*w[0]+v[1]*w[1]

def vertices(k):
    p,e,f = sq[k]
    return [
        (p[0]+F(i*e[0]+j*f[0],2),p[1]+F(i*e[1]+j*f[1],2))
        for i in [-1,1] for j in [-1,1]
    ]

expected_radius = {
    "C": F(17901,10000),
    "B": F(390055437,100040000),
    "M": F(15101,10000),
    "T": F(39101,10000),
    "D": F(9701,2500),
}
for k in sq:
    v = max(dot(z,z) for z in vertices(k))
    assert v == expected_radius[k], (k,v,expected_radius[k])
    assert v < Q, (k,v)
assert Q - expected_radius["T"] == F(9,10000)
assert Q - expected_radius["B"] == F(1201003,100040000)

def half_support(k, n):
    _,e,f = sq[k]
    return (abs(dot(n,e))+abs(dot(n,f)))/2

def separation(k, l, n):
    p=sq[k][0];q=sq[l][0]
    delta=(q[0]-p[0], q[1]-p[1])
    return abs(dot(n,delta))-half_support(k,n)-half_support(l,n)

cert = {
    ("C","B"): (F(1),F(0)),
    ("C","M"): (F(1),F(0)),
    ("C","T"): (F(1),F(0)),
    ("C","D"): (F(0),F(1)),
    ("B","M"): sq["B"][2],
    ("B","T"): sq["B"][2],
    ("B","D"): sq["B"][1],
    ("M","T"): (F(0),F(1)),
    ("M","D"): (F(0),F(1)),
    ("T","D"): (F(0),F(1)),
}
expected_outer_gaps = {
    ("B","M"):F(1699,500200),
    ("B","T"):F(501499,500200),
    ("B","D"):F(17,5002),
    ("M","T"):F(0),
    ("M","D"):F(3,5),
    ("T","D"):F(8,5),
}
assert len(cert)==10
for (i,j),n in cert.items():
    gap=separation(i,j,n)
    assert gap>=0,(i,j,gap)
    if (i,j) in expected_outer_gaps:
        assert gap == expected_outer_gaps[(i,j)], (i,j,gap)
assert min(z[0] for z in vertices("M")) == F(1,100)
assert min(z[0] for z in vertices("T")) == F(1,100)
assert min(z[0] for z in vertices("B")) > F(1,100)
assert max(z[1] for z in vertices("D")) == F(-9,10)
assert min(z[1] for z in vertices("T")) == F(7,10) > F(1,10)
print("PASS: 5 rational squares, 20 disk vertices, all 10 separating axes, true RU double")
