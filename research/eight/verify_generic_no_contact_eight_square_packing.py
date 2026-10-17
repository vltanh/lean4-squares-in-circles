#!/usr/bin/env python3
"""Exact eight-unit-square counterexample to forced contacts or parallel frames
in the near-sharp radius sublevel (q <= 9789/2500).

No floating-point arithmetic or geometry package. Reconstructs the old
ANALYTIC_RATIONAL_CONSTRUCTION.md full EIGHT-unit-square packing, multiplies
each center by 1 + 10^-8 (frames not scaled), then applies distinct exact
Pythagorean rational rotations with half-angle tangent j / 10^12.

Checks:
  * all 8 true unit-square frames are orthonormal;
  * no two frames agree modulo 90 degrees (all different);
  * the origin lies in the interior of exactly one square;
  * all 32 true square vertices fit STRICTLY in q=9789/2500,
    with uniform squared-radius reserve > 1/2,000,000;
  * all 28 distinct square pairs are STRICTLY separated by
    some ACTUAL SAT-owner normal of a true square side,
    with uniform projected reserve > 9/1,000,000,000;
  * all 8 are genuine closed unit squares, and the resulting
    packing has no actual square-square contacts whatsoever.

IMPORTANT: q+ is slightly ABOVE the candidate optimum. This does
NOT disprove R8 >= Rhat, nor any *minimizer-only* contact theorem.
It disproves forced exact contacts/parallelism for ALL configurations
in the near-sharp q<=q+ feasible set.
"""
from fractions import Fraction as Q
from itertools import combinations

q_plus = Q(9789, 2500)
u = Q(11, 12)
r = Q(1753659, 1000000)
U = Q(331179, 200000)
v = Q(547767, 1000000)
w = Q(95073, 50000)
c = Q(255, 257)
s = Q(32, 257)
assert c*c + s*s == 1

h1 = c*r - s*u - 2 - c
h2 = s*w - c*v - 1 - s
P5 = (h1*c - h2*s, h1*s + h2*c)
e0 = (c, s)
f0 = (-s, c)
std_e = (Q(1), Q(0))
std_f = (Q(0), Q(1))

# Exact construction from ANALYTIC_RATIONAL_CONSTRUCTION.md.
base = [
    ("A", (r - Q(1, 2), Q(1, 2) - u), std_e, std_f),
    ("B", (U - Q(1, 2), Q(3, 2) - u), std_e, std_f),
    ("C", (U - Q(3, 2), Q(7, 20)), std_e, std_f),
    ("D", (U - Q(5, 2), Q(3, 2) - v), std_e, std_f),
    ("E", (Q(1, 2) - w, Q(1, 2) - v), std_e, std_f),
    ("T", (U - Q(3, 2), Q(27, 20)), std_e, std_f),
    ("H", (P5[0] + (c-s)/2, P5[1] + (s+c)/2), e0, f0),
    ("G", (P5[0] + (c-s)/2 + c, P5[1] + (s+c)/2 + s), e0, f0),
]
dot = lambda a,b: a[0]*b[0] + a[1]*b[1]
cross = lambda a,b: a[0]*b[1] - a[1]*b[0]
stretch = Q(1) + Q(1,10**8)
S = {}

for j, (name, p, e, f) in enumerate(base, start=1):
    # Independent, pairwise distinct rational rotations.
    t = Q(j, 10**12)   # EXACT half-angle tangent
    ct = (1-t*t)/(1+t*t)
    st = 2*t/(1+t*t)
    enew = (ct*e[0] + st*f[0], ct*e[1] + st*f[1])
    fnew = (-st*e[0] + ct*f[0], -st*e[1] + ct*f[1])
    pnew = (stretch*p[0], stretch*p[1])
    assert dot(enew,enew) == dot(fnew,fnew) == 1
    assert dot(enew,fnew) == 0
    S[name] = (pnew,enew,fnew)

def vertices(p,e,f):
    return [
        (p[0] + (i*e[0] + j*f[0])/2,
         p[1] + (i*e[1] + j*f[1])/2)
        for i in (-1,1) for j in (-1,1)
    ]

def halfwidth(n,e,f):
    return (abs(dot(n,e)) + abs(dot(n,f)))/2

squared_radius_reserves = []
central_labels = []
for name,(p,e,f) in S.items():
    is_central = abs(dot(p,e)) < Q(1,2) and abs(dot(p,f)) < Q(1,2)
    if is_central:
        central_labels.append(name)
    for vert in vertices(p,e,f):
        reserve = q_plus - dot(vert,vert)
        assert reserve > Q(1,2000000), (name, "vertex reserve")
        squared_radius_reserves.append((name,reserve))
assert central_labels == ["C"]

actual_sat_separating_reserves = []
for (name1,(p,e,f)),(name2,(p2,g,h)) in combinations(S.items(),2):
    diff = (p2[0]-p[0],p2[1]-p[1])
    axes = (e,f,g,h) # all 4 genuine pair SAT-owner axes
    gaps = [
        abs(dot(n,diff)) - halfwidth(n,e,f) - halfwidth(n,g,h)
        for n in axes
    ]
    maxgap = max(gaps)
    assert maxgap > Q(9,10**9), (name1,name2, "SAT reserve")
    actual_sat_separating_reserves.append((name1,name2,maxgap))

# The true unit-square frames have eight different orientations
# modulo 90 degrees. All off-diagonal cross and dot products
# of their e axes are nonzero.
for (_,(_,e,_)), (_,(_,g,_)) in combinations(S.items(),2):
    assert cross(e,g) != 0
    assert dot(e,g) != 0

assert len(squared_radius_reserves) == 32
assert len(actual_sat_separating_reserves) == 28
print("PASS: eight exact rational unit squares, all frames pairwise distinct")
print("PASS: all 32 true vertices strictly contained in q = 9789/2500")
print("PASS: uniform squared-radius reserve > 1/2,000,000")
print("PASS: all 28 genuine SAT pair gaps > 9/1,000,000,000")
print("PASS: origin inside exactly the designated central square C")
print("PASS: NO ACTUAL square-square contacts")
print("tightest vertex square:",
      min(squared_radius_reserves,key=lambda x:x[1])[0])
print("tightest square pair:",
      min(actual_sat_separating_reserves,key=lambda x:x[2])[:2])
