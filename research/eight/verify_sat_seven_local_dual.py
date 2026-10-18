#!/usr/bin/env python3
"""Exact rational interval audit of the 32 actual SAT-owner angle duals.

This verifies the strict arithmetic premises in
HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md.

The already isolated sharp q,y,z root is enclosed by the
10^-16 rational box in FIVE_CORNER_REDUCTION.md.
All operations below reuse the outward-rounded integer
fixed-point rational interval arithmetic and exact
positive adaptive dual of verify_adaptive_seven_square_dual.py.
No floating point solver, sampling, or approximate sign
test can accept a branch.

The geometric SAT completeness, Taylor remainder, and
sharp five-corner F>=0 are hand theorems in the cited notes.
"""
from itertools import product
from fractions import Fraction as F
from verify_adaptive_seven_square_dual import (
    I,q,y,z,c,s,x1,x2,x3,y3,y4,x4,h1,h2,
    mA,mB,mD,mE,mH,ab,tb,dt,ed,W,wHG,he,
    A,B,gamma,one,two,
)

half=I(F(1,2))
pA=(x1-half,y+half)
pB=(x2-half,y+I(F(3,2)))
pT=(x2-I(F(3,2)),I(F(27,20)))
pD=(x3+half,y3-half)
pE=(x4+half,y4+half)
pH=((h1+half)*c-(h2+half)*s,
    (h1+half)*s+(h2+half)*c)
pG=(pH[0]+c,pH[1]+s)
P=dict(A=pA,B=pB,T=pT,D=pD,E=pE,H=pH,G=pG)
normals=dict(a=(one,I(0)),b=(I(0),one),e=(c,s),f=(-s,c))
inner=lambda v,w:v[0]*w[0]+v[1]*w[1]
sub=lambda v,w:(v[0]-w[0],v[1]-w[1])

def halfwidth(name,normal):
    # At the exact sharp reference: A B T D E standard,
    # H G tilted through cos t,sin t.
    standard=name in ("A","B","T","D","E")
    axis_standard=normal in ("a","b")
    return half if standard==axis_standard else half*(c+s)

# Complete actual SAT axis classification: only the prescribed
# owner normal directions have zero projected gaps. At the
# candidate all other 11 pair-side axes have strict negative
# projected gaps (<-1/20) on the *entire exact root box*.
wrong={
    ("A","B"):("a",),
    ("T","B"):("b",),
    ("D","T"):("b",),
    ("E","D"):("a",),
    ("G","A"):("f","a","b"),
    ("H","G"):("f",),
    ("H","E"):("e","a","b"),
}
assert sum(len(v) for v in wrong.values())==11
for (i,j),axes in wrong.items():
    d=sub(P[j],P[i])
    for owner_axis in axes:
        g=(abs(inner(normals[owner_axis],d))
           -halfwidth(i,owner_axis)
           -halfwidth(j,owner_axis))
        g.lt(-F(1,20))
        print("PASS wrong axis",i+j,owner_axis)

# The five true same-cluster SAT edges AB, TB, DT, ED, HG
# each permit either endpoint's side as owner. Their true
# signed transverse reference displacements are:
Y=[
    x1-x2,                    # Jb dot (pB-pA)
    pB[1]-pT[1],             # Ja dot (pB-pT)
    pT[1]-pD[1],             # Ja dot (pT-pD)
    x4-x3,                   # Jb dot (pD-pE)
    I(0),                     # Je dot (pG-pH)
]
names=("A","B","T","D","E","H","G")
where={name:i for i,name in enumerate(names)}
# The two mixed reference edges GA (owner G) and HE
# (owner H) have genuinely different nominal frame
# angles; their supports are smooth rather than cusp-like.
Y_GA=(-s)*pA[0]+c*pA[1]-h2-half
Y_HE=h1+half-(c*pE[0]+s*pE[1])
# Disk-corner and mixed-edge angular gradients; the
# contributions from the other five SAT normals are
# added below according to which true owner rotates.
L=[
    B[0],B[1],I(0),B[3],B[4],
    mH*(h1-h2)+he*((c-s)/two-Y_HE),
    W*((c-s)/two-Y_GA),
]

aligned_edges=[
    ("A","B",ab),
    ("T","B",tb),
    ("D","T",dt),
    ("E","D",ed),
    ("H","G",wHG),
]
assert len(aligned_edges)==5

lowest=None
for assignment in product((0,1),repeat=5):
    vec=[I(x) for x in L]
    for k,choice in enumerate(assignment):
        i,j,mult=aligned_edges[k]
        owner=(i,j)[choice]
        vec[where[owner]]=vec[where[owner]]-mult*Y[k]

    # Unique anchored-tree inversion:
    # A is the chosen standard frame, and G fixes
    # the oblique-frame tilt; their frame differentials
    # are zero in this relative-angle calculation.
    cED=vec[where["E"]]
    cDT=vec[where["D"]]+cED
    cTB=vec[where["T"]]+cDT
    cAB=-vec[where["B"]]-cTB
    cHG=vec[where["H"]]
    coeff=[cAB,cTB,cDT,cED,cHG]

    for k,(_,_,mult) in enumerate(aligned_edges):
        reserve=mult/two-abs(coeff[k])
        reserve.gt(F(1,40))
        if lowest is None or reserve.lo<lowest.lo:
            lowest=reserve

assert lowest is not None
print("PASS: all 32 true SAT owner assignments and 160")
print("      angular derivative comparisons certified EXACTLY")
print("PASS: strict minimum true SAT angle reserve >1/40")
print("PASS: candidate wrong axes all <-1/20")
