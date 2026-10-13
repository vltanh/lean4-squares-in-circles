#!/usr/bin/env python3
"""Symbolic audit for the complete SS radial branching bridge exclusion.

The hand proofs are:
  HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md
  HUMAN_B3_SS_SIDE_CORNER_TORQUE_FORM.md
  HUMAN_B3_RADIAL_SS_FULL_EXCLUSION.md

The strict full-square separating gap is exactly 1-c>0,
where c^2+s^2=1 with s>0. The global coarse radius
R^2>19/5 is independently certified in GLOBAL_LOWER_BOUND.md.
This script checks only symbolic/rational substeps,
not the full historical interval certificate or global n=8 proof.
"""
from fractions import Fraction as F
import sympy as sp

k,d,c,s,xi,lX,lY,lZ=sp.symbols(
    "k d c s xi lambdaX lambdaY lambdaZ",real=True)

# SS radial leaf normal (1,0), X top-left C-corner positive
# normal (-c,s), Y bottom-side positive normal (0,-1).
nX=sp.Matrix([-c,s])
nY=sp.Matrix([0,-1])
nZ=sp.Matrix([1,0])
zX=sp.Matrix([-k,d+sp.Rational(1,2)])
zY=sp.Matrix([xi,d-sp.Rational(1,2)])
zZ=sp.Matrix([1-k,0])
cross=lambda v,w:sp.expand(v[0]*w[1]-v[1]*w[0])

f=lX*nX+lY*nY+lZ*nZ
force_values={lY:lX*s,lZ:lX*c}
assert all(sp.expand(x.subs(force_values))==0 for x in f)
torque=sp.expand(lX*cross(zX,nX)+
                 lY*cross(zY,nY)+
                 lZ*cross(zZ,nZ))
torque_from_force=sp.factor(torque.subs(force_values))
assert torque_from_force==lX*(c*(d+sp.Rational(1,2))-s*(k+xi))
solution_xi=sp.solve(torque_from_force,xi)[0]
assert sp.simplify(solution_xi-(-k+c*(d+sp.Rational(1,2))/s))==0

# X's inner face is side normal (-c,s), with unit tangent
# (-s,-c). Even when the original corner contact lies at
# a true endpoint, its full tangent excursion has length <=1.
# Thus min_y(X) >= (d+1/2)-c.
# The genuine bottom C-side contact forces max_y(Y)=d-1/2.
gap=sp.simplify((d+sp.Rational(1,2)-c) -
                (d-sp.Rational(1,2)))
assert gap==1-c

# The coarse certified radius leads to a near-corner
# diameter comparison with all rational inequalities exact.
assert F(71,20)>(F(47,25)**2)
assert F(13,25)**2-(F(3,25)**2+F(1,4))==F(3,500)>0
assert F(71,50)**2>2
assert F(19,5)-F(97,50)**2==F(91,2500)>0

# A true oblique corner normal has s>0 and c in (0,1),
# so the separator gap is strictly positive for all frames.
for ss in (F(1,1000), F(1,5), F(1,2), F(4,5)):
    cc=sp.sqrt(1-sp.Rational(ss.numerator,ss.denominator)**2)
    assert bool(1-cc>0)

print("PASS: force and torque normal form plus strict")
print("      X-Y full-square gap 1-c>0 for the two SS mirrors")
print("      and the certified coarse-radius rational inputs")
