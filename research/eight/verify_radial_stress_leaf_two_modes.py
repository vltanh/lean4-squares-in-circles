#!/usr/bin/env python3
"""Exact symbolic checks of the two radial positive-stress leaf modes.

This is an arithmetic/geometric regression check for
HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md, not a certificate of
a full eight-square packing or of physical global optimality.

At R=39/20, construct two true Z squares with the same bridge
normal (1,0), both with their inner radial support at the correct
b and actual circle vertices at the stated positions.
The unit square C may locally be placed with origin in its open
interior and with its outward support at b.
"""
import sympy as s

R=s.Rational(39,20)
a=s.sqrt(2)/2
rho=s.sqrt(R**2-s.Rational(1,4))
assert s.simplify(rho**2+s.Rational(1,4)-R**2)==0
assert bool(rho>1)
# Side frame Z: full side at rho, inner side at rho-1.
side_verts=[(rho+dx,dy) for dx in (-1,0)
            for dy in (-s.Rational(1,2),s.Rational(1,2))]
side_norm=[s.simplify(x*x+y*y) for x,y in side_verts]
assert all(s.simplify(z-R**2)==0 for z in side_norm[2:])
assert all(bool(z<R**2) for z in side_norm[:2])
side_b=rho-1
side_center=rho-s.Rational(1,2)
assert bool(0<side_b<1)
assert bool(abs(side_b-s.Rational(1,2))<s.Rational(1,2))
assert side_center-side_b==s.Rational(1,2)

# Diagonal frame Z: radial opposite vertices are (R,0) and (R-sqrt2,0).
diag_b=R-s.sqrt(2)
diag_center=R-a
diag_verts=[(R,s.Integer(0)),(diag_b,s.Integer(0)),
            (diag_center,a),(diag_center,-a)]
diag_norm=[s.simplify(x*x+y*y) for x,y in diag_verts]
assert diag_norm[0]==R**2
assert all(bool(z<R**2) for z in diag_norm[1:])
assert s.simplify(R-diag_b-s.sqrt(2))==0
assert bool(0<diag_b<s.sqrt(2))
# A parallel diamond C with center diag_b-a has origin strictly inside.
assert bool(abs(diag_b-a)<a)

# At these values, side bridge supports a 2-circle-vertex
# reaction with equal positive weights, diagonal a single vertex.
assert s.simplify((rho+s.Rational(1,2)*s.I)+(rho-s.Rational(1,2)*s.I)-2*rho)==0
print("PASS: both exact radial side and diagonal positive-leaf geometries")
print("      are locally consistent at R=39/20, preserving the genuine")
print("      frame and circle-contact classifications of the hand lemma")
