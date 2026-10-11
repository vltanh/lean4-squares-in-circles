# An exact obstruction to a uniform linear-tilt center-angle potential

## The failed universal assertion

Let S,T be two pairwise interior-disjoint unit squares with center
norms at least one inside the disk of squared radius

    q0=5/2+sqrt(2).

Write their center-ray angular gap as `delta in (0,pi)`, ordered
counterclockwise, and their *relative side-frame tilts* as
`alpha_S,alpha_T in (-pi/4,pi/4)`: the actual side-frame angle
minus the center-ray angle, using quarter-turn square symmetry.

**Theorem (negative).** There is **no real constant k** such that
every such ordered pair satisfies the uniform inequality

    delta + k*(alpha_T-alpha_S) >= 2*pi/7.              (1)

Both counterexample pairs below use strict interior relative tilts,
so no ambiguous endpoint choice `alpha=+/-pi/4` is involved.
This excludes a simple affine state-potential shortcut for the
seven-outer-center ring. It does not exclude nonlinear or multi-type
potentials, a sharp seven-step walk inequality, or a structural route
through the central square.

## 1. A parallel touching pair forces k <= -1/7

Take two horizontal/vertical squares with centers

    p_S=((1+sqrt(2))/2,-1/2),
    p_T=((1+sqrt(2))/2,+1/2).

They share their horizontal boundary edge, with disjoint open
interiors. Their greatest squared vertex norm is exactly
`q0=5/2+sqrt(2)`; their center norms exceed one.
Their center-ray directions are `-pi/8,+pi/8` since
`tan(pi/8)=sqrt(2)-1`.
Both squares have global side-frame angle zero, so

    delta=pi/4,
    alpha_S=+pi/8,  alpha_T=-pi/8.

Substituting in (1) gives

    pi/4-k*pi/4>=2*pi/7,   hence k<=-1/7.              (2)

## 2. A strictly disjoint rational-frame pair violates every such k

Set `r=5/4`, `c=21/29`, `s=20/29`, and
`a=arctan(s/c)`. Since `s<c` and
`s/c=20/21>1/sqrt(3)`, the exact angle range is

    pi/6<a<pi/4.                                        (3)

Take the centers

    p_S=(r,0),    p_T=(r/2,sqrt(3)*r/2),

and orthonormal side frames with global first-axis angles
`-a` for S and `pi/3+a` for T. Their center-ray directions
are 0 and `pi/3`, so the unique relative tilts are

    alpha_S=-a,    alpha_T=+a,
    delta=pi/3.

The exact greatest squared vertex norm of each square is

    r^2+1/2+r*(c+s)
       =33/16+205/116
       =1777/464 <39/10<q0.                            (4)

Both center norms equal 5/4>1.

For completeness, these two squares are *strictly* separated,
not just numerically near contact. Use the side axis of S

    n=(c,-s)=(21/29,-20/29).

Its center displacement projection is

    |n dot(p_T-p_S)|=5*(21+20*sqrt(3))/232.

The relative frame angle is `pi/3+2a`, which lies between
`2*pi/3` and `5*pi/6`. The support half-width sum is

    [1+|cos(pi/3+2a)|+|sin(pi/3+2a)|]/2
       =(2481+881*sqrt(3))/3364,

using `cos(2a)=41/841`, `sin(2a)=840/841`.
Thus the **exact** strict separating margin is

    (1138*sqrt(3)-1917)/6728 > 0.                    (5)

The final strict sign is checked by squaring positive quantities:

    3*(1138)^2-(1917)^2=210243>0.

This supplies a literal separating line between their closed sets.

By (3), for any k<=-1/7 forced by (2), the left side
of (1) for this second pair satisfies

    delta+k*(alpha_T-alpha_S)
       =pi/3+2*a*k
       <= pi/3-2*a/7
       <pi/3-(pi/3)/7
       =2*pi/7.

This contradicts (1) and completes the theorem.

## Relevance

An affine additive correction depending only on one universal constant
times the signed **relative frame tilt** cannot turn *every* disjoint
outer pair into a directed gap of 2*pi/7, even at the smaller,
sharp two-square threshold q0. A seven-square ring proof must retain
more state, exploit the odd length seven, or use non-pairwise
geometry. Neither pair above supplies an eight-square improvement or
a counterexample to the candidate radius.
