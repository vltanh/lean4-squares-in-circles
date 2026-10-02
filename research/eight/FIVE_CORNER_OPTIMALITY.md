# Complete optimality theorem for the five-corner chain

## Scope

This is a **conditional lower-bound theorem**, with a completely verified
full-domain certificate. It does not assert that all eight-square packings
have this chain. The remaining unrestricted structural problem is explicit.

Let (q*,y*,z*) be the unique root in the rational box certified by
`verify_candidate_stationary.py`, and put R*=sqrt(q*). The terminating
coordinates used to specify that box are exact rational data. Numerically,
R* is approximately 1.97877086533976321493.

## Theorem

Suppose five points P1,...,P5 in a disk of radius R satisfy, after a rigid
coordinate change, the five inequalities (1) of FIVE_CORNER_REDUCTION.md
for an angle 0<=t<=pi/4. Then R>=R*.

Conversely the exact eight-square construction in that note realizes the
five-point chain at R*. Its existence is established by root isolation,
algebraic contact identities, and interval checks of every other inequality.

Thus R* is the minimum radius for this projected-chain problem, not merely
a stationary value within a numerical ansatz.

## 1. The complete scalar domain

It suffices to exclude R<R*. Since R*<2, a chain in such a disk is also a
chain in the disk with squared radius q*. The reduction in
FIVE_CORNER_REDUCTION.md gives

    F(q*,y,z)<=0,
    -2<=y<=0,
    0<=z=tan(t/2)<=sqrt(2)-1<5/12,

with all four nested radicands nonnegative. The verification deliberately
covers the larger rectangle

    D=[-2,0] x [0,5/12].

No small-neighborhood or candidate-angle assumption is added here.

## 2. Convex core

Let

    K=[-11/10,-4/5] x [0,3/20].

The isolated root's (y,z) box lies in the interior of K. Over the complete
rational q enclosure and K, the verifier differentiates F by exact chain and
product rules and certifies that its (y,z) Hessian is positive definite.

For each terminal rectangle it verifies

    F_yy >= a>0,    F_zz >= d>0,
    |F_yz|<=b,      a*d-b^2>0.

These inequalities imply positive definiteness by Sylvester's criterion.
Subdivision proves them on the whole convex rectangle K; it does not assert
convexity merely because some sampled Hessians are positive.

At q=q*, F(y*,z*)=0 and both first partial derivatives vanish. Strict
convexity therefore gives F(q*,y,z)>=0 on K, with equality only at (y*,z*).
This is the mathematical device that treats the exact optimum; a finite
positive-margin cover could not eliminate its zero by itself.

Executed certificate: 1,011 nodes, 506 positive-definite terminal rectangles.

## 3. The complement of the convex core

The original D rectangle is split at the two core y endpoints and its upper
z endpoint, yielding six closed starting rectangles. A cell is accepted only
by one of the following exhaustive rules:

1. It lies entirely in K, already covered by the convexity argument.
2. A nested radicand is strictly negative for every possible feasible point.
3. Direct interval evaluation has strictly positive lower endpoint for F.
4. A centered mean-value bound is strictly positive:

       F(q,m)-sum_i sup_cell |F_i| * radius_i > 0,

   uniformly for q in its certified enclosure.

When a radicand interval merely crosses zero it is NOT discarded. Value
evaluation retains its nonnegative part, and derivative-based acceptance is
disabled unless all required derivatives are defined. An unresolved cell is
bisected into two closed halves. A budget or depth limit raises an error.

Executed certificate: 324 nodes, comprising 3 infeasible leaves, 161 strictly
positive leaves, and 1 leaf covered by K. The leaf/node accounting is
324=2*(3+161+1)-6, corresponding to the six initial rectangles.

Consequently F(q*,y,z)>0 at every feasible point outside K.
Together with section 2, its only nonpositive feasible value anywhere in D
is the zero at (y*,z*).

## 4. The lower-bound contradiction

If R<R*, the chain in the smaller disk is also a chain in the q* disk.
The scalar argument forces y=y*, z=z* and F=0. But the last step of the
five-corner reduction then forces

    |P5|^2 >= h1^2+h2^2 = q*,

contradicting |P5|^2<=R^2<q*. This proves the theorem. It avoids any
unjustified assertion about how the minimizing y,z vary with q.

## 5. Construction at equality

Run

    python research/eight/verify_exact_candidate_construction.py

The script first establishes the exact stationary root. It then checks all
27 non-boundary vertices with squared-radius slack greater than 1/1000 and
all 18 pairs not on the algebraic contact list with projection slack greater
than 1/100. The five boundary and ten zero-separation identities follow
symbolically from the coordinate definitions, c^2+s^2=1, and F=0.

Convexity of each square and the disk reduces containment to its vertices;
the separating-axis inequalities give disjoint open interiors. Thus the
construction uses exact real algebraic coordinates, not rounded placement
coordinates or an assumed optimizer output.

## 6. What remains for arbitrary eight-square packings

The theorem would finish the unrestricted lower bound IF one could show that
any hypothetical R<R* packing gives the five projected inequalities (1),
possibly after a justified deformation that does not enlarge its disk.

That implication is not established. In particular the existing central-square
certificate and the seven-marker quadrant count (2,2,2,1) do not force the
six common orientations, the two-square tilted chain, or the projected span 3.
Alternative separator/contact patterns must be excluded or handled separately.

The frozen-stress failure in NEGATIVE_RESULTS.md is bypassed for this family:
we do not claim its tilt-independent dual multipliers give a sharp bound.
Instead the full algebraic domain is checked and the surviving zero is handled
by convexity. This is a valid intermediate computational proof, with an
analytical replacement remaining possible later.

No Lean formalization has been attempted. All relevant commits use [skip ci].
