# All cycle edges have side owners when the four pair stars are nonparallel

Date: October 27, 2026.

**Status: complete compatible hand selection theorem, submitted for
full root and separate independent review.** This strengthens the
accepted unique/unique AB-owner reduction in
`ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md`.
It is a necessary selected-domain theorem, not a whole high LCD.SS
exclusion. Parallel root-pair cases and physical two-corner masks are
explicitly retained outside the new conclusion.

Keep the original strict-high component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+epsilon,       0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=1105/256.

All nine physical squares, actual circle masks, individual zero weights
and original contact means remain. A,B have their actual genuine S
leaves. C,D are loaded and physically touch. Suppose C and D each
have a unique physical circle corner and both roots' two nonleaf
force directions are nonparallel.

**Theorem.** The common compatible selected certificate can be chosen
so that every one of AB,BC,CD,DA has a normal owned by an actual
side of at least one of its two squares. No free point-only strict
vertex/vertex cycle edge occurs in this entire domain.

Every finite normal choice below is made on the fixed physical pose
before multiplier extraction. Nothing reselects a normal or fixes a
shared-side application in an obtained certificate.

## 1. A boundary neighbor's circle corner cannot be parallel to the real S leaf

This local fact is physical and does not use root degree or a force
equation. Let H have an actual radial S leaf L with direction e,
inner midpoint d*e and d>1. Let T be any other actual boundary
unit that physically touches H, and let z be any physical circle
corner of T.

Then z is not parallel to e.

First suppose z=R*e. Every circle corner is strictly within pi/12
of its body's center direction, by Section 1 of
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`. The actual radial S
unit L has center direction exactly e. Thus the center directions
of T and L would differ by less than pi/12, contrary to the strict
2pi/9 separation in `CENTERED_INNER_ARC.md`.

Next suppose z=-R*e. The actual supporting line of the leaf gives
max_H(e dot x)=d, and the width of a unit in direction e is at
most sqrt(2). Hence every actual P in H, and in particular every
P in H intersect T, satisfies

    e dot P>=d-sqrt(2).

Consequently

    |P-z|>=e dot(P-z)>=R+d-sqrt(2)>sqrt(2),

because R>2 and d>1 give R+d>3>2sqrt(2). But P and z
belong to the same actual unit T, whose diameter is sqrt(2).
This contradiction excludes the opposite direction as well.

This proof covers every physical circle corner, not only a selected
positive one. In the unique/unique mask it says that the fixed
external directions at the adjacent pairs A,D and B,C are
nonparallel.

The other two adjacent external pairs are nonparallel too. The
actual two leaf directions are nonparallel by the accepted full-domain
theorem. The unique C/D circle directions are distinct and acute:
their actual center separation exceeds 2pi/9, each corner differs
from its center by less than pi/12, and the physical touching pair
has strictly acute corner pairs. Thus their directions cannot be
equal or opposite.

## 2. The full cyclic determinant with any edge as its free variable

Use indices modulo four for the unchanged bodies

    S_0=A, S_1=B, S_2=C, S_3=D.

Let e_i denote their fixed external unit directions, respectively the
two real leaf directions and the two unique physical circle directions.
Let n_i be the actual normal on S_i to S_(i+1), and mu_i>0 its
original magnitude. The four full force equations have exactly the
form

    mu_i*n_i-mu_(i-1)*n_(i-1)+lambda_i*e_i=0,
    lambda_i>0.                                  (1)

At the two roots lambda_i are the actual genuine leaf magnitudes.
At C,D they are the lengths of the actual circle resultants. There
is no extra circle term at the clear roots, and no term of a true
degree-three or degree-two equation has been dropped.

Taking each equation's determinant with e_i gives

    mu_i*det(n_i,e_i)=mu_(i-1)*det(n_(i-1),e_i).

Multiplication and cancellation of the four strictly positive
magnitudes yields the exact necessary relation

    product_i det(n_i,e_i)
       =product_i det(n_i,e_(i+1)).               (2)

For any chosen edge j, hold the other three normals fixed and write

    K_j=product_(i!=j) det(n_i,e_i),
    L_j=product_(i!=j) det(n_i,e_(i+1)).

Then (2) is precisely

    det(n_j,K_j*e_j-L_j*e_(j+1))=0.              (3)

This identity contains no application mean and uses no torque
equation. The actual AD,BC,CD and AB means may all vary over their
complete physical supporting segments.

## 3. Every coefficient is nonzero in the stated original domain

The true C2 and D2 pairs are nonparallel by Lemma 2.1 of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, because each has the
other actual boundary unit as a neighbor. The hypothesis of this
source retains nonparallel nonleaf pairs at A,B as well.

If the two pair directions in (1) are nonparallel, taking determinants
with either one shows that neither incident pair direction is
parallel to e_i. Thus every factor appearing on either side of (2)
is nonzero. In particular the actual K_j and L_j are both nonzero.

Section 1 proves e_j and e_(j+1) nonparallel for every j. Hence

    K_j*e_j-L_j*e_(j+1)!=0.                      (4)

When n_j is a free strict vertex/vertex normal, its necessary relation
(3) is therefore a nonzero sinusoidal linear form of that free angular
parameter, if the other normals have their actual values.

## 4. Simultaneous selection for every candidate cycle and every free edge

At the fixed physical pose prelist all ordered assignments of the six
distinct actual bodies and their two candidate genuine radial S leaves,
with unique physical circle corners at the two stated boundary bodies.
These are finitely many pose data. For each tuple and each candidate
free cycle edge j, consider (3) on the original product of permissible
open point-normal intervals.

The matched-junction convention of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` couples only the two opposite
pairs at one actual four-square junction. Omit any tuple that would
use both such opposite pairs positively; it is already impossible
in the common uncrossed certificate. In each retained tuple, the
chosen free edge j can vary over an open interval while the other
three cycle normals remain fixed. Its only potentially linked cycle
edge would be the disjoint opposite pair, which was just excluded;
all adjacent contacts at that junction have fixed own-axis normals.

For every tuple whose complete expression (3) is not identically
zero on this permitted parameter domain, require it to be nonzero.
These are finitely many dense open conditions. In local slope
parameters, multiplication by the positive normalization factors
makes (3) an ordinary polynomial. A nonzero such polynomial has no
open zero set. This finite selection can therefore be made
simultaneously with all preceding strict, nonradial, generic and
matched-junction conditions before extraction.

Original uncrossing retains each surviving point normal and adds
only already available actual shared-side endpoint atoms; all their
fixed side axes were included in the finite prelist. Subsequent
thinning deletes atoms. The minimum-positive-original-atom choice
can be made within this same nonempty normalized admissible class.
Thus the additional selection does not invalidate those existing
properties or any original means.

Suppose a positive component in the stated nonparallel-pair domain
nevertheless survived with edge j free. Its actual values satisfy
(4), so varying j with the other actual normals fixed proves that
its complete expression was not identically zero. It was therefore
included in the finite avoidance list. But its original full force
equations require (3) to vanish. This is a contradiction.

Since the prelist included every candidate edge, all four actual cycle
edges have side-axis owners, as claimed.

## 5. Exact original uses and limitations

After AB is normalized to East, the two clear-root nonleaf pairs
are nonparallel exactly when the two actual leaf directions have
nonzero vertical components. Indeed the unchanged root equations
in (1) identify the vertical component of the other pair force with
the negative vertical component of the positive leaf force.

Thus this full selection applies directly after a caller proves those
two real leaf components nonzero. A genuinely horizontal leaf is a
separate original parallel-root-pair case and is not silently deleted.
If all four actual body frames happen to be parallel, the conclusion
makes all four cycle normals actual axes of that common frame.
For arbitrary neighbor frames it asserts ownership by at least one
endpoint body; it neither makes the frames parallel nor fixes which
body owns a given normal.

The physical two-corner C/D masks remain outside this fixed-external-
direction selection. An individual zero weight in a two-corner
physical mask does not turn it into a unique-corner mask. No
standalone fine gate, whole high LCD.SS claim or completion bound is
inferred from this necessary owner reduction.

No numerical pose, normal reselection after extraction, fixed false
mean, force deletion, compilation, CI, remote mutation or shared
metadata edit is used.
