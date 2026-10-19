# Saturate all isolated squares without increasing the packing radius

## Theorem

Let eight pairwise interior-disjoint unit squares lie in a closed
disk D_R centered at the origin, where

    sqrt(2)+1/2 < R < 2,

and suppose the disk origin lies in the **open interior** of a
unique central square C. Then the configuration can be modified
by finitely many center translations, without rotating any square,
so that:

1. every square still lies in D_R, with pairwise disjoint open interiors;
2. no two squares that initially touched cease touching;
3. **every square has actual-contact degree at least one**.

In particular, because the analytic central-square theorem applies
in the eight-square minimizer radius range, the unrestricted radius
R_8 is attained by a packing with **no isolated vertices** in its
actual-contact graph. Thus one may restrict a *global radius
lower-bound argument* to such an attained representative, without
any extra contact-graph assumption.

**Important scope.** The resulting packing need not be the
minimum-actual-contact-count radius minimizer. The actual-leaf and
actual-bridge theorems which select *that* representative must not
be transferred to the saturated representative without a fresh
justification. This lemma removes global isolates by representative
selection; it does not force a connected graph, a five-corner chain,
or the conjectured sharp radius.

## 1. A universal inward motion of an exterior isolated square

Write a square S as

    S=p+[-1/2,1/2]e+[-1/2,1/2]f,

where e,f form an orthonormal frame. Its greatest squared
vertex norm after replacing p by a*p, a in [0,1], is

    a^2*|p|^2+a*(|p dot e|+|p dot f|)+1/2.           (1)

This is nondecreasing in a>=0. Hence moving any square's
center radially toward zero, while keeping its frame fixed,
**never destroys disk containment**.

Suppose S is isolated in the actual-contact graph and is not
the central square C. Its center p is nonzero, since S omits
zero in its closed set. Move its center continuously along

    p(a)=a*p,        1>=a>=0.

At a=1 every other *closed* square has a positive distance
from S, by isolation and compactness. At a=0, the moved S
contains zero in its open interior and therefore has an
open-interior overlap with C, which also contains zero
in its open interior.

All square-intersection and interior-overlap conditions
depend continuously on a. Therefore there is a **first
closed-set contact** when decreasing a from 1 toward 0.
At that first-contact position, no interior overlap has
occurred with any other square: such an overlap would
persist in a small interval of earlier times by
openness, contradicting that it was the first contact.
Before that event all pairs involving S were disjoint,
and every other pair was unchanged. Equation (1)
guarantees disk containment throughout.

Thus S has gained at least one actual neighbor,
without breaking any previously existing actual pair.

## 2. The same conclusion for an isolated central square

Suppose now C itself is isolated. Hold its frame fixed
and move its center radially to the origin. The fixed
frame's disk-admissible center region is convex:
it is the intersection of the four radius-R disks
imposed by its vertices. It contains both the old
center and zero, since R>sqrt(2)/2. Alternatively,
(1) directly proves containment along the path.

If C makes a new closed-set contact during this
motion, stop at its first contact as in section 1.
Otherwise C now has center zero and is still
isolated.

Choose any other square T, with center p_T and
radius r=|p_T|. Since C and T are separated in
their closed sets, the closed inscribed disks of
radius 1/2 about their centers are disjoint.
Thus r>1. Let u=p_T/r and move C's center from
zero along

    p_C(t)=t*u,        0<=t<=r-1.                       (2)

Every square T contained in D_R has center norm
at most R-1/2: the closed inscribed disk of T
is contained in D_R, and its farthest point on
the radial ray has norm r+1/2. Therefore

    r-1 <=R-3/2.

Every point of C lies within distance 1/sqrt(2)
from its center. Throughout (2) its vertex norms
are bounded by

    t+1/sqrt(2) <=R-3/2+1/sqrt(2)<R,                 (3)

using 1/sqrt(2)<3/2. Thus C stays strictly
inside the containing disk during this motion.

At t=r-1 the centers of C and T are exactly one
unit apart, so their closed inscribed radius-1/2
disks touch and hence their closed squares
touch. If C meets some square earlier, stop at
the first contact instead. In either case C
acquires an actual neighbor, no earlier contact
is lost, and the whole packing remains feasible.

The motion does not assume that C's sides are
parallel to the target's; it uses only the
inscribed disk and the square's circumradius.

## 3. Induction removes every isolate

Start with an arbitrary feasible packing as in the theorem.
If it has an isolated square, choose it. Apply section 1
if it is noncentral, and section 2 if it is central.
Only that square moves. Since it was initially isolated,
**all previously existing contact pairs remain unchanged**.
At least one actual pair is gained, reducing the number
of globally isolated square labels by at least one; any
other square that was a contact-neighbor retains all its
old edges.

Repeat this finite operation. There are only eight square
labels, and every iteration decreases the isolate count.
Therefore after at most eight iterations no square is
isolated, while disk containment and every prior contact
are preserved. This proves the theorem.

## 4. How this changes the sharp n=8 roadmap

The previous actual-contact component analysis allowed
isolated square labels which had to be counted in all
occupancy arguments. The present theorem shows that, for
the *existence* of a radius minimizer realizing R_8,
one can choose a representative where every label
belongs to a nontrivial actual-contact component.
This is a valid unconditional, unrestricted reduction
from the analytic central-square theorem and R_8<2.

The note does **not** show that this representative
also minimizes the number of contacts among radius
minimizers; in fact the saturation explicitly adds
contacts. One must not combine it with
HUMAN_ACTUAL_BRIDGES.md's minimum-contact assumption
without proving a compatible representative-selection
lemma. Nor does it show that an isolated square in an
arbitrary preselected minimizer is impossible.

The primary unsolved global implication remains
`R_8>=R_hat`. A representative with no isolates
is only a contact-graph simplification; further
geometric inequalities are required to derive
the exact five-corner obstruction.
