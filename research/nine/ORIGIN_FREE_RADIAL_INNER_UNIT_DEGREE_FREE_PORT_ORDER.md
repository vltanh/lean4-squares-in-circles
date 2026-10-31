# Any origin-free inner radial-contact unit has strict nonradial port order

Date: October 28, 2026. Author: global_blocks.

**Status: complete proposed uniform geometric theorem; awaiting root and
independent review. No original fine or coarse checkbox is changed.**

Keep the same nine actual interior-disjoint closed unit squares and their
unchanged containing disk, with

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1 < 61/60,
    epsilon = max(d-1,0) < 1/60.

A radial physical contact means an actual common application p and an
actual separating normal e with p=t e, t>0. Its inner unit U lies in
{x:e.x<=t}, and its outer unit V lies in {x:e.x>=t}. The contact need
not carry positive force or belong to a bridge. Its real side mean and
normal are not changed. Assume U avoids O, including on its boundary.
There is no force, degree, circle-load, or genuine-leaf hypothesis on U
or V.

**Theorem.** For any two other actual contacts of U, with units different
from V, retaining the actual outward normals and applications,

    det(p_-,n_-) < 0 < det(p_+,n_+),

the angular change from p_- to p_+ on the unique angular branch of the
origin-free convex U is strictly positive. In addition, no actual unit
T different from V and avoiding O can have a radial contact with U.

The theorem strictly extends the geometric premises of
ORIGIN_FREE_GENUINE_S_ROOT_DEGREE_FREE_PORT_ORDER.md: the outward radial
neighbor is an arbitrary occupied unit, with arbitrary true degree and
arbitrary contact radius t, and is not assigned the shape or equations
of a genuine leaf.

## 1. Exact common center cap

Every actual contained unit center c satisfies

    |c| <= d+1/2 < M = 91/60.

Every actual unit on the outer side n.x>=h of a unit-normal support
satisfies

    c.n >= h+1/2,       h <= d.

These are the degree-free geometric center and halfwidth bounds from
Section 1 of GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md.
Their proof uses the farthest-corner inequality
|c|^2+|c|+1/2 <= R^2 and the minimum unit-square halfwidth 1/2.

Put C=3501/2440. If an actual supporting normal n=(u,v) satisfies

    u > 60/61, |v| < 11/61, h>1,

then c.n>3/2 and |c.Jn|<sqrt(181)/60<27/120. Hence

    c.x > (3/2)(60/61) - (27/120)(11/61) = C.

All such centers lie in the same open cap |c|<M, c.x>C. The squared
diameter of its containing rectangle is

    (M-C)^2 + 4(M^2-C^2) = 52124381/53582400 < 1.

Two distinct actual unit centers cannot belong to that cap, since their
disjoint open radius-1/2 incircles require center distance at least one.
This argument includes arbitrary neighbor orientation and every actual
support point.

## 2. Complete own-coordinate reduction of the actual inner unit

Because U avoids O, one own interval misses zero. Choose its positive
axis and write that interval [a,a+1], a>0. Since p=t e is a maximum-e
point of U, its first coordinate is a+1, and

    t>1, e_x=(a+1)/t > 1/d > 60/61.

Both own intervals cannot miss zero. If they did, radial support would
put both absolute coordinates of p above one, forcing t>sqrt(2)>d.
Thus, in a positively oriented orthonormal own frame,

    U=[a,a+1] x [b,c], c=b+1, b<=0<=c,
    0<a<=t-1<=d-1=epsilon.

In particular d>1 and dist(O,U)=a<=epsilon. Also |e_y|<11/61.
The actual outer V has e-support t>1, so Section 1 places its real
center in the cap c_x>C. This remains valid if the radial point is a
side interior, side endpoint or strict vertex, and for either sign of
e_y. No transverse coordinate of any other contact has been fixed.

## 3. One occupied cap excludes every wrong-sign far feature

Every non-V neighbor with U normal east would have support a+1>1;
its center would occupy the same cap as V. Hence no such actual contact
has that normal, for any far-side mean or endpoint.

At the upper-right vertex (a+1,c), let the actual outward unit normal
be n=(u,v), u,v>=0. Suppose its determinant were nonpositive:

    (a+1)v-c u <= 0.

Then u>0. If v>0, the displayed inequality gives

    h=(a+1)u+c v >= (a+1)(u+v^2/u)=(a+1)/u > 1/u.

The same last strict inequality holds for v=0, because h=a+1>1.
Since h<=d, one obtains u>1/d>60/61 and v<11/61. Also h>1.
The actual neighbor therefore occupies the cap already occupied by V.
It must be V, so it is unavailable to every contact in the theorem.
The north-axis endpoint u=0 has strictly positive determinant and was
never in the contrary case. Thus every non-V upper-right contact has
strictly positive determinant.

Reflecting this calculation in the horizontal axis, and reversing the
moment sign accordingly, shows that every non-V lower-right contact
has strictly negative determinant. This is a proof of the two symmetric
inequalities in one fixed packing, not a new selection or motion of any
normal or body.

These arguments require no local half-plane occupancy by V at the radial
point. In particular V may have a vertex at that point. The proof uses
only its actual occupied center cap, so the S-leaf midpoint property
from the earlier genuine-leaf theorem has been removed entirely.

## 4. The entire remaining feature cover gives strict angular order

On the top side and upper-left vertex cone every nonzero determinant
is positive; their applications have y=c>=0. On the bottom side and
lower-left cone every nonzero determinant is negative, and y=b<=0.
On the left side the normal is west and the determinant is exactly y.
The far-side east axis was excluded in Section 3. The two remaining
far vertices have the strict signs established there.

Consequently every negative non-V port has y<=0 and every positive
non-V port has y>=0. Every actual point of U has x>=a>0. Their angular
change is therefore nonnegative.

Equality would force both port heights to be zero. If b<0<c, the only
remaining zero-height contact feature is the left-side interior and
its determinant is zero. If c=0, every possible nonzero determinant at
height zero is positive, whereas if b=0 it is negative. The distinct
sides cannot both have height zero. Thus the two required strict signs
cannot have equal angular coordinates. The angular increase is strict.
This includes all closed slider endpoints and all original side means.

## 5. The radial-contact uniqueness statement

Section 2 and the same center-cap proof show that any origin-free actual
unit has at most one outward radial contained neighbor. Choose once an
own interval [a,a+1] missing zero; every such contact puts its outer
neighbor in the same cap of Section 1.

Now suppose T!=V avoids O and has a radial contact with U. An application
at O is impossible because U avoids O. If U is the inner endpoint, T
and V would be two distinct outward radial neighbors, contradicting the
cap. If U is the outer endpoint, the origin-free inner T forces its
contact radius t'>1 by the same missing-own-interval argument. But a
radial minimum-support application is the unique nearest point of its
outer unit, so t'=dist(O,U)<=epsilon<1/60, a contradiction.

This proves the second assertion without a force equation or degree
restriction on T, U or V.

## 6. A uniform D-root consequence for any separate cyclic block

Let E have a genuine D leaf L_E, and let Q be any maximal cyclic block
avoiding E. The accepted fixed-D-root theorem says that at most one
actual unit other than E meets D_sigma, where sigma=3/125. The accepted
near-origin boundary-access theorem, applied to the actual outside-Q
edge E--L_E, supplies a unit X of Q meeting D_epsilon. Therefore X is
unique, every Q unit avoids O, and every other actual unit U different
from E,X satisfies

    dist(O,U)>sigma>sqrt(2)*epsilon.

**Consequence.** X has no radial contact to any actual unit T different
from E when the radial normal and application are the ones retained by
the original compatible selected certificate. A preselected contact of
zero weight is allowed. If XT is a positive edge, its original selected
normal and application must be radial; an alternative geometrically
permitted normal is not sufficient for this consequence.

Suppose it existed. The outer-X alternative is impossible: the
origin-free inner T would force radius >1 while dist(O,X)<=epsilon.
Thus X is the inner endpoint, and Sections 1--4 apply with V=T.

There is at least one nonzero moment edge in Q: a cyclic block has an
edge whose endpoints both differ from X, and both such units avoid
D_epsilon. Such an edge cannot be radial. Indeed an origin-free inner
endpoint of a radial contact would meet D_epsilon by Section 2.

The full Q moments form a circulation. Sum all original origin-torque
equations on every outside component; its complete contribution at its
sole Q attachment is zero, since internal moments cancel and every
circle atom has zero origin moment. This leaves precisely Q's full
original edge moments. Delete only zero entries from this auxiliary
moment circulation; no physical force or graph edge is removed from
the packing. Its nonzero entries contain a directed simple cycle C.

If C includes X, its two cycle edges have nonzero original moments.
If XT is positive, the consequence's unchanged-selection premise makes
its original moment zero; if XT has zero weight, it is not a positive
cycle edge at all. Hence neither of the two cycle edges uses T. The two original ports at X
have strictly positive angular advance by Sections 1--4. Every other
vertex of C is farther than sqrt(2)*epsilon from O; the far-body port
lemma in HOUSE_ROOF_AC_D_COMPLETE_MOMENT_EXCLUSION.md, Section 1.2,
gives nonnegative advance with no neighbor-avoidance premise. Thus C
winds positively about O. If C avoids X, all its units avoid D_epsilon,
and the complete degree-free directed-cycle theorem gives the same
positive winding, including all coincident-port equality alternatives.

Choose one sufficiently close compatible physical embedding. It makes
C a Jordan curve with that winding. The actual segment O--c_E lies in
int E and has positive clearance from the C bodies. Thus E is inside
C. Its actual edge to physical boundary L_E lies entirely outside Q
and cannot cross C in the same embedding, putting L_E inside as well.
That contradicts its protected unbounded-face access. This proves the
consequence.

This consequence extends D_ROOT_EXCLUDES_SEPARATE_CYCLIC_BLOCK_CONTAINING_A_LEAF_ROOT.md:
the unique near unit of Q cannot have any outward radial neighbor with
its original compatible selected contact data, including a selected
zero-weight contact to an arbitrary-degree body. A genuine leaf at X is
one special case. A radial contact from E to X can remain and is
explicitly outside the conclusion. A second supporting normal of an
already selected nonradial vertex contact is not reselected as radial.

## 7. Scope and original count boundary

The geometric kernel applies to inner endpoints of arbitrary actual
radial bridges, to genuine S roots, and to radial physical contacts of
zero stress. Every original equation, selected normal, application,
mean interval, physical circle mask, completion square and zero weight
remains. The D-root consequence applies to every block size and chord
pattern, without identifying the unique near vertex's force degree.

No existing original ID has been proved to isolate this entire new
hypothesis. Therefore this source assigns zero fine or coarse count.
It neither excludes every separate block at a D root nor concludes that
a near unit has a radial contact without an actual premise. It uses no
numerical pose, orientation partition, computational proof certificate,
Lean execution, compilation, CI, remote write or shared-ledger edit.

## 8. Operative source pins

The new cap, full feature cover and radial uniqueness are proved above.
The D-root corollary additionally uses only the stated parts of these
unchanged sources (SHA-256):

- GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md:
  8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49.
  Section 1 support bounds; Sections 2--3 for a cycle avoiding X.
- D_LEAF_ROOT_AT_MOST_ONE_OTHER_UNIT_IN_THREE_125_DISK.md:
  34385a647c1889564b3423ecfff03a7a75747275e45f68346c3f8a9f06abfaaf.
  Entire fixed-disk physical exclusion.
- NEAR_ORIGIN_BOUNDARY_ACCESS_TRANSFERS_TO_EVERY_CYCLIC_BLOCK.md:
  49065116bfd526abf3826ae8bbaa6fd9ad43b7bcdbdc0e0653b959fa84359549.
  Entire near-unit transfer, including epsilon=0.
- HOUSE_ROOF_AC_D_COMPLETE_MOMENT_EXCLUSION.md:
  db795b7a1a287d7e8e422bd80f3ea04e714d9d98af88226e9c16ad757b7e0f5a.
  Section 1.2 far-body port lemma with unrestricted actual neighbors.
- PHYSICAL_BODY_GRAPH_UNCROSSING.md:
  bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe.
  Single compatible embedding and physical boundary access.
- RADIAL_BRIDGE_AND_LEAF_REDUCTION.md:
  faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676.
  Genuine D open-origin chart and full original torque conventions.
