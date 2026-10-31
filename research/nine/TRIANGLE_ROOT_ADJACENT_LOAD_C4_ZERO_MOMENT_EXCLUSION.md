# An adjacent-load terminal C4 cannot attach to any actual triangle

Date: October 27, 2026.

Full root review: REVIEW_THREE_BRIDGE_CELL_SS_DIAMOND_AND_ADJACENT_C4_ROOT_2026_10_27.md.
Separate full-source/scope review: REVIEW_TRIANGLE_ADJACENT_C4_ZERO_MOMENT_TRIANGLE_BRIDGES_2026_10_27.md.
The reviews pin the mathematical source before this acceptance-only header edit.

**Status: accepted complete whole adjacent-load C4 exclusion at an arbitrary actual triangle.** The original triangle
need not have an origin-interior vertex. The zero-cycle-moment
domain is included through the accepted pair-resultant ray theorem.

Keep all nine original interior-disjoint physical unit squares and
the same compatible selected certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60.

The unchanged same-nine theorem supplies R>2 wherever its bound
is needed in the local input below. Suppose H,A,C form an actual
positive triangle, and H is the root of the actual terminal C4

    H-U-V-W-H.

U,V have their true positive pair degree two and positive circle
loads. W has true positive pair degree two and zero circle load.
H has its two actual triangle forces, its two actual C4 forces,
and its complete possible original circle force G_H. It has no
other positive pair force. A and C may have arbitrary original
degrees, circle loads and attached branches. Require, as in every
stated block-tree application, that their complete external systems
in the triangle have zero origin moment. The full external system
at H has zero origin moment by the true private C4 equations and
the original radial circle atoms.

**Theorem.** This entire original configuration is impossible.
The reflected adjacent-load placement is included by reflection
and relabeling of the actual cycle. No original force is removed
to change a degree, no terminal block is replaced by a leaf, and
all original masks, individual zero weights, actual means and
arbitrary completion units remain.

## 1. The exact local C4 input does not use an origin-interior triangle

Use Sections 1--4 of
`ROOTED_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_EXCLUSION.md` at their
complete stated local scope. Their proof ends with G_H=0 before
Section 5 first uses that source's origin-interior triangle
hypothesis. Here are the exact inputs and conclusions retained
from that full argument.

The true unloaded W and the actual physical bypass U give a
width-one channel. Rotate and reflect the whole configuration to
its unchanged channel frame:

    W=[alpha,alpha+1] times [z,z+1],
    P=(alpha,y_0) in H intersect W,
    P_V=(alpha+1,y_0) in V intersect W,
    y_0 in [z,z+1],
    H subset {x<=alpha},
    V subset {x>=alpha+1},
    U subset {y>=z+1}.

Let Q be the original H-U application, n its actual H-to-U
normal, mu>0 its original magnitude, and lambda>0 the true
transmitted magnitude. Summing the real private force and origin
moment equations gives

    M:=F_U+F_V=mu n+lambda e_x,
    mu det(Q,n)+lambda det(P,e_x)=0.                 (1)

The support-span calculation and the retained strict singleton
normal convention give either n=e_x, with e_x an actual H side
axis, or n_x>=0 and n_y>0. The complete all-orientation boundary
cap excludes alpha>0. The two true loaded endpoint equations,
their positive radial concurrences, and their proper original
ports then give

    alpha<=0,
    y_0<0,
    M_x>0.                                          (2)

In the parallel case n=e_x, the actual H side contains the two
original ports with

    Q_y>0>y_0,       M=(mu+lambda)e_x.               (3)

In the nonparallel case its genuine root-line concurrence has
the complete form

    q=-tM,      t>0,
    P=q+a e_x,  Q=q+b n,      a,b>=0.               (4)

These are the actual applications and actual proper distances,
including zero proper lengths. No affine concurrence point has
been asserted to belong to H.

The same full local proof retains the possible G_H through its
Section 4. If G_H were positive, the physical boundary path H-U-V
and its true boundary-force cone, together with the signs
(F_U)_y>0>(F_V)_y, would give two actual positive-weight circle
corners with x_V>X_H. The complete aligned/tilted H support
calculation instead gives x_V<X_H. This excludes every possible
positive H circle system with all original weight endpoints and
implies

    G_H=0.                                          (5)

The proof of (5) does not use any force equation at A or C, any
origin-interior triangle vertex, or a reduced degree at H. It
allows H to be physically boundary with zero circle weight.
Only after (5) is established is H's entire external resultant
in the actual triangle identified with M in (1).

## 2. The closed external ray fixes the critical supporting side

Apply `TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY.md` to the actual
triangle H,A,C with its complete external systems. The closed
H contains a point sM with s>=0. By (2), every such point has
first coordinate s M_x>=0, whereas all of H lies in x<=alpha<=0.
It follows simultaneously that

    s=0,       alpha=0,       O belongs to H.         (6)

In particular the entire alpha<0 domain is already excluded.
No physical circle mask or normal is changed at alpha=0.

Let tau_triangle denote the common directed cycle moment of
this original triangle. Its equality on all three actual edges
follows from the full zero-external-moment equations. If this
value were nonzero,
`TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY.md` would put a strictly
positive point sM, s>0, in H. Its positive first coordinate
contradicts H subset {x<=0}. Thus any survivor must have

    tau_triangle=0.                                 (7)

At H the true triangle pair-force sum is N=-M, by the complete
H equation and (5). Apply
`TRIANGLE_ZERO_MOMENT_PAIR_RAY_EXCLUSION.md`, Sections 1--4,
using (6)--(7). It gives the exact remaining restriction

    H intersect {-sM:s>0} is empty.                 (8)

This is the pair-force ray, with the opposite direction from
the full external M. No positive-external-ray statement has
been extended into its false zero-moment domain.

## 3. The full parallel C4 case enters the forbidden ray

In (3), H's actual right side now lies on x=0. Its two unchanged
port heights strictly straddle zero. Therefore O belongs to the
relative interior of that real H side. Since the unit square
extends a full width one to its left, it contains -sM for every
sufficiently small s>0, using M=(mu+lambda)e_x.

This contradicts (8). The strict straddling was proved from the
actual private equations and includes every original shared-side
mean and every possible parallel endpoint.

## 4. The full nonparallel C4 case also enters the forbidden ray

Use (4). If q belonged to H, its equality q=-tM with t>0
would contradict (8) directly. Hence q is outside H. Since
P,Q are actual points of H, this makes both original proper
distances strictly positive:

    a>0,      b>0.

Set

    Z=mu/b+lambda/a>0.

The convex combination of Q and P with positive weights
(mu/b)/Z and (lambda/a)/Z belongs to the same closed H and is

    X=((mu/b)Q+(lambda/a)P)/Z
     =q+M/Z
     =(1/Z-t)M.                                     (9)

Every point of H has first coordinate at most zero and M_x>0.
Consequently 1/Z-t<=0. A negative coefficient in (9) contradicts
(8). The only remaining possibility is

    X=O,       1/Z=t.                                (10)

Both convex weights in (9) are strictly positive. Both actual
ports have nonpositive first coordinates, so (10) forces both
of those coordinates to be zero. Moreover P_y=y_0<0 by (2),
and hence P is not O; equation (10) makes Q distinct from P
and gives Q_y>0. Thus the actual support line x=0 contains a
nondegenerate segment [P,Q] of H with O in its relative interior.

A nondegenerate segment of a square on a supporting line belongs
to an actual side. The point O is therefore in the relative
interior of H's actual right side. Since M_x>0, the vector -M
points strictly into its inward half-plane. Taking a sufficiently
small positive step in that vector also stays between the two
side endpoints. Thus

    -sM belongs to int H for all sufficiently small s>0.

This again contradicts (8). This last argument treats the exact
coefficient-zero endpoint; it does not discard it by continuity
or presume that an affine concurrence lies in a body.

Together Sections 2--4 exhaust both original cycle-moment values
and both complete terminal root-normal alternatives.

## 5. Exact original C3.344.b0 consequences

Use the five original terminal rooted types in
`MIXED_C3_344_COMPLETE_ATTACHMENT_AND_LOAD_REMAINDER.md`.
Its row 2 is the C4 with two adjacent private loads. In every
middle-triangle chain involving that row, H has exactly the
external system used above after retaining and then proving
zero its possible own circle force. The other terminal block
is at the other actual triangle vertex and keeps its complete
external force and moment system. The third triangle vertex
and all nine original squares retain their original equations.

Thus this source excludes, as entire original graph/load domains,

    (2,2), (2,3), (2,4), (2,5).

The pairs involving row 1 were already excluded by the separate
sole-opposite-C4 support theorem. After independent acceptance
of the present source, the remaining original middle-triangle
pairs are exactly the six pairs among rows 3,4,5:

    (3,3), (3,4), (3,5), (4,4), (4,5), (5,5).

These are existing table references, not new proof IDs. No
coarse-cell closure or equality exclusion is claimed merely
from this shorter necessary cover. The exact radius endpoint
and every original physical mask remain in the six domains.

All forces, means, true degrees, physical units and original
selected normals remain. No numerical certificate, Lean
compilation, CI, remote action or shared-ledger edit is used.
