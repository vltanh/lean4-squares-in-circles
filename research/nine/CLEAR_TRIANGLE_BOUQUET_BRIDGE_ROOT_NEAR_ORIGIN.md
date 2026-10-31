# A clear triangle-bouquet root with one radial bridge is near the origin

Date: October 27, 2026.

**Status: accepted complete hand proof at its full stated original scope; root and separate independent full-source/scope reviews passed.**

Accepted reviews: REVIEW_TWO_TRIANGLES_FOUR_BRIDGES_MIXED_BLOCKS_2026_10_27.md and
REVIEW_TWO_TRIANGLE_FOUR_BRIDGES_AND_OPPOSITE_D_ROOT_ROOT_2026_10_27.md.
Source pins in those reviews precede this acceptance-only header update. No central ledger or original gate is changed.

Retain all original units and the common compatible selected certificate
in 79/40<=R<=sqrt(1105)/16, and put

    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Let H be physically circle-clear and carry one or more actual triangle
blocks, with all their original pair forces retained. Suppose its only
other positive pair edge is one actual bridge to K, or there is no
other positive pair edge. Every triangle's full external origin moments
are assumed zero, as supplied by genuine private branch sums in the
original block tree. There is no degree or circle-load assumption on
the other vertices or the actual bridge endpoint K.

**Theorem.** With no outside bridge, O belongs to the closed H. With
one outside bridge, H meets the closed disk D_epsilon.

## 1. A unit's genuine radial support contains the whole inward unit segment

Let an actual unit S have radial supporting point p=x e and lie in
e.z<=x. Then

    (x-t)e belongs to S for every 0<=t<=1.               (1)

If e is an actual side axis, this is its unchanged perpendicular unit
segment, at the same transverse coordinate as p; side-mean endpoints
are included. Otherwise p is its unique support vertex. In its inward
orthonormal axes u,v, the displacement -t e has coordinates
t(-e.u),t(-e.v), both in [0,1], because both coefficients are positive
and at most one. Thus (1) holds for the complete vertex alternative too.

If a contained unit is on the far side e.z>=x, its center projection
is at least x+1/2 and its norm at most d+1/2. Therefore

    x<=d.                                               (2)

Consequently any such support with x>=0 makes S meet D_epsilon:
if x<=1 take t=x in (1), giving O; if x>1 take t=1, giving a point
of norm x-1<=d-1=epsilon. These are original physical points, not
new shared contact means.

## 2. The full triangle rays and the actual root equation

For each actual triangle at H, let N_j be the sum of its two genuine
outward H forces. Its complete external resultant at H is exactly
-N_j, whatever the other root groups are. The general theorem
`TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY.md` gives

    P_j=-t_j N_j in H,          t_j>=0.                 (3)

Each N_j is nonzero by the full external-resultant theorem. If any
t_j=0, O belongs to H and the claimed conclusion follows immediately.
Otherwise all t_j are strictly positive. Put Z=sum_j(1/t_j)>0.
The actual convex combination of (3) with weights (1/t_j)/Z is

    -(sum_j N_j)/Z in H.                               (4)

With no other root pair edge, physical clearance and the full H
equation give sum_j N_j=0. Equation (4) proves closed O containment.

With one outside bridge, write its original force beta e, beta>0,
directed from H toward K. Its complete actual branch torque makes
the unchanged application p=x e, with H in e.z<=x and K in e.z>=x.
The full root equation is

    sum_j N_j+beta e=0.

Thus (4) is a strictly positive multiple of e in H. Its support
inequality forces x>0. In the earlier t_j=0 alternative, O in H
instead gives x>=0. In either case (1)--(2) prove H meets D_epsilon.

This uses every original root triangle and the bridge force. It does
not assign a smaller degree to H, remove a possible K circle load,
or require nonzero triangle moments or strictly positive ray parameters.
It applies equally to one actual triangle at a degree-three root and
two actual triangles at a degree-five root with one genuine arm.

All physical masks, individual zero circle weights, common means and
remaining original units are retained. No normal reselection, numerical
certificate, physical motion, Lean compilation, CI or remote action is
used.
