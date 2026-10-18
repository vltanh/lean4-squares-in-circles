# Rational obstruction to independently pushing outer squares outward

**Theorem (counterexample).** There are two unit squares with both center
norms greater than one, each strictly contained in the disk of squared
radius q_plus=9789/2500, whose closed sets are initially *strictly
disjoint*. Moving the first center *radially outward*, without rotating
either square or moving the second, makes the interiors overlap while
both squares remain strictly contained in the **same disk**.

Consequently, even in the outer-center subgraph, one cannot push
squares independently toward disk contact while preserving their
pairwise disjointness. The private radial-ray theorem and the radial
escape theorem concern rays of *points*, not radial translations of
entire squares.

## Exact coordinates and frames

Let the first square S have center

    p=(51/50,0)

and orthonormal frame

    e=(323/325,-36/325),  f=(36/325,323/325).

Let T have center

    q=(18/25,107/100)

and orthonormal frame

    u=(111/689,680/689),  v=(-680/689,111/689).

These are genuine unit orthonormal frames: 323^2+36^2=325^2
and 111^2+680^2=689^2, with their other vectors the
counterclockwise perpendiculars.

For a square centered at a point a with frame (x,y), its
largest squared vertex norm is exactly

    Q(a;x,y)=|a|^2+1/2+|a dot x|+|a dot y|.                 (1)

Direct rational substitution gives

    Q(S)=86681/32500 <9789/2500,
    Q(T)=26688637/6890000 <9789/2500.                    (2)

The centers have norms |p|=51/50>1 and
|q|^2=(18/25)^2+(107/100)^2=16633/10000>1.

For any of the four side axes n=e,f,u,v the separating-axis
margin is

    g_n=|n dot(q-p)|
        -( |n dot e|+|n dot f|+|n dot u|+|n dot v| )/2.   (3)

All comparisons are rational. Here they are, before moving S:

    g_e = -6808131/11196250,
    g_f = +121709/22392500,
    g_u = -7639/447850,
    g_v = -498267/895700.                                (4)

In particular g_f>0 gives a separating line with a strict
positive gap; the two *closed* squares are disjoint.

## Outward translation creates overlap

Replace only the first center by

    p'=(6/5,0).

This moves S outward along its original center ray by
6/5-51/50=9/50>0. Its farthest vertex squared norm is now

    Q(S')=10613/3250 <9789/2500,                         (5)

so the translation has not broken disk containment. Both
centers remain outer.

With p' substituted in (3), all four separating-axis
margins become strictly **negative**:

    g'_e = -2402604/5598125,
    g'_f = -324763/22392500,
    g'_u = -10313/223925,
    g'_v = -6399/16900.                                  (6)

The separating-axis theorem for rectangles states that two
closed convex squares have disjoint open interiors if and
only if at least one signed side-axis projection gap is
nonnegative. All four absolute margins being negative
means strict interior overlap. This proves the counterexample
with no floating-point calculation.

## Consequence for the n=8 proof

This example involves only two squares; it does *not*
disprove the conjectured n=8 optimum. It rules out the
short-cut 'all outer centers may be independently moved
outward to their maximal radii' as an equivalence or
deformation of a full packing. The exact pairwise radial
endpoint **existential** lemma in HUMAN_RADIAL_ENDPOINT_PAIR.md
remains valid, because it changes the existence problem for
a single pair, not its specific initial placement or a full
multi-square packing.

Any reduction that requires every outer square to meet the
containing circle must first prove an additional collective
deformation theorem; it cannot follow merely from private
center rays or endpoint-wise pair feasibility.
