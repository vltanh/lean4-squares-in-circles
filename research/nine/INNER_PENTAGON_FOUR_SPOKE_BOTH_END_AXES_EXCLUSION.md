# A four-spoke pentagon cannot have both end normals owned by its hub

Date: October 28, 2026.

**Status: complete new hand local theorem and whole original interface,
frozen for full independent and root review.** No graph, load or ledger
flag is changed. This theorem is radius-free. It uses the original
strict point-normal convention and the full four-force hub equation.

## 1. Complete local and original scope

Let H,A,B,C,D,E be distinct actual closed unit squares with disjoint
open interiors and physical contacts

    HA, HB, HC, HD, AB, BC, CD, DE, EA.                 (1)

Assume the four positive pair forces at H are its entire positive
neighborhood A,B,C,D, and H has zero circle load. Assume D has zero
circle load and its entire positive neighborhood is H,C,E. No degree,
load or physical circle-mask hypothesis is imposed on A,B,C,E.

Use the unchanged strict point-normal convention of
PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section 2. In particular a
point-only vertex/vertex contact has a normal strictly exposing both
actual vertices. Positive-length shared sides retain their actual
aggregate means, including either endpoint-valued mean.

**Theorem.** The two actual normals from H to A and D cannot both be
side axes of H.

For the original H4_D0 pentagon, the exact substitution is

    (A,B,C,D,E)=(0,1,2,3,4).                           (2)

The physical rim is 012340 and all four original spokes H0,H1,H2,H3
remain. In both load representatives 124 and 0124, H is unloaded of
degree four and 3 is unloaded of degree three. Thus (2) proves the
entire both-H-owned-end-spoke interface of **both** original families.
The reflected four-load representative is handled by reversing the
rim path so its unloaded end is D. No force at H is dropped, and no
loaded or degree-three endpoint is treated as a two-force tip.

All nine actual squares, every original side mean and physical
one-/two-circle-corner mask remain. No circle equation, force at E,
canonical motion, inner-hole capacity or completion-square placement
is used below. The other end-owner interfaces remain open.

## 2. A strict coordinate reach fact

We use the elementary support-span argument of
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Section 1. If an actual
unit T has a minimum-n support point P and n dot u<0 for a unit
direction u, then

    max_(x in T) u dot (x-P)<1.                        (3)

For completeness, at a vertex P write the two inward orthonormal
axes v,w, so n dot v,n dot w>=0. Both u dot v and u dot w cannot
be positive, since that would imply n dot u>=0. At most one positive
component contributes to the maximum. That component is strictly
less than one: equality would make u an inward axis and again give
n dot u>=0. At a side support, the inward normal edge contributes
negatively and only a transverse interval of length at most one
contributes positively. Its projected unit component is strictly
less than one. This includes all actual side means and endpoints.

In particular, if n_x>0, every point of T has x>P_x-1; if n_x<0,
every point has x<P_x+1. The analogous strict statements hold in y.
These are statements about the entire physical unit, not only its
center or its force application.

## 3. The complete four-axis alternatives at H

Normalize H=[0,1]^2. Let n_A,n_B,n_C,n_D be its original outward
unit normals, with positive magnitudes a_A,a_B,a_C,a_D. Its complete
unchanged force equation is

    a_A n_A+a_B n_B+a_C n_C+a_D n_D=0.                (4)

For a side normal owned by H, the physical triangle theorem gives
nonnegative dot product with the other incident normal in that
triangle. Thus the actual triangles HAB and HCD give

    n_A dot n_B>=0,             n_D dot n_C>=0.        (5)

### 3.1. Equal end axes

If n_A=n_D, dotting (4) with that common axis is strictly positive
by (5). This is impossible.

### 3.2. Opposite end axes

Take n_A=East and n_D=West. Then

    n_B,x>=0,              n_C,x<=0,                 (6)

and the y coordinate of (4) says that n_B,y and n_C,y are either
both zero or have opposite strict signs.

If they are both zero, n_B=East and n_C=West. The actual units B,C
then lie respectively in x>=1 and x<=0, so cannot touch.

Otherwise reflect vertically if necessary so n_B,y>0>n_C,y.
If n_B,x>0 and n_C,x<0, the H applications are the opposite vertices
(1,1) and (0,0). Applying (3) to B in the West and South directions
gives B subset {x>0,y>0}. Applying it to C in the East and North
directions gives C subset {x<1,y<1}. Every common point of B and C
would therefore lie in int(H), impossible for actual units whose
open interiors are disjoint from H.

Here and below, even a boundary point of another closed unit cannot
lie in int(H): every neighborhood of that point meets the other
unit's open interior, producing an open-interior overlap.

If n_B,x=0, B lies in y>=1. When n_C,x<0, its strict southwest
vertex application at (0,0) and (3) give max_C y<1; when n_C,x=0,
C instead lies in y<=0. Both exclude BC. The remaining endpoint
n_C,x=0 with n_B,x>0 gives C subset {y<=0} and B subset {y>0}.
Thus all weak axis endpoints in (6) are covered. Opposite end axes
are impossible.

### 3.3. Perpendicular end axes

Up to a rigid motion and reflection take n_A=East and n_D=North.
Equation (5) gives n_B,x>=0 and n_C,y>=0. The x and y coordinates
of the full equation (4) then give

    n_C,x<0,              n_B,y<0.                   (7)

If both n_B,x and n_C,y are positive, their H applications are
(1,0) and (0,1). Formula (3) gives

    B subset {x>0,y<1},    C subset {x<1,y>0}.

Their intersection would again be in int(H). If n_B,x=0 but
n_C,y>0, B lies in y<=0 while C lies in y>0. If n_C,y=0 but
n_B,x>0, C lies in x<=0 while B lies in x>0. Each contradicts BC.

Consequently the only remaining possibility is exactly

    n_A=East, n_B=South, n_C=West, n_D=North.          (8)

This deduction kept all four original positive forces, used no
neighbor equation, and covered every strict vertex and owned-axis
endpoint. It did not assume a fan with degree-two end tips.

## 4. A degree-free equality lemma for two adjacent units

We prove the following physical statement. Suppose actual units B,C
touch, and

    max_B y=0,   max_C x=0,
    max_B x>=1,  max_C y>=1.                          (9)

Then necessarily

    B=[0,1] x [-1,0],     C=[-1,0] x [0,1].          (10)

Choose a topmost vertex (p,0) of B and a rightmost vertex (0,q) of C
so their complete actual frames can be written

    B=(p,0)+[0,1](-a,-b)+[0,1](b,-a),
    C=(0,q)+[0,1](-c,d)+[0,1](-d,-c),
    a,b,c,d>=0,        a^2+b^2=c^2+d^2=1.           (11)

Aligned squares are included by allowing a zero axis component;
no support mean is being chosen or replaced. Let a common physical
point have actual coordinates U,V in B and R,S in C, all in [0,1].
Equality of its two coordinate expressions gives

    p+b=a U-b V-c R-d S+b,
    q+d=-b U-a V-d R+c S+d.

Since max_B x=p+b and max_C y=q+d, their sum is exactly

    (a-b)U+(c-d)S-(a+b)V-(c+d)R+b+d
       <=max(a,b)+max(c,d)<=2.                       (12)

But (9) makes the sum at least two. Equality therefore holds, and
max(a,b)=max(c,d)=1. Both actual frames are aligned with the axes.
Write B=[l,l+1]x[-1,0] and C=[-1,0]x[m,m+1]. The last two
inequalities in (9) give l,m>=0; the actual BC intersection gives
l,m<=0. Hence l=m=0, proving (10).

The lemma retained arbitrary orientations and every common-point
endpoint. It uses neither a stress nor a containing-circle premise.

## 5. Actual outer frames and their entire slider intervals

In (8), B lies in y<=0 and C lies in x<=0, both touching H. The
actual AB contact, with A subset {x>=1}, gives max_B x>=1.
The actual CD contact, with D subset {y>=1}, gives max_C y>=1.
Lemma 4 applies, so the two unchanged middle squares are exactly (10).

Consider A. Its H support is min_A x=1. If A were not aligned,
this support would be a single actual vertex P. Because A touches
H, P_y is in [0,1]. Its physical contact with B in (10) must also
occur at P, since B has x<=1. That contact gives P_y<=0. Thus
P=(1,0), which is a vertex of both H and A, and their intersection
is point-only. The retained strict point-normal convention forbids
the actual H-to-A axis East at this two-vertex point.

Therefore A is aligned, and the two actual contacts give

    A=[1,2] x [r,r+1],               -1<=r<=0.       (13)

The same argument at D uses its minimum-y support and its contacts
with H and C. A nonaligned D would meet both at the H vertex (0,1),
where the North axis is again forbidden for a point-only contact.
Consequently

    D=[s,s+1] x [1,2],               -1<=s<=0.       (14)

We retain the full weak intervals in (13)--(14). At r=-1 or s=-1
the corresponding H contact is already incompatible with its
assumed axis under the strict convention, but the remaining argument
also excludes these enlarged endpoints. Every actual aggregate mean
on the original H sides is unchanged and unconstrained beyond its
real overlap interval.

## 6. The full unloaded D3 equation contradicts the last physical edge

D has precisely the three positive neighbors H,C,E and zero circle
load. Its original outward normal toward H is South. If s<0 in
(14), the actual CD intersection is a positive-length horizontal
side segment at y=1. Thus its normal toward C is also South,
with every original mean in that segment allowed.

The full D3 force equation consequently makes its E normal North.
The actual DE support is on D's top side y=2, so every point of E
has y>=2. This contradicts the actual AE contact, because (13)
gives max_A y=r+1<=1.

It remains the entire endpoint s=0. Now C and D meet only at
(0,1), the lower-left vertex of D and upper-right vertex of C.
Their original selected D-to-C normal strictly exposes both, so it
is southwest. Write the actual two force vectors from D to H and C
as (0,-gamma) and (-u,-v), respectively, where gamma,u,v>0.
The complete unchanged D3 balance gives the vector toward E as

    (u,v+gamma).                                      (15)

This has both coordinates strictly positive. Its actual D support
is therefore D's upper-right vertex P=(1,2), including all possible
owners and physical circle masks of E. At E, P is a minimum support
point for the same northeast unit normal. Apply (3) in the South
direction: every actual point of E has

    y>P_y-1=1.                                        (16)

Again (13) gives A subset {y<=1}, contradicting AE. Thus the zero
slider, point-only CD endpoint is excluded without replacing its
normal by South or altering any side mean.

Equations (15)--(16) use the full D3 force balance. No D torque,
E equation, missing H force, circle-resultant direction or geometric
triangle not present in (1) is substituted. This finishes the whole
local theorem and the two original interface applications in (2).

## 7. Frozen direct inputs and precise residual

| Actual input | SHA-256 |
| --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434 |

Only the triangle theorem's degree-free side-normal implication and
its elementary support span, the original strict vertex/vertex
normal convention, and the literal original graph/load mapping are
imported. The full proofs needed for the new equality and all feature
exits are given here. The closed four-ring cross theorem is not a
premise: there is no assumed physical or positive AC/AD end chord.

After this interface, the actual H4_D0 families still retain all
cases in which at least one of H0,H3 is not H-owned. This source
does not close either entire load family, their graph parent, or a
coarse six-body cell. It changes no source, metadata, force, normal,
mean or square and uses no numerical pose search, Lean or CI.
