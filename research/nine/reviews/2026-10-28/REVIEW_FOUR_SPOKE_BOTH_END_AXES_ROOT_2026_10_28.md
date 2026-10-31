# Full root review: both hub-owned end normals in the four-spoke pentagon

Date: October 28, 2026. Reviewer: root.

**Mathematical verdict: accepted unchanged for the entire stated local
interface, subject to the distinct full independent adoption review.**
I read all of the new source and all three frozen direct inputs. I
independently rederived the support-span argument, all four-force hub
alternatives, the arbitrary-orientation two-square equality lemma,
both complete outer slider intervals, and the full unloaded end
equation. No radius estimate, smaller-degree balance or completion
capacity is used.

Source: `INNER_PENTAGON_FOUR_SPOKE_BOTH_END_AXES_EXCLUSION.md`,
SHA-256
`e1106b043b8b6b61899177a7e68121fce49c65e3ebf86273ef332cf451f437bf`.

## 1. Literal original scope and unchanged certificate

The actual six units are H,A,B,C,D,E with contacts
HA,HB,HC,HD,AB,BC,CD,DE,EA. H has exactly the four positive
neighbors A,B,C,D, and D exactly the three H,C,E; both are
unloaded. No equation or degree restriction is imposed on A,B,C,E.
The statement assumes that the actual H-to-A and H-to-D normals
are axes of H. It does not choose or change either normal.

The original substitution is A=0,B=1,C=2,D=3,E=4 in the no-chord
four-spoke pentagon. The genuine degrees are 4 at H, 3 at each of
0,1,2,3, and 2 at 4.
Both positive-load representatives 124 and 0124 leave H and 3
unloaded. The reflection i maps to 3-i modulo 5 preserves every
spoke and rim edge and moves the alternative unloaded end into 3.
All nine units and every other force, circle mask, individual zero
circle weight and original shared-side mean remain present.

I reread the complete load-cover source, especially its Section 6,
and the complete physical-graph selection source. The latter fixes
strictly exposing normals at point-only vertex/vertex contacts
before obtaining multipliers; subsequent uncrossing and thinning
preserve that property. This existing convention is used literally,
not imposed after extraction. Positive-length side contacts retain
their actual endpoint-weighted means.

## 2. The strict coordinate reach estimate

At a minimum-n support vertex P of a unit square, its inward unit
axes v,w have nonnegative n components. If n dot u<0, the two
u components cannot both be nonnegative: otherwise their expansion
would give n dot u>=0. At most one positive component contributes
to the maximum u reach, and it is strictly less than one. Equality
would make u an inward axis and contradict the same strict sign.

At a side-interior support the inward normal component contributes
negatively, and the available tangential interval has length at most
one and projected unit component strictly below one. Thus the same
strict estimate holds for every mean, including both side endpoints.
This proves the source's whole-unit fact, without any stress or
containing circle. I also checked its use at arbitrary-degree
triangles against the full direct triangle source.

The elementary closure point used later is sound: a point of a
second closed square lying in the open interior of H would have
nearby points of the second square's open interior still inside H.
Consequently open-interior disjointness excludes even such boundary
points, not merely an open intersection of the two exterior squares.

## 3. Every alternative for the two H axes

Normalize H to [0,1]^2 and retain its four positive magnitudes.
The actual triangles HAB and HCD, with the stated owned end axes,
give n_A dot n_B>=0 and n_D dot n_C>=0. These are arbitrary-degree
physical implications; neither end is treated as a two-force tip.

If the end axes agree, the dot product of the full H4 equation with
that axis is strictly positive. If they are opposite, take A East
and D West. The other normals have n_B,x>=0 and n_C,x<=0, and
the full y equation requires both y components zero or opposite in
strict sign. The zero case puts B in x>=1 and C in x<=0. In the
strict case, after reflection, a strict NE B and strict SW C would
have every common point inside H by the coordinate reach estimate.
If either x component is zero, one unit is entirely beyond a
horizontal H side and the strict estimate for the other separates
them strictly. If both are zero, they lie above and below opposite
sides. This covers the weak-axis endpoints without discarding a
positive hub force.

The remaining end axes are perpendicular. Take A East and D North.
The full x and y equations give n_C,x<0 and n_B,y<0. If both
other components are positive, the strict SE and NW applications
again force any BC common point into the open H interior. If just
one is zero, the exact horizontal or vertical side and the strict
reach of the other unit separate them. The only surviving normals
are exactly A East, B South, C West, D North. These cases exhaust
all four possible axes for either end, modulo actual rigid motions
and reflection.

## 4. The complete two-square equality lemma

With max_B y=max_C x=0, take actual extreme vertices and full
frames

    B=(p,0)+[0,1](-a,-b)+[0,1](b,-a),
    C=(0,q)+[0,1](-c,d)+[0,1](-d,-c),

where all four coefficients are nonnegative and each axis pair is
unit. Zero components include every aligned frame. These are
physical frames, not replacements of an application mean.

At an arbitrary actual common point with four coordinates U,V,R,S
in [0,1], I independently eliminated p,q and obtained

    max_B x+max_C y
      =(a-b)U+(c-d)S-(a+b)V-(c+d)R+b+d
      <=max(a,b)+max(c,d)<=2.

The four ordering possibilities a>=b or b>=a and c>=d or d>=c
give the stated box maximum, including all coefficient-zero faces.
The AB contact and A subset x>=1 imply max_B x>=1; CD and D
subset y>=1 imply max_C y>=1. Equality is therefore forced.
Each maximum of the nonnegative coefficients equals one, so both
frames are aligned. Writing their remaining shifts as l,m, the
projection bounds give l,m>=0 and their physical intersection gives
l,m<=0. Thus B=[0,1]x[-1,0] and C=[-1,0]x[0,1] exactly.

No orientation sample, strict common-point assumption or unlisted
contact is needed. In particular, BC may be a point-only contact;
the equality argument uses only its actual nonempty intersection.

## 5. The whole outer frames and the strict normal convention

A has minimum x equal to one. If it were nonaligned, that support
would be a single vertex. Contact with H puts its y coordinate in
[0,1], while contact with the now exact B puts it in [-1,0]. The
vertex must be (1,0), a vertex of H as well. Their intersection is
point-only. East does not strictly expose H's vertex, contradicting
the original selected-normal convention. Hence A is aligned.

Both physical contacts then give the full actual interval
A=[1,2]x[r,r+1], -1<=r<=0. The identical argument for D gives
D=[s,s+1]x[1,2], -1<=s<=0. The intervals are deliberately weak:
r=-1 and s=-1 would already fail the point-normal convention, but
retaining them enlarges the domain and causes no loss in the final
contradiction. No original H side mean is changed or fixed.

## 6. All three D forces, including the zero-slider endpoint

For -1<=s<0, CD has a genuine positive-length horizontal common
side at y=1, so the D-to-C normal is South. D-to-H is also South.
The complete D3 equation then forces D-to-E North. Every point of
E has y>=2, while every point of A has y<=1. Thus the actual AE
edge is impossible, for every original mean on both South sides.

For s=0, CD is point-only at (0,1), the lower-left D vertex and
upper-right C vertex. Its unchanged selected normal is strictly
Southwest. Writing the two original forces toward H,C as
(0,-gamma),(-u,-v) with gamma,u,v>0, the third actual vector is
(u,v+gamma), strictly Northeast. Its support on D is (1,2).
At E this is a minimum support point for the same NE normal.
The strict South reach estimate puts every point of E above y=1,
again contradicting AE. It includes every possible E frame, degree,
mask and support owner. The endpoint is not treated as a South
side, and no third D force or corner normal is removed.

## 7. Exact record and acceptance boundary

The supporting exact record is
`/tmp/pr11_root_h4_both_end_axes_checks_20261028.json`, generated
by the correspondingly named Python script. It checks all four
frozen pins, both common-point coordinate identities, the span
identity, all four linear-box ordering cases, both full endpoint
force coordinates, the literal degree and load maps, and the actual
graph-preserving reflection. The continuous support and equality
arguments above supply the proof; the code is only exact algebra
and interface verification, with no pose sampling.

I accept the entire stated local theorem and both original
both-H-owned-end interfaces unchanged. The separate full independent
review remains required for adoption. Neither whole H4 load family,
their graph parent nor a coarse cell is closed by this interface.
There is no circle estimate, force deletion, canonical motion,
missing-chord assumption or completion-square placement. No Lean
compilation, CI, workflow, remote mutation or merge was performed.
