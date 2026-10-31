# Radial-side bodies also obey the proper-contact inner-face capacity bound

**Status:** hand proof; two independent full mathematical reviews passed
on 2026-10-29, including the radial load split, degenerate contact
triangles, and the closed coordinate boundaries in the cap estimates.

Use the physical entirely loaded seven-ring of a hypothetical ten-square
packing with `6241/1600<=R^2<9/2`. Assume every pair contact is proper
`SV` or `VS`, in the support-face convention of
[SEVEN_RING_OWNERSHIP_ALPHABET.md](SEVEN_RING_OWNERSHIP_ALPHABET.md).
Assume each body with a unique geometric circle vertex belongs to one of

```text
U1, U6, U7, U10.
```

Radial-side bodies, with two geometric circle vertices and any nonnegative
split of the positive circle load between them, are now permitted.

**Theorem.** These hypotheses are impossible. All three inner squares
would lie in the centered disk of squared radius `83/50`, less than the
known three-square minimum `425/256`.

This extends [SEVEN_RING_INNER_FACE_CAPACITY.md](SEVEN_RING_INNER_FACE_CAPACITY.md).
It does not treat unique-circle rows U4,U5,U8,U9 or SS/VV pair contacts.
The unique-circle rows U2/U3 are independently excluded by
[LOADED_INCIDENT_MIXED_EXCLUSION.md](LOADED_INCIDENT_MIXED_EXCLUSION.md).

## 1. Only three local support patterns survive on a radial-side body

Rotate a radial-side square to

```text
C=[a,a+1] x [-1/2,1/2],       a>9/10,
S=a+1,       R^2=S^2+1/4.
```

Write its inner corners as `L=(a,-1/2)` and `U=(a,1/2)`, and its bottom
and top edges as D and T. The circle-load resultant is a positive multiple
of `(S,ybar)`, with `-1/2<=ybar<=1/2`. Neither circle corner can be a
physical contact. A neighbor beyond the outer edge would have a point
of first coordinate at least `S+1>R`, which is impossible. A neighbor
supported across the inner edge is strictly circle-clear by Section 3 of
[SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md), including
contacts at either endpoint of that edge. Thus neither vertical edge can
be an S incidence.

Keep the actual counterclockwise cycle order. The common contact torque
is strictly positive. At a bottom S incidence an inward force is `(0,h)`
with `h>0`; its origin torque is `x*h>0`, so D can only be incoming.
At a top S incidence the inward torque is negative, so T can only be
outgoing. At L, every strict inward normal has both components positive,
and its torque is `a*f_y+f_x/2>0`; thus L can only be incoming. At U,
every strict inward normal has positive first and negative second
component, giving negative torque; thus U can only be outgoing.

The remaining pairs are therefore D->T, D->U, L->T and L->U.
The pair D->T has both actual forces vertical and cannot supply the
strictly positive first component of the circle-load resultant. Exactly
three necessary local patterns remain:

```text
D -> U,       L -> T,       L -> U.                    (1)
```

This derivation is independent of ybar and does not require both geometric
circle vertices to carry positive load. The raw radial rows in the
ownership alphabet are covered by these three geometric patterns after
rotation.

## 2. Choosing a small core corner on each body

For a unique-circle body choose its opposite corner as before. On a
radial-side body use the following table:

| Local pattern | Core corner A_i | Circle vertex chosen for its nontrivial V incidence |
|---|---|---|
| D -> U | L | upper circle vertex `(S,1/2)` |
| L -> T | U | lower circle vertex `(S,-1/2)` |
| L -> U | U | lower circle vertex for the incoming contact L |

In the last row, the outgoing contact already equals the core corner.
The inner boundary follows the whole segment L U, and the outgoing
contact triangle will be degenerate. The chosen circle vertex is used
only for geometry; no assertion about its individual load is needed.

In each row the body path from its incoming contact through A_i to its
outgoing contact follows its inner boundary, with no self-intersection.
The two mixed rows use the same two-side boundary paths as the earlier
capacity theorem. A radial L->U body uses just its inner vertical side.

Every chosen core corner satisfies

```text
|A_i|^2 <= R^2+1-2sqrt(R^2-1/4)
         <= 11/2-sqrt(17) < 36/25.                    (2)
```

For radial bodies this is direct from `|L|^2=|U|^2=a^2+1/4`.
For unique-circle bodies it is the reviewed opposite-corner bound.

## 3. Every nondegenerate contact triangle has the old cap geometry

At a proper pair contact P, direct the pair temporarily from its S body
to its V body. Let A and B be the chosen core corners of those bodies.
If P=A or P=B, the contact triangle is degenerate and already lies in
the convex hull of the core corners.

Otherwise the local geometry is exactly

```text
w=(X,-Y),       X>=1/2, Y>=1/2,
C=w+[-1,0]u+[0,1]v,       u=(1,0), v=(0,1),
A=w-u+v,       P=A+t*u,       0<t<=1,
u'=(cos d,sin d),       v'=(-sin d,cos d),
C'=P+[0,1]u'+[0,1]v',       w'=P+u',       B=P+v',
0<d<pi/2,       |w|=|w'|=R.                           (3)
```

For a radial S body, the selected circle vertex in Section 2 gives
`X=S>1`, `Y=1/2`. For a radial V body in a nondegenerate triangle, its
selected circle vertex is adjacent to P, and B is its other inner corner,
exactly as displayed. A radial L->U body's outgoing triangle was already
removed as degenerate; its incoming one has P=L, B=U and uses the lower
circle vertex. Thus no inconsistent choice is made at that body's two
contacts.

The inward normal on C' is v. Strict V support makes both of its
coefficients in `(u',v')` positive and gives the stated acute angle.
The orientation bookkeeping is unchanged: an outgoing S incidence uses
a positive frame, whereas an incoming S incidence reverses traversal
and reflects the frame. The radial mixed rows have exactly those same
inner-boundary incidences. Consequently every nondegenerate triangle
`conv{A_i,p_i,A_(i+1)}` is counterclockwise in the original cycle order.
Degenerate triangles contribute zero to the oriented boundary identity.

There is no need to exclude t=0 by a strict farthest-corner sign: it was
removed as a degenerate triangle. The endpoint t=1 cannot occur for a
radial S body, since P would be its other circle vertex. For a unique
mixed S body, the previous local torque identity still excludes t=1.
Thus only a unique two-side body can require the t=1 cut.

## 4. The cap estimates retain all radial boundary cases

Suppose first that the S body has unique circle vertex and row U1.
The [side-source cap proof](SEVEN_RING_SIDE_SOURCE_CAP.md) gives squared
radius below `83/50`. Its proof of the nondegenerate cap inequality uses
only the equal-radius equation, the source body's two physical neighbors,
and the relevant own-frame coordinate signs. It does not require the V
body's second circle coordinate to be strictly above 1/2. In particular:

* The entire X<1 argument is unchanged: its estimates use the first
  body's `Y>1/2` and the equal-radius equation, and no strict second-body
  circle sign is a premise of its derivative or first-entry argument.
* For X>=1 and `0<t<1`, the chord and radial cap estimates discussed
  below apply with a nonstrict second-body coordinate as well.
* Its t=1 calculation gives second-body own circle coordinates `(Y,X)`
  with both coordinates at least one; that case is automatically unique.

Every other S body is mixed. For a unique-circle mixed body, the physical
neighbor at its other strict vertex gives X>1 by the unit-normal-step
calculation in Section 2 of the previous capacity theorem. For a radial
mixed body, X=S>1 holds directly. Thus in both cases

```text
X>=1,       Y>=1/2,       0<t<1.                       (4)
```

The reviewed [chord endpoint bound](SEVEN_RING_CAP_CHORD_BOUND.md)
explicitly allows Y=1/2 and gives squared norm below `33/20`.
Its other endpoint B has squared norm below `36/25`, by (2).
For the [radial extreme bound](SEVEN_RING_RADIAL_CAP_BOUND.md), the second
body's coordinate denoted Z is now allowed to equal 1/2. Every step of
that proof uses only Z>=0 in its auxiliary interval. Its final point
still satisfies Z>=1/2>0, so the interval has positive length and the
same first-entry proof applies. Therefore the full retained cap has
squared radius below `33/20<83/50`.

For `0<t<1`, the unit-square diameter-disk cut is purely local geometry
and does not assume either circle vertex is unique. For t=1, the only
remaining S type is the unique two-side body. The previous endpoint cut
uses only `X>1/2`, the acute angle d, and the inner square's center norm
below one; it likewise does not require the V body to have a unique
circle vertex. Thus every inner-square vertex in a nondegenerate
triangle belongs to the stated cap.

## 5. The boundary and the three-square contradiction

The chosen paths through the core corners concatenate to a simple inner
boundary. Proper S/V contacts are single points, nonneighbor loaded
bodies never touch, and each body path is simple. Some contact points
coincide with their own core corner; deleting the resulting zero-length
segments leaves the same simple boundary. The paths lie in loaded
bodies, so replacing the original center/contact ring preserves winding
number about zero. The boundary still encloses the half-radius disk and
therefore contains all three inner squares, by the connected-interior
argument of the previous capacity theorem.

As oriented chains,

```text
boundary(hole)
 = (A_0 A_1 ... A_6 A_0)
   + sum_i boundary(conv{A_i,p_i,A_(i+1)}).            (5)
```

Every summand is either a counterclockwise triangle or the zero chain.
Outside the convex hull of the core corners, the first polygon has
winding number zero. Therefore every point of the hole outside that
convex hull belongs to one of the nondegenerate contact triangles;
boundary points follow by closure. A degenerate triangle cannot add a
point outside that convex hull because P equals one of its two core
corners.

By (2), the core convex hull lies strictly in the centered disk of squared
radius `36/25`. By Sections 3--4, every inner-square vertex in any of the
remaining triangles has squared norm below `83/50`. Hence all vertices,
and therefore all three entire inner squares, belong to the centered
disk of squared radius `83/50`. The exact inequality

```text
425/256-83/50=1/6400>0
```

contradicts the established three-square minimum. This proves the theorem.

## 6. Remaining proper-contact rings

After this theorem and the incident mixed exclusion, every still-possible
proper SV/VS seven-ring must contain a unique-circle body with one of

```text
U4, U5, U8, U9.
```

Radial-side bodies alone no longer distinguish an open subfamily of the
proper-contact case. For a pure-arrow scheme (`r=0`), only mixed rows can
occur, so at least one U4 or U5 is necessary. For a source/sink scheme,
U4,U5,U8,U9 remain candidates. Pair-contact defects SS or VV are outside
this theorem. No full C04 closure is asserted.
