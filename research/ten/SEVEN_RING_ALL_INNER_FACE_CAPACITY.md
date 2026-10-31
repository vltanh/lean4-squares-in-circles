# A selected loaded ring must contain a weak opposite-corner body

**Status:** hand selection and capacity theorem; two independent full
mathematical reviews passed on 2026-10-29, including the joint open-normal
selection, all rational margins, and the global triangle reduction.

Assume a strictly subcritical ten-square packing exists and take an
unrestricted radius minimizer. The radius window is
`6241/1600<=q=R^2<9/2`. Select a physical stress before classifying its
components, strengthening the selection of
[LOADED_VV_GENERIC_RESTRICTION.md](LOADED_VV_GENERIC_RESTRICTION.md)
by the additional open-interval restrictions below.

**Theorem.** Every entirely loaded positive seven-ring of this selected
stress contains a unique-circle body of type U4,U5,U8 or U9.

Equivalently, if all its unique-circle rows are U1,U6,U7,U10, the ring
cannot enclose three inner squares. This permits every radial-side body
and every pair-support type SS,SV,VS,VV. Rows U2/U3 were already excluded
by the incident mixed theorem. The theorem does not close the remaining
weak opposite-corner rows or unrestricted n=10.

The proof retains the core-corner construction and SS boundary replacement
from [SEVEN_RING_SHARED_SIDE_CAPACITY.md](SEVEN_RING_SHARED_SIDE_CAPACITY.md).
It supplies a bound for VV contact triangles that was missing there.

## 1. A VV pair with circle vertices adjacent to its contact is symmetric

Consider two loaded squares meeting at a strict VV contact P. Suppose
each has a geometric circle vertex adjacent to P, and choose such a
vertex on each square. This is automatic for good unique-circle V
incidences, and for radial V incidences with the choice in the radial
capacity theorem. The exceptional radial outgoing contact that already
equals its core corner gives a degenerate triangle and needs no geometry.

Rotate so `P=(r,0)`, where r>0. The two unit steps from P to the selected
circle vertices have equal scalar product with P, because the circle
radii are equal. They are distinct: coincident steps would give a shared
point of the containing circle, which is impossible. Thus, after naming
the upper and lower square, the steps and inward companion edges are

```text
u_+=(c,s),       v_+=(-s,c),
u_-=(c,-s),      v_-=(-s,-c),
c=cos theta,    s=sin theta,       0<theta<pi/2.       (1)
```

To justify the range, initially the two steps have angles ±theta with
`0<theta<pi`. A selected farthest circle vertex forces the perpendicular
companion edge to point toward the origin, so the displayed v signs are
necessary. If theta>pi/2 the two square interior sectors overlap at P.
If theta=pi/2 they share their whole leftward incident side and cannot
have strict VV support. Hence theta<pi/2.

The two core corners in a nondegenerate triangle are

```text
A_-=(r-s,-c),       A_+=(r-s,c),
q=r^2+1+2r*c,
r=sqrt(q-s^2)-c,
X=rc+1,       Y=rs,       X^2+Y^2=q.                  (2)
```

These X,Y are the own-frame circle coordinates on both squares.
For unique circle vertices Y>1/2; for a radial selected vertex Y=1/2.
Always X>1. The counterclockwise contact triangle has vertices
`A_-,P,A_+` and positive signed double area `2s*c`.

The body centers have first coordinate `r+(c-s)/2>0` and opposite
nonzero second coordinates. Here `r>R-1>=39/40` because P is one unit
from a circle vertex. Thus the lower square precedes the upper one in
the physical counterclockwise ring. The positive pair force f points
from the lower square into the upper square.

## 2. The only cap problem has two unique mixed endpoints

If either endpoint is radial, P is one of that body's inner corners.
It has squared norm below `36/25`, as do both core corners. Their whole
triangle therefore has that bound by convexity.

Now suppose both endpoints have unique circle vertices. Apply the generic
VV restriction: either such a pair does not belong to the selected
loaded ring, or each endpoint's other pair is SS on a positive-length
shared segment, with aggregate application in its relative interior.
Each endpoint is mixed. In the present good-row scope those bodies are
U6/U7, so their other support edges are the inner edges opposite v_±.

On the upper body, write that other application as

```text
Q=P+v_+ + t*u_+,       0<t<1.                         (3)
```

The interval will be made more precise below. Normalize its positive
circle coefficient to lambda>0 and write its outgoing S force as
`mu*v_+`, with mu>0. Force balance gives

```text
f=lambda*w_+ + mu*v_+.
```

Equality of the two origin torques gives

```text
mu*t=lambda*Y,
f=lambda*(X*u_+ + k*v_+),
k=Y*(1-t)/t>0.                                       (4)
```

Indeed the torque at P is `lambda*rs+mu*rc`, while that at Q is
`mu*(rc+t)`. These are local force/torque identities for the actual
positive stress, not a movement of the SS application point.

Let phi be the angle of f in the coordinates of (1). The open common
normal interval at this VV contact is exactly

```text
max(theta,pi/2-theta)<phi<min(pi/2+theta,pi-theta).     (5)
```

Equation (4) consequently requires

```text
t=Y/[Y+X*tan(phi-theta)].                             (6)
```

## 3. A loaded SS neighbor gives an exact upper bound on t when Y<1

Assume `1/2<Y<1`. Work in the upper body's `(u_+,v_+)` coordinates.
The body and its shared side are

```text
C=[X-1,X] x [-Y,1-Y],       Q=(X-1+t,1-Y).
```

A neighbor on the other side of this support edge is parallel and lies
in `v in [1-Y,2-Y]`. Since `1/2<Y<1`, its farthest vertical coordinate
is `2-Y`. Being loaded, its farthest horizontal coordinate has absolute
value

```text
Z=sqrt(q-(2-Y)^2)>1.                                  (7)
```

The last inequality follows from `q>=6241/1600` and `2-Y<3/2`.
A negative farthest horizontal coordinate would put the neighbor's whole
horizontal interval strictly below zero, whereas `X-1>0`; it could not
touch C. Hence the neighbor is exactly

```text
[Z-1,Z] x [1-Y,2-Y].
```

Also

```text
Z^2-X^2=4(Y-1)<0,
0<t<=T:=1-X+Z<1.                                     (8)
```

The weak lower endpoint in the actual overlap is t=0; the generic
restriction had already excluded it as an aggregate contact. Only the
upper bound in (8) is needed below.

## 4. Choose normals to remove the dangerous part of the VV geometry

For every geometric point-only VV contact between two unique-circle
squares whose circle vertices are adjacent to the contact, compute the
fixed parameters (1)--(2). Impose an additional open normal-interval
restriction when Y<1 and either

```text
(a) theta>=pi/4,   or
(b) theta<pi/4 and r^2>=83/50.                         (9)
```

We show that in either case a nonempty interval immediately above the
lower endpoint in (5) makes the required t in (6) exceed T. A positive
loaded ring using this pair would then contradict (8).

In case (a), the lower endpoint is phi=theta. The limit of (6) there is
one, which is strictly greater than T. Continuity gives the required
nonempty open interval inside (5).

For case (b), the lower endpoint is `phi=pi/2-theta`, and the limiting
value is

```text
t_lim=Y/[Y+X*cot(2theta)].                            (10)
```

Here are explicit rational bounds proving `t_lim>T` throughout the
whole case, rather than just at theta=pi/4.
First `r^2>=83/50>81/49` gives r>9/7. From q<=9/2,

```text
c=(q-r^2-1)/(2r)<=23/(25r)<5/7.                       (11)
```

For the last comparison, squaring positive sides reduces to

```text
25*625*83-529*49*50=825>0.
```

As theta<pi/4, also `c>1/sqrt(2)>7/10`. Equation (11) gives
`s>2/3`, because `1-25/49=24/49>4/9`. Consequently

```text
0<cot(2theta)=(2c^2-1)/(2sc)<15/686<1/40,
X/Y=c/s+1/(rs)<15/14+7/6=47/21<9/4.
```

Substitution in (10) gives

```text
t_lim>160/169.                                       (12)
```

For an upper bound on T, note that r increases with theta and with q
on `0<theta<=pi/4`: its theta derivative from (2) is
`s*(1-c/sqrt(q-s^2))>0`, since q>1. Therefore

```text
r<=2-1/sqrt(2),
Y=rs<=sqrt(2)-1/2<13/14,
X+Z<2X<2R<=3sqrt(2)<30/7.
```

These inequalities use `sqrt(2)<10/7`. Equation (8) now gives

```text
X-Z=4(1-Y)/(X+Z)>1/15,
T<14/15<160/169<t_lim.                               (13)
```

The middle rational comparison is `14*169=2366<2400=15*160`.
This proves the strict gap in case (b), so continuity again supplies
an open interval of normals with t>T.

Make this restriction independently for every pair satisfying (9).
For the other geometric point-only VV pairs keep any nonempty open
admissible interval. Now perform the finite nonzero-polynomial avoidance
of the generic VV theorem inside the product of these restricted open
intervals. A nonzero polynomial cannot vanish on this smaller open box,
so all the generic, strict, nonradial and nondiagonal exclusions remain
simultaneously available. The physical stress existence proof applies
to every such strict choice, as before.

After this selection, no loaded seven-ring can contain a VV pair in
(9) with both good unique-circle endpoint bodies. If it did, the generic
restriction would first force the SS neighbors, and (4)--(8) would then
contradict the chosen normal interval. The argument does not assume that
an old positive graph survives reselection.

## 5. The remaining VV triangles have squared vertex radius below 83/50

If `theta<pi/4` and `r^2<83/50`, all three triangle vertices have squared
norm below `83/50`: P has that bound by hypothesis, and the two cores
have the stronger bound below `36/25`. Thus the whole triangle does.
Together with Section 2, this already covers all radial cases.

The only other surviving unique-circle case has `Y>=1`. This implies
`theta>pi/4`, because the bound `Y<=sqrt(2)-1/2<1` in Section 4 applies
whenever theta<=pi/4. Since X>1 and Y>=1,

```text
|A_-|^2=|A_+|^2=(X-1)^2+(Y-1)^2<49/64.               (14)
```

This is the reviewed elementary corner bound for two own coordinates
at least one. To use it, we need the diameter-disk cut for an inner square
vertex z in the triangle.

At P the two forbidden square sectors leave an inner free sector of
angle `pi-2theta<pi/2` and an outer free sector of angle `2theta<pi`.
If an inner square contained P, its local interior sector could only
fit in the outer one. Thus P would be its vertex, with both incident
unit edges having strictly positive first coordinate. Its center would
have first coordinate greater than r>1, contradicting the inner-center
bound. Here r>1 follows from theta>pi/4, q>=6241/1600 and
`q>2+sqrt(2)`, by the formula for r in (2). Therefore P does not belong
to any inner square.

Translate P to zero. The two core vectors have length one and scalar
product `s^2-c^2>0`. The endpoint version of the diameter-disk cut in
Section 3 of [SEVEN_RING_INNER_FACE_CAPACITY.md](SEVEN_RING_INNER_FACE_CAPACITY.md)
now applies verbatim: if `(A_--z) dot (A_+-z)>0`, the entire triangle is
in the open unit disk centered at z. Both unit edges of the inner square
must leave the triangle through its core-to-core base, because they
cannot cross the two occupied unit sides or pass through P. That base
subtends an angle less than pi/2, contradicting perpendicular edges.
Hence z belongs to the disk with diameter A_- A_+.

The elementary diameter-disk norm estimate and (14) give

```text
|z|^2<=|A_-|^2+|A_+|^2<49/32<83/50.                  (15)
```

Thus every inner-square vertex in every remaining VV triangle has the
required strict bound.

## 6. The global capacity argument now allows every pair type

Retain the core corners from the radial theorem. For SS pairs replace
only the geometric boundary point by the inner overlap endpoint from
the shared-side theorem. For point pairs retain their actual point.
All body paths through their cores remain simple. At an SS pair they
meet only at the selected inner endpoint; at an SV or VV pair the whole
body intersection is that single point. Nonneighbors cannot touch.
Thus the paths give the same simple inner boundary enclosing all three
inner squares, with the same winding-number preservation as before.

The oriented triangle identity remains

```text
boundary(hole)
 = (A_0 A_1 ... A_6 A_0)
   + sum_i boundary(conv{A_i,q_i,A_(i+1)}).            (16)
```

SS triangles are zero. Proper SV/VS triangles are counterclockwise or
zero by the radial theorem. A VV triangle is either zero because a core
already equals its contact, or has the positive orientation verified in
Section 1. Hence every hole point outside the core convex hull belongs
to one of the nondegenerate contact triangles.

The core hull has squared radius below `36/25`. The reviewed proper-pair
cap theorem and Section 5 put every inner-square vertex in every remaining
triangle below squared radius `83/50`. Thus all three whole inner squares
lie in that disk. This contradicts

```text
425/256-83/50=1/6400>0.
```

All pair types have now been included. Therefore a loaded seven-ring of
this selected certificate must contain a unique-circle row outside
U1,U6,U7,U10. The incident mixed theorem already excludes U2/U3; the only
remaining unique-circle candidates are U4,U5,U8,U9, as claimed.
