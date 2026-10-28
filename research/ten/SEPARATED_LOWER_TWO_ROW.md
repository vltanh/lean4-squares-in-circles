# Two-row cores whose lower pair need not touch

**Handoff status:** draft proof; the independent audit was incomplete when
work paused. In particular, review the virtual-rectangle slot argument and
the reuse of the earlier arc and cap bounds before relying on this extension.

Suppose a packing in the origin-centered disk of squared radius `9/2`
contains four axis-parallel unit squares with centers

```text
(-a,-t), (a,-t), (-b_L,1-t), (b_R,1-t),
1/2<=a<=1/sqrt(2),       0<t<=5/12,
b_L+b_R>=1,
b_L^2+(1-t)^2<=1,  b_R^2+(1-t)^2<=1.
```

Then at most five additional unit squares fit, even with independent
orientations. This removes the touching-lower-pair hypothesis from the
small-displacement two-row theorem. In particular it covers every such
core whose lower centers have norm at most `13/20`, allowing a horizontal
gap between them. No radial count certificate is used.

This theorem still requires the exact common-frame two-row arrangement,
vertical row separation one, and a lower pair symmetric about the vertical
axis. These hypotheses have not been proved for arbitrary four inner
squares.

Write

```text
r=sqrt(1+1/sqrt(2)), A=(sqrt(17)-1)/2,
h=1/2-t, z=3/2-t, d=a-1/2,
gamma_a=acos((a+1/2)/r), gamma_0=acos(1/r),
t_0=2^(-1/4)-1/2.
```

As before, the upper-center constraints imply

```text
t>=1-sqrt(3)/2>1/8,
3/16<b_L,b_R<13/16,
z>=13/12>27/25.
```

## 1. All additional centers are exterior to the unit disk

The lower core horizontal intervals are
`[-a-1/2,-d]` and `[d,a+1/2]`. Their union covers `[-1,1]` except for
the middle opening `[-d,d]`, with `d<1/4`.
Below height h, a point of the unit disk is therefore at squared distance
less than

```text
(1/4)^2+(3/8)^2=13/64<1/4
```

from the lower pair: the horizontal miss is at most d, and the vertical
miss below the bottom `-t-1/2` is at most `1/2-t<3/8`.

Above h, the upper-pair clearance proof in
[ASYMMETRIC_TWO_ROW_COMPLETION.md](ASYMMETRIC_TWO_ROW_COMPLETION.md)
is unchanged. The common top z exceeds one, and every horizontal miss
from their union is less than `1/2`.

Thus every additional center has norm `1<u<=A<25/16`. Its square has a
single connected test-circle arc of angle at least `pi/4`, and its radial
test-circle point is in its open inscribed disk.

## 2. The ordinary arc and upper-clearance argument survives the gap

The identities `r cos(pi/8)=1/2+1/sqrt(2)` and `a>=1/2` give

```text
pi/8<=gamma_a<=gamma_0<pi/4.
```

The lower squares' upper outside corners lie strictly inside the test
circle: `(a+1/2)^2<=r^2-1/4` and `h^2<1/4`.
Their inner corners are also inside, since
`d^2+(t+1/2)^2<1/16+(11/12)^2=65/72<1`.

If `(a+1/2)^2+(t+1/2)^2<=r^2`, the lower squares do not cross the
test circle. In particular `t<=t_0`. The noncrossing proof in Section 1
of [EXTREME_ASYMMETRIC_TWO_ROW.md](EXTREME_ASYMMETRIC_TWO_ROW.md)
uses only this fact, the upper core, and exterior additional centers.
It therefore applies without change.

Otherwise the lower traces have the former endpoints with gamma_a in
place of gamma_0, and

```text
delta=asin((t+1/2)/r)>gamma_a>=pi/8.
```

When both upper offsets are at least `1/4`, retain their quadrant arcs as
in [ASYMMETRIC_TWO_ROW_COMPLETION.md](ASYMMETRIC_TWO_ROW_COMPLETION.md).
The four complementary gaps are

```text
pi-beta_L-beta_R,
alpha_L+gamma_a,
pi-2delta,
alpha_R+gamma_a.
```

They have capacities at most one, two, two, and two. Both side gaps cannot
hold two arcs. Indeed this would force both lower upper-square endpoints
to be x-bound endpoints and give

```text
b_i+1/2<=r sin(gamma_a)
 =sqrt(r^2-(a+1/2)^2)<=2^(-1/4),
```

so `b_L+b_R<=2t_0<1`.

Thus six additional squares require an upper-gap square and a side gap
holding two. The latter forces one `b_i<=t_0`; consequently the middle
opening of the upper pair has width

```text
g=b_L+b_R-1<11/32+13/16-1=5/32<4/25.
```

The upper-gap angle forces `z<=H=(1+sqrt(2))/2` and equal endpoint
angles `beta=asin(z/r)`. The center-clearance proof in Sections 3 and 4
of the asymmetric manuscript now applies unchanged: it uses only this
upper sector and the upper core, not the touching of the lower pair.
It excludes the required upper-gap square.

## 3. Extreme upper asymmetry and a virtual filled rectangle

It remains to treat a crossing lower pair with, after reflection,

```text
b:=b_R<1/4,       b_L>=1-b>3/4.
```

The upper-left center bound implies

```text
t>1-sqrt(7)/4>1/3.
```

Retain its second-quadrant trace and the two lower traces, ignoring the
small upper-right trace. Their three complementary gaps have capacities
one, two, and three, exactly as in Section 2 of
[EXTREME_ASYMMETRIC_TWO_ROW.md](EXTREME_ASYMMETRIC_TWO_ROW.md), with
gamma_a replacing gamma_0. The upper-left trace has endpoints
`[pi-beta,pi-alpha]`, where

```text
beta=asin(z/r),       pi/4<beta<3pi/8,
0<alpha<pi/8.
```

These follow from `z<7/6<H`, `b_L+1/2>5/4>H`, and the same inner-edge
bound as before. The large gap has lifted angular interval
`[-gamma_a,pi-beta]`. Six additional squares would need three there.

Here `g<1/16`, so the previous upper-sector clearance proof excludes every
additional center with angle in `[beta,pi-beta]`. Each large-gap square
therefore has center `(x,y)` satisfying

```text
-gamma_a<=arg(x,y)<beta,
x>0,       -9/8<y<25/16.                            (1)
```

Consider the virtual filled rectangle

```text
J=[b-1/2,b+1/2] x [-t-1/2,z].
```

Its upper half is the small upper-right core square. Its lower half is
covered by the lower core pair except for the open vertical slot

```text
G=(-d,d) x (-t-1/2,h).
```

The slot's two sides and top are contained in actual core squares; only
its bottom is open to the exterior. If d=0, J is already wholly in the
core. For d>0 we prove that no large-gap square can enter G either.

Suppose an interior point p of such a square S were in G. Its center c
is outside G, because every point of G has squared norm less than
`d^2+(t+1/2)^2<65/72<1`, whereas c has norm greater than one.
On the other hand, its horizontal coordinate is bounded by

```text
0<x<d+1/sqrt(2)<=sqrt(2)-1/2<11/12.
```

The circumradius `1/sqrt(2)` justifies the distance from p to c.
The angular restriction in (1), together with
`tan(gamma_a)<=tan(gamma_0)=2^(-1/4)<17/20`, now gives

```text
y>=-x tan(gamma_a)>-187/240>-5/6>-t-1/2.
```

Thus the segment from p to c remains strictly above the slot's bottom.
It lies entirely in S's interior and must exit G, since c is outside G.
Its first exit is through a side or the top, which belongs to a core
square. An interior point of S cannot belong even to a core square's
boundary, because a neighborhood would meet the core interior. This is
a contradiction. Hence S's interior is disjoint from G. Openness also
excludes an interior point on the slot's bottom edge, since a neighborhood
would enter G. Every other point of J outside G belongs to the actual core.
Thus S's interior is disjoint from the whole virtual rectangle J.

## 4. The existing corner and cap argument now applies

Apply Section 4 of
[EXTREME_ASYMMETRIC_TWO_ROW.md](EXTREME_ASYMMETRIC_TWO_ROW.md) to S and
J. That argument needs their interior disjointness, (1), `t>1/4`, the
upper-center constraints, and the same radius and height bounds. All
hold here; the original stronger threshold `t>t_0` served only to imply
`t>1/4` and `z<H`, which now follow from `t>1/3`.

The corner lemma puts every large-gap square wholly in `x>1/2` or
`y<-1/2`. The latter cap meets its available angular interval only in
`[-gamma_a,-pi/8]`, of length at most `gamma_0-pi/8<pi/8`, so cannot
contain an arc of angle at least `pi/4`. Thus all three necessary
large-gap squares would belong to the right cap `x>=1/2`.

The sharp three-square cap theorem forces the axis-parallel square
centered at `(1,1)`. It overlaps the upper-right core square at `(b,1-t)`,
because `1-b<1` and `t<1`. At most two such large-gap squares can fit.
This contradicts the count in Section 3, and completes the theorem.
