# At most three body vertices need lie inside the planar disk

**Status:** reviewed exact hand theorem, 2026-10-30; root and two independent
mathematical reviews passed. This is a universal geometric
and graph reduction, independent of the loaded count k and retained
unloaded count b. It does not introduce a new enumeration.

Let interior-disjoint unit squares lie in the centered disk of radius
`79/40<=R<=3/sqrt(2)`. For graph statements, use the jointly selected
planar physical stress before classifying its positive components.

**Theorem.** Every body whose center has norm at least `1/sqrt(2)` has
an outward radial ray disjoint from every other square. At most three
body centers have norm strictly less than `1/sqrt(2)`. Consequently the
whole selected positive graph has a planar disk drawing with at most
three body vertices in the interior; every other vertex is on the
boundary in its center-ray circular order.

This counts physical body vertices, including unloaded degree-two
transmitters. Suppressing such transmitters leaves at most three
interior retained vertices. All endpoints of D or SS skeleton paths
are among the exposed boundary vertices. Thus any retained vertex not
covered by the radial exposure conclusion has only direct or S-type
incident connections, including possible double-S bundles.

## 1. Sharpen the radial-exposure threshold

Write a body center as `c=a e`, where e is a unit vector and
`a>=1/sqrt(2)`. Suppose some point `p=c+s e`, s>0, of its outward ray
belongs to a different square centered at b. As in
[OUTER_CENTER_EXPOSURE_AND_WIDTH_TWO_UNIQUENESS.md](OUTER_CENTER_EXPOSURE_AND_WIDTH_TWO_UNIQUENESS.md),
center separation and the unit-square circumradius give

```text
|b-c|^2>=1,       |b-p|^2<=1/2,
b dot e >= a+s/2+1/(4s) >= a+1/sqrt(2).              (1)
```

Using center separation once more yields

```text
|b|^2 >= 1+2a*(b dot e)-a^2
       >= 1+a^2+sqrt(2)*a
       >= 5/2.                                      (2)
```

But the universal center bound gives
`|b|^2<(25/16)^2=625/256<640/256=5/2`.
This contradiction proves that the ray misses every other square,
including its boundary. The threshold equality `a=1/sqrt(2)` is included.

The simultaneous embedding construction in Section 2 of the linked
exposure theorem now applies unchanged: the contact-incidence segments
and their finite planar routing neighborhoods avoid these rays. Distinct
exposed centers cannot have the same direction, since their radial
distance difference would be less than
`25/16-1/sqrt(2)<1`. The inequality follows from
`1/sqrt(2)>9/16`. Their mutually disjoint rays therefore give exterior
access in exactly the center-ray circular order.

## 2. At most three centers can fall below that threshold

Suppose four distinct centers had norm strictly less than `1/sqrt(2)`.
If one were the origin, its distance from every other one would be
less than one, impossible. Otherwise four nonzero center rays have
two consecutive directions separated by an angle at most `pi/2`.
For their positive radii a,b, the squared center distance is at most

```text
a^2+b^2 < 1,
```

because the cosine term is nonnegative. This again contradicts center
separation. Thus there are at most three such bodies in the entire
packing, not just in any one positive component.

Expose all other positive-graph vertices by Section 1. The resulting
disk drawing has at most these three possible interior body vertices.
Suppression removes vertices and follows their paths; it cannot create
an additional interior retained vertex. This proves the graph bound.

## 3. Every D or SS endpoint is exposed

For a D path the endpoint-center projection difference in its common
normal direction is at least `1+sqrt(2)`. Since the other endpoint
center has norm below `25/16`, each endpoint center has norm greater than

```text
1+sqrt(2)-25/16 = sqrt(2)-9/16 > 1/sqrt(2).           (3)
```

The last comparison is equivalent to `1/sqrt(2)>9/16`.
For an SS path the corresponding lower bound is
`3-25/16=23/16`, which is still larger. Both conclusions depend only
on the support strip and containment; endpoint loads and degrees are
irrelevant.

All these endpoints are therefore boundary vertices in the same disk
drawing. In particular no two vertex-disjoint D/SS paths, or other
graph paths between four such exposed endpoints, may have alternating
endpoint order. The previously reviewed D-forest restriction and the
one-width-two-pair theorem remain available on this same certificate.

The remaining branching problem is consequently a single universal
family: planar disk graphs with at most three interior physical bodies,
all D/SS endpoints on the boundary, at most one width-two endpoint pair,
and the existing local force, torque, bundle, and body-budget conditions.
This is a necessary structural reduction; it does not assert that every
graph satisfying those conditions is realizable or already excluded.
