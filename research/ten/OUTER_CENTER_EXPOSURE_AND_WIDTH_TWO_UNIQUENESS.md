# Outward radial exposure permits at most one width-two endpoint pair

**Status:** hand theorem; root and independent full mathematical reviews
passed on 2026-10-30, including simultaneous radial exposures and every
actual/effective path-sharing case. No finite catalog count is changed
by this manuscript alone.

Work in `79/40<=R<=3/sqrt(2)` with interior-disjoint unit squares in the
centered radius-R disk. For the graph consequences, use the jointly
selected planar physical stress of
[PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md),
and classify its positive graph only after that selection.

**Theorem.**

1. If a square center c has norm at least one, its outward radial ray
   from c is disjoint from every other square, including their boundaries.
2. All such positive-graph vertices can be exposed simultaneously to the
   exterior in their center-ray circular order, whether loaded or unloaded.
3. There is at most one distinct unordered retained endpoint pair among
   all actual SS paths and all effective width-two connections supplied
   by unloaded retained vertices with two distinct neighbors. Parallel
   SS paths with the same endpoints count as one pair.

The last statement holds across the whole selected graph, and therefore
in each C05 skeleton, with arbitrary allowed k,b. It strengthens the
matching property of
[TWO_NEIGHBOR_UNLOADED_BRANCH_RESTRICTIONS.md](TWO_NEIGHBOR_UNLOADED_BRANCH_RESTRICTIONS.md).
An effective connection remains bookkeeping for its physical bodies;
no fictitious stress edge is introduced.

## 1. An outer center has a completely free outward ray

Write `c=a e`, where `a>=1` and e is a unit vector. Suppose
`p=c+s e`, with s>0, belongs to a different square of center b. Distinct
unit-square centers are separated by at least one, and every point of
a unit square is at distance at most `1/sqrt(2)` from its center. Thus

```text
|b-c|^2>=1,       |b-p|^2<=1/2.
```

Expanding the second expression and subtracting gives

```text
2s*(b-c) dot e >= s^2+1/2,
(b-c) dot e >= s/2+1/(4s) >= 1/sqrt(2),
b dot e >= 1+1/sqrt(2) > 25/16.                      (1)
```

The middle inequality is the elementary arithmetic-geometric mean
inequality, or the square `(s-1/sqrt(2))^2>=0` divided by 2s.
The last strict comparison follows, for example, from
`1/sqrt(2)>9/16`, whose squared comparison is `128>81`.
But every square center has norm below `25/16`, by the universal center
bound in [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md),
Section 3. This contradicts `b dot e<=|b|` and proves the ray assertion.

## 2. The planar embedding can preserve all these exposure rays

The contact-incidence construction for the selected planar graph joins
each square center to its physical contact points inside that square.
No contact point lies on the outward ray of an outer center, by Section 1.
The ray's portion inside its own square therefore meets its incidence
segments only at the center; different segments from one center could
share a further point only if they were collinear along this same ray.
Its remaining portion meets no square and hence no incidence segment.

The local contact-routing disks and track neighborhoods may be chosen
to avoid these rays. There are only finitely many contact points and
segments, and every relevant disjoint compact pair has positive
separation away from its own center. At that center the tracks fan out
while leaving the ray as an exterior access path, just as for the
loaded exposure paths in the planar selection theorem.

Distinct outer-center rays have distinct directions. If two centers had
the same radial direction, their distance would be less than
`25/16-1<1`, contradicting center separation. Their outward rays are
therefore mutually disjoint. Extend them to one common circle outside
the entire graph drawing. They meet that circle in their exact
center-ray circular order. This produces simultaneous noncrossing
access paths from all these vertices to the exterior. Equivalently,
the drawing may be regarded as a disk drawing with these vertices on
its boundary in that prescribed order.

In particular two vertex-disjoint graph paths with four distinct
alternating outer-center endpoints are impossible. Adjoin the four
exposure paths and truncate them at the common circle: one of the two
paths, completed along a circle arc, separates the two boundary
endpoints of the other, contradicting their disjointness.

## 3. Two different width-two pairs must alternate in radial order

An actual SS path separates its retained endpoint squares by a parallel
support strip of width two. The local effective connection through a
two-neighbor unloaded retained vertex supplies the same width, by
Section 1 of
[TWO_NEIGHBOR_UNLOADED_BRANCH_RESTRICTIONS.md](TWO_NEIGHBOR_UNLOADED_BRANCH_RESTRICTIONS.md).
That manuscript's Section 6 proves, without any loading assumption:

* each endpoint center has norm greater than `23/16`;
* any two distinct endpoint center rays are more than 36 degrees apart;
* each width-two pair has both circular arcs greater than 162 degrees;
* the distinct width-two endpoint pairs form a matching.

Suppose two different pairs exist. Name them {A,B} and {C,D}; their
four endpoints are distinct by the matching property. If the pairs
did not alternate around the origin, each pair would consist of two
adjacent members of this four-element circular order. Two different
successive gaps would then be greater than 162 degrees, and the other
two gaps greater than 36 degrees. Their sum would exceed
`162+162+36+36=396` degrees, instead of 360 degrees. Thus the pairs
alternate. All four centers have norm above one, so Section 2 applies.

## 4. Their actual physical paths are vertex-disjoint

For an actual SS relation choose one of its two-S paths. For an
effective relation through an exceptional vertex H, use its direct edge
and one of the two single-S paths in its double-S bundle. This gives
a positive-graph path between its two retained neighbors, with internal
bodies H and that chosen S transmitter. The selected path's order may
be A,H,S,B or A,S,H,B, depending on which endpoint is direct.

All these choices are actual positive graph paths. Their possible
shared-body cases are exhausted as follows.

* Their endpoint sets are disjoint by Section 3. A suppressed internal
  S body cannot equal any retained endpoint.
* Internal bodies on distinct maximal suppressed paths are disjoint.
  Two chosen single-S paths at different exceptional vertices could
  be the same maximal path only if those exceptional vertices were
  adjacent. That is excluded by Section 3 of the two-neighbor theorem.
  A single-S path and an SS path cannot be the same maximal path.
* The exceptional retained vertex H of an effective relation cannot
  be an endpoint of an actual SS relation: its only incident symbols
  are direct and double-S. It cannot be an endpoint of a different
  effective relation, since that would again make two exceptional
  vertices adjacent. It cannot be a suppressed internal body, since
  it is retained.

Two effective relations with the same endpoint pair were already
excluded by Section 4 of the two-neighbor theorem. An actual SS
relation cannot coexist with an effective relation on that same pair,
by Section 2 of that theorem. Repeated actual SS paths on a single
pair do not concern the assertion here.

Consequently the two different pairs supply vertex-disjoint paths.
Section 3 makes their four outer-center endpoints alternate, contrary
to the disk embedding of Section 2. This contradiction proves that
there is at most one distinct width-two endpoint pair.

The argument does not use the exceptional-vertex body budget or assume
any endpoint is loaded. In particular it supplies another proof that
there is at most one exceptional unloaded two-neighbor vertex, and
also says that, if one exists, there is no actual SS path anywhere in
the selected graph. If an actual SS pair exists, every other actual
SS path has that same endpoint pair.
