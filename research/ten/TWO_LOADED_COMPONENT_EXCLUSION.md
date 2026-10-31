# Every two-loaded positive component is impossible below the target radius

**Status:** complete hand theorem; root and two independent full
mathematical reviews passed on 2026-10-30, including all graph degrees,
endpoint load splits, cavity configurations, and capacity boundary cases.
No finite catalog count is changed by this manuscript alone.

Assume a hypothetical ten-square packing has squared radius below `9/2`,
take an unrestricted radius minimizer, and choose the jointly selected
planar physical stress. Work in the reviewed radius window

```text
79/40 <= R < 3/sqrt(2).
```

**Theorem.** No connected positive-contact component has exactly two
loaded bodies. This includes trees, simple cycles, and arbitrary
branching components with any number of unloaded retained vertices.

Use [TWO_LOADED_PARALLEL_FORCE_REDUCTION.md](TWO_LOADED_PARALLEL_FORCE_REDUCTION.md)
to conclude that all its contact forces are parallel to one unit vector
e. The circle-force resultants on its two loaded bodies are nonzero and
opposite. The physical force application points and all original torque
equations remain unchanged. The proof below does not replace the two
circle atoms of a radial-side body by a fictitious physical contact.

## 1. The positive force flow has one source and one sink

Orient each positive body-pair contact from its left body to its right
body in direction e. If the contact supports the squares i,j, then

```text
e dot (c_j-c_i)=h_i(e)+h_j(e)>=1,
```

where h denotes directional halfwidth. Thus the directed graph is
acyclic. Give each edge its positive force magnitude. On every unloaded
body, the total incoming and outgoing magnitudes agree.

Every source or sink of this finite directed graph must consequently be
loaded: a positive-degree unloaded source or sink cannot balance. A
connected component with edges has at least one source and at least one
sink, and no vertex can be both. With exactly two loaded bodies these
are therefore distinct bodies A and B, the unique source and sink.
Every vertex, and every edge, lies on a directed A-to-B path: extend a
path backward and forward until it reaches a source and a sink. In
particular A has only outgoing contacts and B only incoming contacts.

Aggregate each body's contact forces separately on its left and right
support faces. These weighted application points belong to those faces
and preserve torque. An unloaded body has equal positive totals on the
two faces. Torque balance makes the displacement between its two
aggregate points parallel to e.

If e is a side normal, that body is an effective S transmitter of
projection width one. Otherwise its two support faces are opposite
vertices. Their displacement can be parallel to e only when e is a
diagonal direction, giving effective width `sqrt(2)`. Thus every
unloaded body is S or D in the common direction, even if it has several
neighbors on either face. This assertion concerns aggregated forces;
an individual directed path is not assumed to keep one transverse
force line through a branching body.

## 2. The endpoints are radial S bodies and the common gap is two

At either endpoint all contact forces have one sign along e. Their
aggregate is one force at a point on one support face. Its torque about
the origin is zero because each original circle force is radial.
The loaded-leaf calculation in
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md), Section 3,
therefore applies to this aggregate, independent of the endpoint's
degree. The endpoint is a radial S or D body, with positive inward
contact radius

```text
a_S=T-1,       T=sqrt(R^2-1/4),
a_D=R-sqrt(2).
```

An S endpoint has two equally weighted adjacent circle vertices. A D
endpoint has its unique circle vertex in the radial direction. The
force sign places the source A on the negative ray and the sink B on
the positive ray. Their inward aggregate points are consequently
`-a_X e` and `a_Y e`, for endpoint types X,Y. Thus their inward support
lines have gap

```text
W=a_X+a_Y>0.                                         (1)
```

Along any directed A-to-B path, all contacts are on successive common
support lines. Projection onto e telescopes: W is the sum of the full
projection widths of its unloaded internal bodies. Their individual
contact points may have different transverse coordinates; this does not
affect the projection identity.

The endpoint-center projection difference is at least `1+W`, whereas
both endpoint centers have norm below `25/16`. Hence `W<17/8`.
Each internal width is one or `sqrt(2)`, so

```text
W in {1,sqrt(2),2}.                                  (2)
```

A direct path with no internal body would give W=0, already excluded.

Here the radius window eliminates all endpoint choices except S--S.
Indeed `T>19/10`, because
`R^2-1/4>=5841/1600>(19/10)^2`. Therefore

```text
2a_S>9/5>sqrt(2).
```

For S--D,

```text
T+R-1 > 23/8 > 2sqrt(2),
a_S+a_D > sqrt(2),
a_S+a_D < 17/16+3/4=29/16<2.
```

The comparison `23/8>2sqrt(2)` is `529>512` after squaring.
The upper bounds use `T<33/16` and `R-sqrt(2)<3/4`.
This lies strictly between two successive possibilities in (2).
For D--D, `R>sqrt(2)+1/2` since
`sqrt(2)<29/20` and `79/40>39/20`; strict subcriticality gives

```text
1<2a_D<sqrt(2),
```

again impossible by (2).

Both endpoints are therefore S. Equations (1)--(2) force

```text
W=2,       2(T-1)=2,       T=2,       R^2=17/4.
```

Rotate e to the horizontal direction. The two endpoint squares are

```text
A=[-2,-1] x J,       B=[1,2] x J,
J=[-1/2,1/2].                                       (3)
```

Their aggregate inward contact points are `(-1,0)` and `(1,0)`.

## 3. Every remaining body belongs to one of two parallel columns

Each directed A-to-B path has total internal width two. Its internal
bodies must therefore be exactly two S bodies; no D width can occur.
Since every body lies on such a path, all unloaded bodies are parallel
unit squares in the two columns

```text
left:  [-1,0] x I,
right: [0,1] x I',                                  (4)
```

where I,I' are unit vertical intervals. Every left-column body contacts
A, and every right-column body contacts B. Every column body also has
at least one positive contact to the other column.

Each vertical interval in (4) overlaps J in positive length. A singleton
intersection would be a point-only vertex/vertex contact carrying a
side normal, forbidden by the selected strict-normal convention.
Intervals within one column have disjoint interiors. Three disjoint
unit intervals cannot all overlap J positively, so each column has
either one or two bodies. Write m,n for these counts and `t=m+n`;
then `2<=t<=4` and the component has `2+t` bodies.

The convex hull of each column's vertical intervals contains zero:
the corresponding endpoint's weighted contact point has height zero
and is a positive average of points of those intervals. In particular,
if a column has just one body its interval contains zero.

## 4. All column gaps are sealed cavities of height less than one

Suppose a column has two intervals, ordered as

```text
[l,l+1], [u,u+1],       u>=l+1.
```

If u=l+1 there is no gap. Otherwise the positive overlaps with J give

```text
-1/2<l+1<u<1/2.                                     (5)
```

Its open gap rectangle therefore has height less than one and lies in
`|y|<1/2`. Its outer vertical side, at x=-1 or x=1, is blocked by A or B.
Its horizontal sides are blocked by its own two column squares.

At the interface x=0 there are two possibilities. If the other column
has just one body, both bodies of the split column must contact it,
since each lies on an A-to-B path. Their overlaps with that body's unit
interval are positive by the strict-normal convention. The entire
closed gap in (5) is consequently in the interior of that interval,
so the interface is blocked too.

If the other column also has two bodies, its combined vertical span
contains J. This follows directly from its two disjoint unit intervals
both overlapping J positively: its lowest endpoint is below -1/2 and
its highest is above 1/2. A gap can therefore open at x=0 only into the
other column's gap. If the two gap rectangles connect across x=0, treat
their union and that interface as one cavity. Otherwise each is a
separate cavity. Every such connected complementary region is sealed
by the component squares and lies in the strip `|y|<1/2`.

The interior of an additional square is connected and disjoint from
the closed core squares. If it entered one of these cavities, it would
be entirely in that complementary region. This is impossible: every
unit square has vertical projection width at least one, whereas the
cavity's vertical width is strictly less than one. Thus these gaps
may be filled as auxiliary obstacles. No square is physically inserted.

After filling, each column is one vertical rectangle whose interval
contains zero. At every interface the neighboring intervals intersect
at zero. The filled core consequently has a vertical interval containing
zero at every `-2<x<2`. At x=+-2 the containing open disk has `|y|<1/2`,
which is entirely blocked by its outer anchor in (3).
The barrier argument of
[STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md) now puts
every additional square wholly in the closed upper or lower half-plane,
unless it lies in one of the side caps. A side cap has horizontal width
`sqrt(17)/2-2<1` and cannot contain a unit square. Hence every additional
square belongs to an upper or a lower class.

## 5. The existing capacity theorems leave at most nine squares

The [wide-neck theorem](WIDE_NECK_THREE_POINT_STABBING.md) bounds each
half-plane class of unit squares avoiding A,B by three. Its reflected
version gives a combined capacity of six. The
[one-neck theorem](ONE_NECK_STABBING.md) improves one of these two
capacities to two whenever we retain a column square whose interval
contains zero, as follows.

Suppose first that some column body H has center height h with
`|h|<=1/2`. Reflect horizontally if needed to place it in the left
column. If h>=0, H contains `[-1,0] x [0,1/2]`; if h<=0 it contains
`[-1,0] x [-1/2,0]`. Thus every additional square in the corresponding
half-plane, as well as every other column square wholly in that
half-plane, avoids the fixed middle obstacle used in the one-neck
theorem. The combined capacity for these candidates, excluding H and
the two anchors, is at most `2+3=5`.

At most one interval in each column can straddle zero in its interior,
because intervals in a column have disjoint interiors. In H's column,
every other interval is wholly in a closed half-plane. In the other
column, at most one fails to be wholly in a half-plane. Therefore at
least `t-2` of the other `t-1` column bodies already occupy places in
this capacity-five bound. Every additional square occupies another
place, so there are at most `5-(t-2)=7-t` additional squares. The total
is at most

```text
2+t+(7-t)=9.                                        (6)
```

This also covers h=0 and |h|=1/2. A positive-area square cannot belong
to both closed half-plane classes, so no candidate is counted twice.

If no column interval contains zero, every one of the t column squares
is already wholly above or wholly below zero. They consume t of the
six places in the two wide-neck capacities. There are at most `6-t`
additional squares and at most `2+t+(6-t)=8` squares altogether.

Both alternatives contradict ten squares. This proves the theorem,
uniformly for all branching degrees and all allowed unloaded retained
counts. The other squares have arbitrary orientations throughout.

The conclusion is a reviewed selected-certificate structural exclusion
of every k=2 component. Existing finite k=2 records may therefore be
marked excluded without changing any raw catalog denominator.
