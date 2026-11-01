# Independent hand review: two-loaded components and the six-body unloaded-module bound

Date: October 31, 2026. Reviewer: articulation continuation.

**Decision: PASS R.1--R.5 at their original stated hypotheses, and PASS
the full-cut application below.** The component-cardinality result alone
proves that every nonempty connected entirely unloaded region with a
nonempty full positive cut has at most six actual bodies in the original
nine-unit radius window. Neither P.ALL nor a physical completion theorem
for a six-body core is used in this application.

## 1. Exact source and reading boundary

I read the complete current source `TWO_LOAD_RECIPROCAL_RIGIDITY.md`
from the fixed head `cb411042ad89d55d2f4c8d6e24682cec34677c89`.
Its exact identities are

- Git blob: `f10efa51418a4e1b68e6d31aa13f212d100d7d59`.
- SHA-256: `2b52f732faeb0f3484c3e322d7371626082f7be7be640495f5d9a8733198ee1f`.

The mathematical target here is Sections 1--7 through the at-most-six
statement of R.5. The later P.ALL and five-/six-body completion updates
are separate downstream results and are not premises of this review's
conclusion. The source's displayed polygon argument is reconstructed
below; no external background article is used as a proof substitute.

The original certificate has one selected normal per positive body pair
after its already authorized physical aggregation. All original shared
means and physical circle corners remain. For the layer-cardinality
step only, the original selected common normal strictly exposes both
vertices at a point-only vertex/vertex contact. This is an actual
premise, not a later normal adjustment.

## 2. Full reciprocal argument, including the global cancellation

For a balanced connected plane graph, attach dual displacement Jf to
the crossing from the right face to the left face of each oriented
primal edge carrying f. A closed dual curve sums the divergences of
the enclosed primal vertices, hence has increment zero. Decomposing
closed walks, including repeated edges, proves a well-defined face
potential. An alleged primal bridge would itself carry zero force by
summing divergences on one side, and so causes no hidden integration
obstruction when all retained edges are nonzero.

At a primal vertex the successive potentials form a closed polygon
whose edge vectors are Jf in the same cyclic order. If the force
directions are nondecreasing through one counterclockwise turn, this
polygon is weakly convex. For any chosen oriented side, the successive
transverse increments first have nonnegative and then nonpositive
sign, ending at zero; all partial sums consequently stay on its left
closed half-plane. Its signed area is nonnegative and is strictly
positive if the incident vectors are not collinear.

In the sum of all polygon shoelace areas, the potential segment for
each primal edge occurs once in each orientation at its two ends.
It cancels even when a face occurs repeatedly in a polygon walk.
Thus the total signed area is zero. A distinguished balanced degree-two
vertex has polygon area zero. All other vertex areas are nonnegative,
so every one is zero and all incident forces at each vertex are
collinear. Connectedness propagates that line globally. This verifies
the full force-polygon lemma, not merely a local force triangle.

## 3. The actual square incidence graph satisfies every hypothesis

For each actual contact application p, aggregate only the original
forces on one body S at that same p. Their positive normal-cone sum
F(S,p) is nonzero: its scalar product with p-c_S is a positive sum
of square support halfwidths. Join c_S to p inside the actual square.
Different actual interiors are disjoint, and the spokes inside one
square meet only at their common center after equal p's are combined.
The resulting incidence graph is plane; no body-graph planarity or
torque-destroying uncrossing is assumed.

Around an unloaded body, actual boundary order and convexity order its
normal cones counterclockwise. At a junction, -F(S,p) belongs to the
actual inward tangent cone of S. For a square vertex this is precisely
the negative of its right-angle outward normal cone. At a side
interior the inward normal is in the corresponding inward half-plane.
The actual incident center spokes lie in the same respective cones.
Disjoint tangent-cone interiors therefore give the required force order
at the junction too, with boundary ties permitted. The right-angle
fact is essential; no assertion about arbitrary acute polygons is used.

For a loaded square, the farthest-corner formula gives one physical
circle corner or two adjacent ones at R^2>9/4. Their positive radial
resultant is nonzero. A single circle corner has an exterior route.
Another unit cannot share it: two square tangent quadrants inside a
circle's inward half-plane would force an edge tangent to the circle,
whose positive-length continuation lies outside the strictly convex
disk.

For two adjacent circle corners, their outer chord has an empty
exterior cap. A second unit with interior on both sides of the chord
would cross its relative interior and enter the first square. A unit
wholly in the cap would have directional width less than one. The
circle endpoints are already unavailable. Hence that cap gives an
empty exterior route, and there is no intervening contact along the
outer side. The two consecutive circle directions can be replaced
topologically by their positive resultant without disrupting body
cyclic order. Individual zero coefficients and the other physical
corner remain part of the actual packing.

With exactly two loaded bodies, connect those two exterior ports to
one exterior vertex. Component force balance makes its two vectors
opposite. Both exterior routes can be drawn without crossing the
incidence graph. The polygon lemma now makes all aggregated incidence
forces parallel.

Finally the aggregation has not hidden nonparallel pair forces. If two
active bodies at one junction have aggregates of the same sign, their
common inward ray is a boundary ray of both disjoint tangent quadrants.
Each aggregate is then on an extreme ray of its normal cone, forcing
every positive constituent onto that same ray. At a junction with at
least three active bodies one sign group has at least two members;
this argument handles that group and all incident original pairs, and
then the other group as well. With only two active bodies there is
just their selected body-pair force, possibly combined along the same
normal. Thus every original positive pair force, not just each
aggregate, lies on the one common line. This proves R.1.

## 4. Loaded endpoint classification and radius quantization

Orient that common line by e and every positive pair from lower to
upper e support. Center projections strictly increase along each edge,
so the directed graph is acyclic. At an unloaded body both incoming
and outgoing totals are positive and equal. With exactly two loaded
bodies, one is the unique source and the other the unique sink;
every body lies on a directed path between them. Each endpoint's
entire original pair star is consequently on its inward support face.

The endpoint lemma is used at this full parallel-star scope, with the
positive weighted mean of its actual applications. Torque makes that
mean radial. One can directly verify its S/D classification: with one
circle direction the far vertex and radial opposing support must be
opposite vertices, forcing the square diagonal. With two adjacent
physical circle corners, a nonzero transverse resultant would put the
opposite support on the contrary transverse side, inconsistent with
radial torque and the positive longitudinal coordinate. Thus the
resultant is along their common own-side axis and the endpoint is S.
This includes a proposed individual zero circle coefficient before
the equations exclude any incompatible split.

The inward support-plane distance between the two actual radial
endpoints is therefore one of

\[
 2A_0,\quad A_0+B_0,\quad 2B_0,
 \qquad A_0=\sqrt{R^2-1/4}-1,\quad B_0=R-\sqrt2.
\]

At every internal body, grouping its whole parallel star by its two
opposite support faces and using torque gives width exactly one or
sqrt(2), just as for a genuine two-force channel. This grouping does
not impose original degree two. Along any directed path these actual
widths add to the endpoint support gap.

All centers have norm below 61/40 in the window. The two endpoint
halfwidths add at least one to the internal width sum when measuring
their center-projection separation. Consequently three internal
bodies are impossible; two internal bodies cannot include a diagonal
width. The only possible gap sums are 0, 1, sqrt(2), 2.

Throughout the entire closed window, the source's strict bounds give

\[
 1<2B_0<\sqrt2,
 \qquad \sqrt2<A_0+B_0<2,
 \qquad \sqrt2<2A_0<51/25.
\]

For example 9/10<A_0<51/50 and 11/20<B_0<7/10 supply the
middle and outer comparisons directly. All three possible endpoint
gaps are positive. The only matching discrete sum is 2A_0=2.
Thus R^2=17/4, both terminals are opposite S squares centered at
(-3/2,0),(3/2,0), and every directed path has exactly two side-type
internal bodies. Every internal unit is axis-aligned and belongs to
one of the two actual layers x=-1/2 or x=1/2. This proves R.3 with
all full degrees retained.

## 5. Exactly where strict singleton normals enter the body count

Each layer unit has a positive horizontal contact with its corresponding
loaded endpoint, so its center height satisfies |y|<=1. Equality would
make that contact a point-only aligned vertex/vertex contact. Its
horizontal original normal would not strictly expose the vertex in
either body, contrary to the stated selected-certificate premise.
Hence every layer height lies in the open interval (-1,1).

Two distinct axis-aligned units in one layer must have center heights
separated by at least one. Three such heights would have total span
at least two and cannot belong to that open interval. Each layer
therefore has at most two bodies. Adding the two loaded endpoints
gives at most six actual component bodies, proving the cardinality
part of R.5. Shared contacts with an endpoint mean are not confused
with point-only contacts: only the physical |y|=1 geometry is removed.
No false |y|<=1/2 bound is assigned to individual channel means.

## 6. New literal application to every full-cut unloaded module

**Theorem.** In the same original nine-unit packing and certificate,
every nonempty connected set K of entirely unloaded bodies with a
nonempty full original positive cut has |K|<=6.

Suppose |K|>=7, and let G be its complete connected positive component.
There are at most two actual units outside K in the whole packing, so
G has at most two loaded bodies. It has a positive edge because the
full cut is nonempty.

G cannot have zero loaded bodies: summing its full translations dotted
with its actual body centers cancels internal forces into a strictly
nonzero sum of positive contact magnitudes times positive support
widths. It cannot have exactly one loaded body: summing all translations
would make that body's circle resultant zero, but one circle corner
or two adjacent farthest corners with positive coefficients have a
nonzero resultant. The radius window has R^2>9/4, so all hypotheses
used for this circle-mask fact hold.

Thus G has exactly two loaded bodies. R.5 gives |G|<=6, whereas
K is a subset of G with |K|>=7. This contradiction proves the theorem.
It applies in particular to the three-port modules, without assuming
distinct external terminal identities. The bound concerns actual
bodies, including every genuine transmitter and every member outside
a reduced hub graph.

The argument uses no P.ALL exit, no five-body slider reduction, no
six-body completion theorem and no assumption that a merely physically
boundary unit is positively loaded. It is valid for arbitrary original
degrees and internal cycles at exactly the stated full-cut and selected
circle-load scope.

## 7. Verification boundary

The proof bodies and all new joins above were checked by hand. The
only file operations identify the exact current source bytes. No
external mathematical script, finite-force checker, pose sample,
graph enumeration, Lean, build or CI is used. No frozen source or
ledger is changed. The remaining global original-certificate audit
and unrelated parent/equality obligations retain their original scope.
