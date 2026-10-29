# Draft finite skeleton for mixed branching positive components

**Status: independently reviewed necessary skeleton reductions.** The
suppression, degree, bundle, and effective-contact arguments in Sections 1–4
received an independent mathematical audit on 2026-10-29. They give a finite
overclassification of C05; they do not exclude C05 or change its roadmap
status. No Lean verification is claimed.

Work with the selected physical positive-stress certificate of a hypothetical
strictly subcritical ten-square packing in `79/40<=R<3/sqrt(2)`. A loaded
body has positive circle load. The component under consideration is mixed,
contains a cycle, and is not itself a simple cycle. No planarity of its
body-pair graph is assumed.

## 1. Suppress only unloaded vertices of degree two

Retain every loaded vertex and every unloaded vertex of degree at least
three. Suppress each maximal path whose internal vertices are unloaded
and have degree two. The retained vertices and the resulting multiedges
form the proposed skeleton K.

The reviewed inputs in [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md)
give the following necessary properties.

* A nonempty unloaded set cannot have zero or one outside body-neighbor.
  Thus there are no unloaded leaves, and no suppressed path can form a loop
  at one retained vertex. Such a loop's internal bodies would have only
  that vertex as an outside neighbor.
* A nonempty suppressed path has width `1`, `sqrt(2)`, or `2`. Its type is
  respectively S, D, or SS, and its internal-body cost is respectively
  one, one, or two. An unsuppressed direct edge has type 0 and cost zero.
* Two paths between the same retained endpoints realize the distance
  between those endpoint squares. They have the same width and the same
  directed closest-displacement vector. A direct edge cannot coexist with
  a nonempty path between those endpoints.

Every component of K with one retained vertex deleted must contain a
loaded vertex. Every bridge cut has a loaded vertex on both sides. These
are necessary cut tests, not a claim that those tests suffice for a stress.

Write k for the loaded retained count and b for the unloaded retained
count. Then `k+b+sum(edge internal-body costs)<=10`, where parallel edges
are counted separately. Every unloaded retained vertex has multigraph
degree at least three. K is connected, contains a cycle, and has a vertex
of multigraph degree at least three. Subdivision preserves these graph
properties.

Here `2<=k<=7`. The upper bound is the previously reviewed strict-radius
loaded-count bound used in [CASE_ROADMAP.md](CASE_ROADMAP.md). For the lower
bound, summing body forces makes the sum of positive circle-load vectors
zero. Zero loaded bodies are excluded by the positive contact virial sum.
The circle vertices of a single square lie in one open hemisphere: if c
is its center and w a circle vertex, then
`c dot w=(R^2+|c|^2-1/2)/2>0`. Thus one loaded body is impossible too.
In particular the still-open branching family includes k=2; the reviewed
two-terminal theorem must not be applied to arbitrary branching graphs.

## 2. Universal body degree bound: eight

Fix a body center c. Every touching body's
center differs from c by a vector of length in `[1,sqrt(2)]`: the lower
bound follows from disjoint open inscribed half-unit disks, and the upper
bound from a shared point and the two circumradii.

If there were nine neighbors, two successive difference vectors would
have angular gap at most `2pi/9`. Set `C=cos(2pi/9)`. Then `C>3/4`:
`C>1/2`, the polynomial `4x^3-3x+1/2` increases for `x>1/2`, its value
at C is zero by the triple-angle identity, and its value at `3/4` is
`-1/16`.

The squared distance between the two neighbor centers is
`a^2+b^2-2ab cos(delta)`, with `1<=a,b<=sqrt(2)` and
`cos(delta)>=C>3/4`. Separate convexity in a and b bounds it by the four
corner values of this rectangle. Those values are strictly below
`1/2`, `1`, or `3-(3/2)sqrt(2)<1`. This contradicts center separation.
Hence every original positive body degree, and every retained multigraph
degree, is at most eight.

## 3. Parallel-bundle bounds

For a D bundle, all its single diagonal
transmitters have the same orientation. The contacts on either endpoint
support face vary only in the transverse direction and by at most one,
since a square's support face is a vertex or a unit side. Thus their
centers differ transversely by at most one. Two such identically oriented
diagonal squares with the same longitudinal center coordinate need
transverse separation at least `sqrt(2)` to have disjoint interiors.
Consequently a D bundle has multiplicity at most one.

For S and SS, use the **selected-certificate** strict-normal convention
recorded in Section 1 of
[COMMON_CORNER_MIXED_TRANSMISSIONS.md](COMMON_CORNER_MIXED_TRANSMISSIONS.md).
At point-only vertex/vertex contact, a selected positive normal is strictly
inside both normal cones; in particular it cannot be a side normal of
either square. This convention is not being asserted for arbitrary
physical stresses.

Look at the first S body in each path from one fixed endpoint H. These
first bodies have the same longitudinal unit interval. Their transverse
unit intervals have disjoint interiors. Each meets H's support face,
which is either a single point or a unit interval.

If that support face is a point, two of the transverse intervals could
contain it only by both ending there. Their contacts with H would then be
point-only vertex/vertex contacts carrying a side normal, forbidden by the
selected convention. Thus there is at most one path in this case.

If H's support face is a unit interval J, each transverse unit interval
must overlap J in positive length. A singleton intersection would again
be a forbidden vertex/vertex side-normal contact. Three unit intervals
with disjoint interiors cannot each overlap a unit interval in positive
length: a point in the first overlap and a point in the third overlap
would be more than one apart. Thus the multiplicity is at most two.
The same argument applies at the other endpoint and to the first column
of an SS bundle. A double S or double SS bundle therefore has side support
at both endpoints, fixing their frames parallel to the transmitters.

Combining these bounds with Section 1 gives the finite per-pair
alphabet

```text
absent, direct, S, double-S, D, SS, double-SS.
```

Their body costs are `0,0,1,2,1,2,4`, respectively. A double-S edge means
two parallel one-body paths; SS means one two-body path. Those must not be
confused. This is an overclassification, with continuous geometric and
force parameters still attached to every retained record.

## 4. An unloaded branch with two distinct retained neighbors

Suppose an unloaded retained vertex H has exactly two distinct skeleton
neighbors, even though its multigraph degree is at least three. Aggregate
the parallel-path forces separately for those two neighbors. Their
effective application points remain on H's corresponding support faces.
Force and torque balance make H an effective S or D transmitter between
the two neighbor groups.

If both incident bundles were nonempty transmission bundles, the total
width across H would be at least three, contradicting the endpoint-center
projection bound `1+W<25/8`. Hence one bundle is direct. The other must
have multiplicity at least two, so the proposed bounds in Section 3 leave
a double S or double SS bundle. Double SS would again give width at least
three. A D frame for H together with double S would give width
`1+sqrt(2)>17/8`. The only remaining pattern is therefore one
direct edge and one double-S bundle, with H itself an effective S body.

Here is the effective-point justification for that projection argument.
For a bundle of paths between H and J, give each path its common positive
force magnitude as weight. Its two endpoint application points differ by
`W d`, with the same W and d for the entire bundle. Taking the same
weighted averages on H and J preserves that identity and keeps both
averages on the corresponding convex support faces. For a direct edge,
use its original application point and W=0.

On H the two aggregate forces are opposite and equal, and their total
torque vanishes. Thus their two effective points differ by `w_H d`, where
`w_H` is 1 or sqrt(2), by the usual two-force square argument. The two
outer effective points consequently differ by
`(W_1+w_H+W_2)d`. The outer endpoint squares lie on opposite sides of the
support lines through those points. Their center projections differ by
at least `1+W_1+w_H+W_2`. Both centers have norm below `25/16`, so this
quantity is strictly less than `25/8`, exactly the bound used above.
The effective points are used only to deduce this necessary geometry;
no replacement physical stress or movement of a body is asserted.

## 5. Next work and exact stopping boundary

No enumeration was run. A first manageable subclass would set b=0, so all
branch vertices are loaded and every unloaded body lies on a suppressed
path. For k>=4, direct loaded edges join radial neighbors. Vertex-disjoint
transmission paths with alternating loaded endpoints must both be D, by
[SINGLE_SIDE_TRANSMISSION_UNCROSSING.md](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md)
and its width-two dependency. These give further necessary rejection
tests for a future finite generator. The k=2, b=0 subclass is already
excluded by the reviewed two-terminal theorem.

Required next steps are an exact
canonical finite generator with body-budget and cut checks, and geometric
exclusions for the retained skeletons. There is presently no claimed
number of C05 cases and no claimed C05 closure.
