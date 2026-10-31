# Independent review: central and exterior extras of a selected cycle are disjoint

Date: October 30, 2026 UTC. Reviewer: root continuation.

**Decision: ACCEPT the complete uniform theorem at the frozen pin below.**
I read the whole source and its five complete direct source/review inputs,
checked their exact pins, and reconstructed the geometric, full-cut and
local-routing arguments. My earlier confirmation of the author's reported
outline was not an adoption gate; this is the subsequent full-source
review. The author had already supplied the general four-junction result
and its proof before that confirmation. I supplied no new argument or
repair in this manuscript.

Reviewed source:

`SIMPLE_POSITIVE_CYCLES_SEPARATE_ALL_CENTRAL_AND_EXTERIOR_COMPLETION_SQUARES_2026_10_30.md`

SHA-256:

`0bd4cc0dcf3653652e31c88190b5455549846cf1a4a9c2f74e0331e31caa6eca`.

## 1. Exact selected-cycle and physical-region scope

The entire positive component must be a simple cycle. Thus each of its
vertices has exactly two original positive pair forces. Additional
physical contacts and every physical circle corner remain, including
zero coefficients; a merely graph-theoretic cycle inside a larger
positive component does not satisfy this premise.

The common selected-normal restrictions are precisely those of the
accepted full unloaded two-port theorem. They were imposed before
certificate extraction and survive physically compatible uncrossing and
thinning. The new result does not reselect a normal, add a positive
edge or assert planarity of the entire physical contact graph.

Central and exterior refer to the bounded and unbounded sides of the
actual bare cycle, respectively. The proof needs only these two winding
labels. It does not infer the position of an extra from a force polygon.
Every fixed compact path in an extra's open interior has positive
distance from the closed core union. Arbitrarily small local graph
routings leave its winding label unchanged. This stability also follows
directly for a bare cycle with any load count: two sufficiently small
routings differ only near the original occupied curve and cannot change
the winding at a fixed point outside that closed union. Thus the broad
R>sqrt(2) theorem does not import the narrower channel-cap bounds
outside their stated radius or three-load scope.

## 2. Complete four-square circle lemma

Four interior-disjoint unit squares at one point must each contribute
a right-angle tangent sector. The sectors fill a turn, making the exact
aligned 2 by 2 block. In its frame, with junction p=(u,v), the
largest squared norm on the block is

    (|u|+1)^2+(|v|+1)^2.

Strict convexity in each coordinate makes every maximizing point one of
the four outer block corners. A constituent touching the containing
circle must contain such a maximizing point, since the entire block is
contained in the disk. Each constituent contains exactly one outer
corner. If opposite constituents touch, their opposite outer corners
both maximize. Both coordinate signs must then maximize, so u=v=0.
The physical circle radius is sqrt(2).

This covers placements outside the block center, both zero-coordinate
ties and all rotations. It concerns physical circle contact, independent
of individual force weights. Therefore two opposite constituents cannot
both be boundary squares when R>sqrt(2).

## 3. The full two-port rule excludes a supported opposite pair

A supported opposite pair at a four-square junction is an actual
point-only vertex/vertex contact with a selected strict free normal.
If either endpoint were unloaded, its singleton subset would have
exactly two positive cut edges because the component is the entire
simple cycle. The complete two-port theorem forbids a free contact
in that cut. The other edge may be shared with any original mean;
the two-port theorem covers it without freezing that mean.

Hence both endpoints would have positive total circle load and thus
be actual physical boundary squares. The preceding four-square lemma
excludes them. The matched free parameters at a four-junction do not
create an exception: the accepted two-port theorem explicitly handles
that pairing, and the physically compatible selected graph retains
at most one supported opposite pair.

All this uses the full original degree two, not a two-force equation
assigned after omitting an outside force.

## 4. Complete contact and routing argument

Suppose two actual extras with opposite winding labels touch at p.
If p misses the closed core union, a small disk around p misses the
cycle, and short segments from the two extra interiors through p give
a path between them in the cycle complement. Their labels would agree.

The same reasoning applies if no original positive cycle application
occurs at p. A center-to-application segment has every other point in
its own open square, so it cannot pass through p belonging to an extra.
There are finitely many strands; a sufficiently small neighborhood of
p and routing avoid them. This includes a zero-stress core contact and
a positive shared interval whose actual mean is elsewhere. A physical
circle point cannot be shared with the extras, by the complete radial
interior-segment argument in the embedding input.

Therefore p is an original positive application of a core edge V-W.
The four distinct squares V,W,T,E meet there. The sector bound excludes
a fifth and forces the full aligned four-quadrant junction.

If V,W are adjacent quadrants, T,E are the other adjacent pair.
The core strand can be routed on the V/W side of the junction, while
the interiors of the two extras connect on the other side. No second
cycle strand can use p: only those four bodies meet there, the extras
are not cycle vertices, and the simple cycle has no second V-W edge.
Thus there is no hidden local obstruction to the connection.

This includes an original shared-side mean equal to the endpoint p.
Routing the mathematical graph strand close to the occupied common
side changes neither the force application nor any equation. At fixed
nearby extra interior points the labels are stable under that routing,
so the resulting connecting path contradicts their being different.

Only opposite V,W could separate the extra quadrants. Their contact
is the singleton p, making their positive cycle edge exactly the
supported opposite pair already excluded in Section 3. The proof
therefore covers all shared-mean endpoints and weak physical junctions.

## 5. Conclusion, callers and retained constraints

Every central/exterior pair of additional closed squares is disjoint.
Each pair is compact, so its minimum distance is strictly positive.
There are finitely many such pairs, giving a common positive clearance
when both classes occur. This removes only their mutual active-contact
constraints from a possible sufficiently small motion. It does not
establish any feasible motion against the remaining bodies or circle.

The stated C6 and all four/five/six-load short-C7 callers satisfy the
whole-component premise and retain every actual extra. The two-RR
caller's one-central/one-exterior labels come from its prior complete
pocket theorem. No such labels are assumed when a different caller
has no central extra. All same-region, extra/core, nonconsecutive-core,
circle and shared-interval constraints remain possible and untouched.

This is a uniform geometric restriction, not a completion-capacity
contradiction or a closure of an original coarse or fine parent.
The global bound, equality and existing transitive prerequisite audit
are not certified by this new review.

## 6. Complete direct input identities

| Complete input | SHA-256 |
| --- | --- |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md | f9a008a8cebb02825891d773afeafa0fa953f5c499988bdaae0bac947ff6f1e7 |
| GENERIC_TWO_AND_THREE_PORT_CUT_RULES_FOR_ARBITRARY_UNLOADED_BODY_MODULES_2026_10_30.md | f6b12507086fd284e99b637748ef3b40c994c56aba44264a2c3a408338181251 |
| REVIEW_GENERIC_TWO_THREE_PORT_UNLOADED_MODULE_CUTS_BRANCH_BUDGET_INDEPENDENT_2026_10_30.md | b8c0e97d822da38d43bf5577ec9a85bea75eec059751a1afcc020ecd6e4e4dcd |
| RADIAL_RADIAL_TRANSMITTERS_CAN_SLIDE_OUTWARD_AND_CANNOT_FORM_A_CLOSED_TWO_BODY_BLOCKER_NETWORK_2026_10_30.md | 0fbcce339700b2d2e23fa30a516a64c2773e868b90ed60f695fcc93ac4cafff7 |

All five pins match the complete read bytes. The new proof consumes only
the two-port part of the generic cut source; no new shared-mean
determinant or rational-stress inference is hidden in the join.

No numerical pose/angle search, mesh, optimizer, new packing certificate,
Lean/Lake invocation, CI, force or normal change, physical deletion,
shared-source modification, metadata edit or remote action was used.
