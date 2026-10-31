# Root review: arbitrary retained hub spokes and three complete five-load families

Date: October 26, 2026.

Reviewed the complete sources GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md
and CHORDED_HEXAGON_THREE_FIVE_LOAD_FAMILIES_CLOSED.md, including every
endpoint-owner case, the actual pocket routing and the three original
load-domain joins. Direct inputs inspected: the complete corresponding
sections of CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md;
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1;
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1;
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section 1;
FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md, Sections 1--3;
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md; and the original hexagon
graph/load table and fine labels.

## 1. Full force system and the new scope

The final standalone statement has 3<=k<=6. At that scope any extra
nonconsecutive boundary contact would create a physical boundary cycle
of length at most six, excluded by the original angular-order theorem.
Its separate seven-cycle exception is therefore not silently discarded.
All three original new callers have k=5 and are unchanged by this
explicit scope clarification.

The new hub theorem expressly requires the entire positive component
to be one unloaded hub with a loaded boundary path and an arbitrary
subset of internal hub spokes. Both path endpoints have true positive
degree two. Internal loaded bodies retain their genuine extra spoke
forces. The zero hub force and torque, and the zero total circle
resultant, follow from the full original equations.

The boundary-edge moment lemma is genuinely degree-free. Its proof
uses physical circle corners, a separating normal and the unit-width
support bounds, not a degree-two internal-body equation. The two
endpoint torque equations therefore supply opposite strict signs at
the first and last hub ports even when the next boundary body has no
hub spoke. The proper endpoint concurrence theorem retains physical
two-corner masks and individual zero weights and does not assert that
the concurrence lies inside the endpoint square.

The normal-order premise is preserved under omission of internal
spokes: the remaining normals are a subsequence in the same physical
port order. At coincident applications their original tangent-sector
order is retained. The proof does not manufacture a new normal.

## 2. Every endpoint-owner branch

Both H-axis endpoints: the identical-axis full-turn case has the
incompatible port order b<=a and strict moment signs a<0<b. The
adjacent-axis short interval has nonnegative force components and is
impossible. The long interval has strict northwest port projections
greater than r/sqrt(2)>1/4. For opposite axes the possible outer arc is
the left arc; if its vertical side came within 1/4 of O while crossing
the horizontal axis, both actual endpoint radii would force vertical
distances greater than 1/2, incompatible with their unit separation.
The comparison (2-sqrt(2))^2-1/16>1/4 follows from sqrt(2)<91/64.

One H axis and one oblique endpoint: the two short normal intervals
contradict the full hub force equation. The remaining long interval
has strict negative x coordinates at both endpoint concurrences and
the whole outer H arc. The horizontal portion is no nearer O than
the true endpoint; the possible vertical portion is covered by the
same two-port radius calculation. Both top-left and bottom-left cases
and every side mean are included.

Adjacent oblique vertices: the actual endpoint moments force h>0.
If the horizontal center coordinate has magnitude at least one, the
opposite endpoint projection exceeds 3/2, contradicting its actual
contained-neighbor bound p.n<=R-1. Thus one endpoint has horizontal
coordinate of magnitude at most 1/2. Its boundary radius gives
h^2>=r^2-1/4>9/100, using sqrt(2)<283/200. The entire outer side is
above 3/10, and both proper endpoint resultants point upwards.

Opposite oblique vertices: grouping all original forces at a coincident
endpoint is legitimate. The complete torques about the two endpoints
give nonnegative y components of the endpoint groups. Monotonicity of
the actual normal order within each vertex cone gives the same weak
sign for the genuine first and last normals. Their strict endpoint
moments and the retained projection bound p.n<=R-1 force the center
between the endpoints horizontally, and then h>0. Each outer side has
positive support at least r/sqrt(2)>1/4. Zero y components, coincident
applications, side endpoints and arbitrary internal spoke subsets are
covered without a fan-only bound on the hub center.

These are the full normal types for a square. No subinterval in an
angle or force magnitude has been omitted.

## 3. Physical pocket, winding, and strictness

The crosscut is made of actual occupied pieces and the gap-facing
contact extremes, leaving the true application means in the equations.
Its endpoint-body pieces miss D_(1/4) by the physical diameter bound.
The actual H arc has the proved strict margin. The independent
homotopy is used only to compute winding at O and lies in the endpoint
resultant half-planes; it need not avoid D_(1/4). The balance of at
least three distinct loaded resultants makes the actual closing gap
strictly shorter than pi. The final auxiliary loop is in one strict
half-plane, so winding at O is zero. Constancy on the connected closed
quarter disk, followed by the compact boundary margin, proves that
every whole square in the actual pocket is at distance GREATER than
1/4. The proof does not infer this from auxiliary concurrence geometry.

## 4. Complete original three-family assembly

For D03.L01245 the actual hub is3 and the path is2,1,0,5,4;
for D0203.L12345 and D0204.L12345 the hub is0 and the path is1,2,3,4,5.
The listed spokes, true endpoint degrees and internal degrees match
the exact original graphs. Their bounded faces are triangles or
four-rings containing three physical boundary units, hence all have
unit capacity zero. The full physical routing accounts for every
extra: direct boundary-pair pockets are empty, and all three extras
must be in the one closing pocket through H. Together with the five
physical boundary units this produces eight actual disjoint open
radius-5/4 sections, each longer than pi/4, a contradiction.

The source explicitly keeps NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md
as the inherited certified lower-radius input. It introduces no new
scalar certificate and does not claim the old one is retired.

Accept both complete mathematical sources and exactly the three fine
load gates named above, subject to the separate independent review.
No graph parent or coarse cell closes: in particular D02.L01345,
the multi-hub triangulations and every other load of these three
graphs retain their full obligations. All nine original squares,
physical circle masks, zero individual weights, unchanged means and
true positive degrees remain. No Lean compilation or CI was used;
the older full prerequisite audit and unrestricted theorem remain open.
