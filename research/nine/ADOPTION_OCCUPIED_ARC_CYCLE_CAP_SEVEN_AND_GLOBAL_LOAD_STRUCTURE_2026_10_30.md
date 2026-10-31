# Adoption: every compatible cycle has at most seven bodies, with global load structure

Date: October 30, 2026 UTC.

Input head: `e6eb16bf2bc05012e913407953107c87236ce0be`.

**Every compatible simple positive-cycle component has at most seven
actual square bodies. All eight- and nine-body simple components are
excluded simultaneously, across all load counts and internal orientations.**
The theorem also applies to a displayed cycle with arbitrary extra edges
at its physical boundary marks, provided each remaining vertex is genuinely
unloaded and has true positive degree two in the same complete graph.

The proof uses occupied arcs of actual boundary squares and the actual
set gaps forced by intervening units. It needs no torque, no force polygon,
no centered-arc approximation and no discrete orientation classification.
The complete geometric metric inequality is stated before its graph caller.

Separate global force theorems show that every genuine long channel has
positively circle-loaded endpoints, and every connected component of the
retained direct-contact subgraph contains a positive circle load. Together
with the preceding capacity checkpoint, all long channels in a nine-square
packing use one distinct endpoint pair, and both members of that pair are
positively loaded. Parallel channels on that same pair remain possible.

The unrestricted sharp lower bound, equality classification and common-
selection audit remain **OPEN**. Original identifiers, order and flags remain
**2373/2513 fine checked, 140 open; 36/58 coarse closed, 22 open**. No arbitrary
chorded parent is credited from a simple-cycle theorem.

## 1. One actual arc-and-gap inequality replaces the remaining C8 case split

Work in the inherited window

    79/40<=R<=sqrt(Q), Q=1105/256.

Every physical boundary square intersects the circle of radius rho=5/4
in one connected closed arc of angular length greater than pi/4. Its
relative interior is inside the actual open square. The complete old
occupied-arc proof is reconstructed in the new source, with its outward
own-axis convention stated correctly.

The radial direction of every actual containing-circle corner lies in
the relative interior of this arc: the point (rho/R)z is inside the
original square. The center direction lies there as well, because its
radial point is within 4/15<1/2 of the actual center. Trim slightly to
obtain a closed interior arc of length still greater than pi/4. These
actual occupied arcs are disjoint and have exactly the physical corner
and center order, including squares with two circle corners or zero
selected circle weights.

For any t>=2 selected boundary units in this actual circular order, let
D_i be the true set distance between consecutive units. The chord joining
the corresponding arc endpoints has length at least D_i. Its intervening
directed circular arc has length at least that chord, including a major
arc. Occupied arcs plus intervening arcs use one full circle, so

    sum_i D_i < (5*pi/16)(8-t).                         (A)

This is a force-free metric theorem. It does not require adjacency and
does not assume that other physical units avoid the intervening arcs.

For a compatible marked cycle, the exterior physical spokes prove that
cycle order is this actual corner order. A common-normal run with j_i
internal bodies has actual endpoint set gap at least

    W_i=sum_internal 2h_U(n)>=j_i.

Every unit's true support width is retained. Therefore (A) gives

    m-t=sum_i j_i <=sum_i W_i < (5*pi/16)(8-t).

The left side is nonnegative, forcing t<8; since
5*pi/16<55/56<1, it follows that m<8 and hence

    m<=7.                                             (B)

The same source retains the stronger continuous width budget, not just
its integer consequence. No separate upper bound on a run length is
needed for this proof.

The full-force caller requires the complete true-degree-two, zero-circle-
load equation at every unmarked internal body. Marked endpoint degrees
are unrestricted. An entire positive simple component has at least two
loaded bodies, as proved from its full force equations, and is a literal
caller. The theorem works with one compatible translational certificate;
it does not identify a separately selected torque certificate with it.

**Consequences:** all compatible simple C8 and C9 components are excluded;
all cycles of those sizes with additional edges only at physical boundary
marks are excluded. A surviving such cycle must have a physically circle-
clear vertex with an additional positive edge. Arbitrary chorded blocks,
interior graph vertices and repeated outer-face walks retain their own
obligations.

Complete source:
OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md.
The full source and its old arc input have complete root and independent
reviews. The seven-body record orbit (2,0,1,0) is preserved: its four marks
and total internal reserve three satisfy 3<5*pi/4.

## 2. Every long channel ends at positive circle loads

For every actual packing at q<=Q, any physical contact point has radius
strictly less than 29/15. The proof is independent of stress: at a point
of greater radius, every incident square center would have to lie within
45 degrees of the inward radial direction. Two such center displacements
would have positive dot product and would put the two centers at distance
less than one, contradicting their disjoint open incircles. The boundary
case retains an exact reserve 1/240.

For a gap-two endpoint pair, the support/height estimates force the entire
outward own side of each endpoint beyond radius 29/15. That whole side,
including its corners, is consequently free of every actual contact. All
contact normals have nonpositive projection along its outward own axis;
the inward long-channel force has strictly negative projection. A full
translational balance without a positive circle load is impossible.

Thus **both endpoints of every genuine two-internal-body channel have
positive circle load**, even at arbitrary true degree. Physically touching
the circle with zero selected weight is insufficient. The proof needs no
torque, planarity or lower radius window.

The preceding two-channel capacity theorem already showed that all long
channels among nine actual squares have one distinct endpoint pair. The
new theorem makes that pair positively loaded. It excludes long channels
ending at unloaded hubs or articulations while expressly preserving
parallel channels with the same two loaded endpoints.

Complete source:
UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md,
with full root, annular_capacity and axial_chain reviews.

## 3. Every direct-contact component contains a positive load

Suppress only genuinely unloaded true-degree-two paths in one complete
retained translational stress. Keep positively loaded vertices and all
unloaded positive-degree vertices of other degrees. An unloaded physical
square of degree zero is outside this graph domain and remains an actual
packing square. Keep parallel channels and their actual internal units.

Let H0 be the spanning subgraph consisting of the retained direct contacts,
with no internal body on an edge. Suppose one H0 component contained only
unloaded retained vertices. Dot each complete force equation with its
actual center and sum over that component. Each internal channel gives
a strictly negative contribution under the stated sign convention.
Each outgoing channel must contain an internal body, since every outgoing
direct edge would be in H0. Its center-projection gap is at least two,
so its endpoint contribution is less than

    mu*(M-2)=-29*mu/60<0,  M=91/60.

At least one positive force coefficient is present in the graph domain. The
strictly negative sum contradicts zero force balance. Hence every H0
component contains a positive circle load, including isolated retained
vertices. Every unloaded hub has a direct-contact path to a loaded vertex.

If h is the number of unloaded retained hubs and e0 the number of direct
edges, a spanning forest gives

    e0>=h.

This argument is uniform in graph size, block decomposition, parallel
channels and endpoint degree; it requires neither torque nor a planar
embedding. It is a necessary graph invariant, not a whole coarse-cell
exclusion.

Complete source:
DIRECT_CONTACT_COMPONENTS_OF_RETAINED_STRESS_CONTAIN_POSITIVE_LOADS_2026_10_30.md,
with full root and separate annular_capacity reviews.

## 4. Whole-side return localization and a larger junction-capacity region

For a compatible marked cycle with a long run and at least three boundary
marks, all return marks lie on one common side after a single reflection.
The coupled endpoint heights put the long endpoint directions within five
degrees of the long axis. Actual marked order and boundary separation
then put every return center in the same 35-to-145-degree sector, with
height greater than 43/60. Every point of every such return square is
therefore at height greater than 1/120.

The resulting center cap has projection width less than 827/420<2 in
every direction at least 45 degrees from the long axis. A nonempty
common-normal return run requires center-projection gap at least two.
Its normal must consequently lie within 45 degrees of the long axis.
This is actual whole-square clearance and an actual normal cone; it
does not assert a shared frame or a perpendicular direct join.

A separate force-free capacity theorem enlarges the region of translated
four-square junctions that force total packing capacity eight. In their
actual common frame, let P=|p_x| and T=|p_y|. It suffices that

    P,T<=5/16,
    (1-P)^2+(1-T)^2+1-max(P,T)+1/4 >= (91/60)^2.

This includes the entire closed box P,T<=1/5 and both rectangles with
one coordinate at most 1/20 and the other at most 5/16. Actual incircle
clearance from the real 2x2 block rules out diagonal completion regions.
The remaining center caps have total capacity at most two per axis. The
shallow half-cap diameter has exact squared upper bound 7189/7200<1.

For a genuine long channel whose middle contact is an actual four-square
junction, the preceding line barrier and this new capacity theorem force

    5/16<|t|<=9/16

in a nine-square packing. The record junction at |t|=9/16 is retained.

Complete sources:

- LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md
- TRANSLATED_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_BY_TWO_CAPS_PER_AXIS_2026_10_30.md

Both have complete root and separate independent reviews.

## 5. Retained pair-angle improvements and their superseded C8 tables

Three independently reviewed intermediate sources remain useful geometric
tools. They are frozen as written, and their historical C8 remainder tables
are superseded by the stronger bound (B):

- A true set gap at least one between two physical boundary squares forces
  their center angle to exceed 90 degrees. This first closed the whole
  alternating four-mark C8 family.
- The 40/90/105/175-degree combination gives
  8m+2k1+3d+11ell<=71.
- Two complete closed interior-arc profiles, proved with exact quartic
  certificates, strengthen physical boundary separation to more than 41
  degrees and a unit set-gap separation to more than 93 degrees. Their
  combined inequality is 41m+11k1+12d+52ell<=359. This closed the whole
  five-mark C8 family and the six-mark family containing a diagonal run.

The 41/93-degree pair theorems are force-free and remain valid independently
of the later occupied-arc proof. Their complete whole-arc inclusion includes
both own coordinates and every intermediate point. The diagonal-to-side
classification is used only with the same full moment certificate.

## 6. Frozen mathematical sources

| Source | SHA256 |
| --- | --- |
| OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md | `369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403` |
| UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md | `d6adb49263e0c2ffb3c1dc58477bef25ed2d0ae83bde59089c33d76c2d23b705` |
| DIRECT_CONTACT_COMPONENTS_OF_RETAINED_STRESS_CONTAIN_POSITIVE_LOADS_2026_10_30.md | `5b91a3b7e7f55317c706bdc6c1b65fd2bd0e99ce823411d5cbe73378dc8e151d` |
| LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md | `c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e` |
| TRANSLATED_FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_BY_TWO_CAPS_PER_AXIS_2026_10_30.md | `17f78403de1ab75d0de0aba42bf1344dd82e9c64822bf8743bd1e9f2d2ea5260` |
| BOUNDARY_UNIT_GAP_FORCES_OBTUSE_CENTER_ANGLE_AND_FOUR_LOAD_EIGHT_CYCLE_EXCLUSION_2026_10_30.md | `fa63e0ef4a0d94d47ff05e848b46792ac2861d0504b8369bc109beb3fd7d5e5a` |
| COMBINED_MARKED_CYCLE_BUDGET_AND_EIGHT_BODY_FIVE_LOAD_SIDE_REDUCTION_2026_10_30.md | `dbb9eaeee362c2148a6ada5319a05e0b962b5fdd2ea5ed36772e8175c8af005f` |
| BOUNDARY_ARCS_41_AND_UNIT_GAPS_93_DEGREES_EXCLUDE_FIVE_LOAD_EIGHT_CYCLES_2026_10_30.md | `aec4e482006c95ceadb6e3c9456c900ff6321511ea7bf61b1f7db2468c6c4c09` |

The checkpoint JSON pins all complete reviews, adoption text, metadata
and exact arithmetic. All previous mathematical sources remain unchanged.
Every new theorem has a complete root reconstruction and at least one
separate full review; a headline or a numerical check is not used as a
substitute for the continuous proof.

## 7. Exact remaining proof boundary

The new invariants remove whole cycle and channel families, but the original
22 coarse parents retain other graphs, attachments or completion domains.
For large cycles the explicit remaining obstruction is a circle-clear
branching vertex. For smaller stressed cores, all physical completing
squares still matter. The opposite seven-body long/side-short orbit
(2,0,1,0) remains a sharp test: the actual direct joins and coupled endpoint
tilts/heights have not yet been converted into the required q>=Q inequality.

The staggered nine-square equality example remains allowed. Its internal
heights need not coincide, its long channel is not a solid four-square row,
and its lower triple does not satisfy a fabricated sharp common cap. The
two remaining physical units cannot be deleted from a completion argument.
The same-pair parallel-channel equality domain is also preserved.

The selected physical certificate, all actual means, every positive force,
zero-weight physical circle corners and full true degrees remain explicit.
The planar translational and full rotational certificates have not been
declared identical. The inherited common-selection gate is still open.

Verification used complete hand-proof reconstruction and exact fraction/
polynomial identities. There was no Lean or Lake build, CI dispatch,
numerical pose search, orientation grid, new packing certificate or merge.
