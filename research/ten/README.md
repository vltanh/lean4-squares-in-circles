# Ten unit squares in a circle

Research checkpoint: 2026-10-29 (UTC), based on main commit
`4bea747b3efa13c869b956cb28435efaf21526fa`.

Start with the [case tree and progress bars](CASE_ROADMAP.md) for exactly what
remains. [HANDOFF.md](HANDOFF.md) records dependencies, failed shortcuts, and
validation. [CYCLE_CASES.md](CYCLE_CASES.md) lists all 279 larger-cycle cases.

**The sharp radius and complete equality family are proved by hand for the
entire common-coordinate-separated class, including independently rotated
squares, and for unrestricted packings with eight square centers at distance
at least `1` from the disk center. The remaining unrestricted cases are OPEN.**
The radius is `R* = 3/√2`, with squared radius `Q = 9/2`. Common-coordinate
separation means that one fixed pair of perpendicular directions separates
every square pair by disjoint projection interiors along at least one of
the directions. This is an additional hypothesis on `Packing`.

This research does not extend the public n≤8 Lean theorems.

Erich Friedman's [Squares in Circles](https://erich-friedman.github.io/packing/squincir/)
page, consulted on 2026-10-23, lists this n=10 radius and credits the construction
to Friedman (1997). It lists only n=1–8 as proved optimal. The coordinates and
arguments below are derived and checked here; the reference is provenance for
the known bound, not a lower-bound proof.

## What is established here

| Result | Evidence | Scope |
| --- | --- | --- |
| Ten squares fit at `Q = 9/2` | [Exact hand proof](CONSTRUCTION.md), [rational witness](construction.json), [checker](check_construction.py) | Upper bound only |
| Sharp radius and complete six-parameter equality family for all parallel packings | [All-parallel theorem](ALL_PARALLEL_THEOREM.md) | Arbitrary centres; common square orientation |
| Same sharp theorem with independent orientations and common-coordinate separation | [Rectification theorem](COORDINATE_RECTIFICATION.md) | One common orthogonal separating frame |
| Complete physical completion of four anchors | [Anchored equality classification](ANCHORED_EQUALITY_CLASSIFICATION.md) | Remaining six orientations initially unrestricted |
| Three squares in a sharp cap force alignment and boundary anchors | [Three-square cap](THREE_SQUARE_CAP.md) | Arbitrary orientations, all wholly beyond a line at distance `1/2` from the disk centre |
| A square in an outward quadrant forces the sharp corner bound | [Corner rigidity](CORNER_RIGIDITY.md) | Arbitrary orientation |
| At least two squares enter the central disk of radius `1/2` | [Exterior-arc bound](CENTRAL_DISK_REDUCTION.md) | Arbitrary orientations; squared containing radius at most `9/2` |
| Eight exterior squares force four anchors; the exactly-two-central case is closed | [Sharp exterior ring](SHARP_EXTERIOR_RING.md) | Arbitrary orientations; no common separating frame assumed |
| Eight centers outside the open unit disk force four anchors | [Center-radius reduction](CENTER_RADIUS_REDUCTION.md) | Arbitrary orientations; a smaller ten-packing must have exactly 3, 4, or 5 centers in the open unit disk |
| A square's arc cost bounds its center's squared radius | [Inner arc moment](INNER_ARC_MOMENT.md) | Hand proof; used in the completed five-center exclusion |
| An inner center of norm at least `.9` costs more than `pi/6` on the test circle | [Large inner arc](LARGE_INNER_ARC.md) | Hand proof; at most two such centers in the four-inner case and at most one in the three-inner case |
| Five inner centers either form the aligned plus or a strict convex pentagon | [Moment reductions](FIVE_CENTER_MOMENT_REDUCTIONS.md) | Hand proof; independent outward radial translations preserve disjointness |
| Five squares centered in the closed unit disk have squared-center moment at least four, with equality only for the plus | [Completed moment proof](FIVE_CENTER_LARGE_TURNS.md), [small turns](FIVE_CENTER_SMALL_TURNS.md), [printed table](FIVE_CENTER_LARGE_TURNS_TABLE.md) | Hand argument with 78 explicit finite-table cases and 1,193 rational vertex bounds; excludes five inner centers in a ten-packing |
| Four inner squares have hull width at least two in every direction | [Four-center width](FOUR_CENTER_WIDTH.md) | Hand proof; does not yet exclude six outer squares |
| Three squares wholly inside the test circle almost fill a smaller circle | [Three-core stability](THREE_CORE_INNER_STABILITY.md) | Hand proof with an explicit no-protrusion hypothesis |
| Two or three origin-vertex squares bound total capacity by nine or eight | [Origin-vertex capacity](THREE_ORIGIN_VERTEX_SQUARES.md) | Hand proof for squared containing radius at most `17/4` |
| One origin-vertex square plus three radial side terminals bounds capacity by nine | [One-origin capacity](ONE_ORIGIN_VERTEX_THREE_TERMINALS.md) | Hand proof at squared radius `17/4` |
| Two fixed interior points stab every square in the specified upper one-unit neck | [One-neck stabbing theorem](ONE_NECK_STABBING.md) | Complete hand proof at `17/4`; implies capacity two in that region |
| Every staggered four-square S-S chain has total capacity at most nine | [Chain completion](STAGGERED_CHAIN_REDUCTION.md), [three-point theorem](WIDE_NECK_THREE_POINT_STABBING.md) | Hand proof for all slide parameters and arbitrary orientations of additional squares |
| The exceptional five-square tree core has total capacity at most nine | [Exceptional-core completion](KAPPA_CORE_COMPLETION.md) | Hand proof uniform in its transverse slide parameter |
| Every nonzero minimizing stress component must contain a cycle | [Expanded tree inventory](EXPANDED_TREE_INVENTORY.md) | Hand tree exclusion in the stated radius window; lower window imported explicitly from n=8 |
| Every entirely circle-loaded positive component is a seven-square physical ring enclosing the other three squares | [Loaded-ring theorem](ALL_LOADED_COMPONENT_RINGS.md) | Conditional on an entirely loaded component in a strictly subcritical ten-packing |
| The loaded ring's contact-force polygon strictly contains the origin | [Force circulation](SEVEN_RING_FORCE_CIRCULATION.md), [strict containment](SEVEN_RING_FORCE_ORIGIN.md) | Hand proof using original physical force witnesses |
| Loaded-body force lines concur inside their closed squares; the physical contact polygon is convex and contains the three inner squares | [Internal concurrence](SEVEN_RING_INTERNAL_CONCURRENCE.md) | Hand proof covering unique and double geometric circle vertices; no sufficient capacity bound for this polygon yet |
| Every loaded-ring contact magnitude is within a factor `32/9` of every other; one-chirality incoming contacts force `R cos(alpha)>1` | [Force ratios and neighbor containment](SEVEN_RING_FORCE_RATIO.md) | Reviewed hand necessary conditions using the original physical neighbors |
| One-chirality hole vertices outside the opposite-corner disk lie in explicit contact triangles and in their base-diameter disks | [Spike reduction](SEVEN_RING_SPIKE_REDUCTION.md) | Reviewed hand reductions; the local cap bounds below supply completion obstructions |
| A loaded ring with common signed frame offsets cannot contain three further squares | [Uniform-ring exclusion](REGULAR_SEVEN_LOADED_RING.md) | Hand proof; other ownership patterns remain open |
| Adjacent opposite-corner moments bound the capacity of a one-chirality hole | [Corner-moment capacity](SEVEN_RING_CORNER_MOMENT_CAPACITY.md) | Reviewed hand sufficient condition, including the displayed own-coordinate subcase |
| Every strict one-chirality side/vertex ring is uniform and cannot enclose three more squares | [Global action theorem](SEVEN_RING_GLOBAL_ACTION.md), [exact verifier](check_seven_ring_action.cpp) | **Computer-assisted**, independently audited; the separate hand cap theorem below now excludes its completion pattern |
| A loaded body supported on its two inner sides has a small opposite corner | [Double-side restriction](LOADED_DOUBLE_SIDE_RESTRICTION.md) | Reviewed hand necessary bounds; other ring ownership remains open |
| Every physical one-chirality seven-ring has insufficient room for three inner squares | [Hand cap theorem](SEVEN_RING_RADIAL_CAP_BOUND.md), [chord bound](SEVEN_RING_CAP_CHORD_BOUND.md) | Reviewed hand closure: squared inner radius below `33/20<425/256` |
| Every surviving selected seven-ring contains an outer-edge/opposite-corner row U4 or U5 | [All-inner-face capacity](SEVEN_RING_ALL_INNER_FACE_CAPACITY.md), [outer-edge reduction](SEVEN_RING_OUTER_EDGE_REDUCTION.md) | Reviewed hand reductions including arbitrary radial bodies and SS/VV pairs; U4/U5 remain open |
| The extra U4/U5 corner has squared norm below 9/2-2sqrt(2); if it reaches 83/50, its opposite-corner pair is proper V/S | [Outer-body bounds](LOADED_OUTER_MIXED_RESTRICTIONS.md), [VV normal selection](LOADED_OUTER_VV_NORMAL_EXCLUSION.md) | Reviewed hand restrictions; the S neighbor has unique-circle row U1/U6/U7; the capacity gap remains open |
| Generic selection restricts unique-circle endpoints of loaded-ring VV pairs | [Concurrence-polynomial selection](LOADED_VV_GENERIC_RESTRICTION.md) | The other pair must be an SS overlap with interior aggregate application; radial load splits remain outside this restriction |
| The incident opposite-corner rows U2/U3 are impossible in a loaded ring | [Incident mixed exclusion](LOADED_INCIDENT_MIXED_EXCLUSION.md) | Reviewed hand local exclusion allowing either support type on each loaded neighbor |
| The unique-circle D-S three-loaded five-cycle is impossible | [D-S exclusion](DIAGONAL_SIDE_EXCLUSION.md), [exact table checker](check_diagonal_side_clearance.py) | Reviewed hand closure, including both endpoint load patterns |
| The entire three-loaded five-cycle is impossible | [Final S-S exclusion](SIDE_SIDE_EXCLUSION.md), [complete case index](MIXED_FIVE_CYCLE_STATUS.md) | Reviewed hand closure of all ordered transmitter choices and both central circle-contact types |
| The unique-circle S-D three-loaded five-cycle is impossible | [S-D exclusion](SIDE_DIAGONAL_EXCLUSION.md) | Reviewed hand closure by torque and elementary analytic clearance; no finite interval table |
| A four-loaded diagonal five-cycle permits at most one other square wholly inside the test disk | [Inner trace restriction](DIAGONAL_FIVE_CYCLE_INNER_TRACE.md) | Reviewed hand restriction used in the nearer-endpoint exclusion below |
| Every whole mixed simple cycle follows loaded radial order; the strip cap gives stronger angle bounds | [D-D uncrossing](DIAGONAL_PATH_UNCROSSING.md), [cap-angle theorem](TRANSMISSION_CAP_ANGLE_BOUND.md), [234-case budget](SHARP_TRANSMISSION_CYCLE_BUDGET.md) | Reviewed hand structural theorem and exclusions; with the six-cycle results, 238 cases are closed and 41 shorter signatures remain |
| Three-loaded six-cycles with an SS path are excluded | [SS/D exclusion](SS_DIAGONAL_SIX_CYCLE_EXCLUSION.md), [SS/S exclusion](SS_SIDE_SIX_CYCLE_EXCLUSION.md) | Reviewed hand closures of `LLDLSS` and `LLSLSS` for the selected certificate |
| Three-loaded six-cycles with at least two D paths are excluded | [D-path forest](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md), [two-D/one-S exclusion](TWO_DIAGONAL_ONE_SIDE_SIX_CYCLE_EXCLUSION.md) | Reviewed hand closures of `LDLDLD` and `LSLDLD`; every D-path graph is a forest of paths |
| A physical stress can be selected with a planar body-pair graph and the loaded vertices on its exterior face in radial order | [Planar selection](PLANAR_SELECTED_PHYSICAL_STRESS.md) | Reviewed hand existence theorem compatible with the normal restrictions used by the case ledger |
| The four-loaded diagonal five-cycle has a force quadrilateral strictly around zero | [Force quadrilateral](FOUR_LOADED_FORCE_QUADRILATERAL.md), [trace-route obstruction](DIAGONAL_CORE_TRACE_OBSTRUCTION.md) | Reviewed hand necessary geometry; scalar transmitter bounds alone do not force enough trace |
| Every four-loaded five-cycle is excluded for the selected certificate | [Diagonal exclusion](DIAGONAL_FIVE_CYCLE_EXCLUSION.md), [generic normal selection](GENERIC_CONTACT_NORMAL_SELECTION.md), [nearer endpoint](DIAGONAL_FIVE_CYCLE_NEAR_ENDPOINT.md) | Reviewed hand closure of C19: D neighbors must have side-interior contacts, but the nearer endpoint cannot have side support |
| With at most one diagonal transmitter, a mixed simple cycle follows loaded radial order | [Single-side uncrossing](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md), [117-case batch](single_side_cycle_batch.json) | Reviewed hand theorem; 90 closures in that batch; superseded in coverage by the 206-case theorem |
| Two transmission runs sharing a loaded endpoint obey strict angular budgets | [Shared-endpoint cases](SHARED_ENDPOINT_CYCLE_ANGLE_BUDGET.md), [seven-loaded cases](SEVEN_LOADED_LONG_PATHS.md) | Reviewed hand closures of eleven further larger-cycle entries; [uncrossing](TRANSMISSION_PATH_UNCROSSING.md) closes thirteen more |
| A radial-side central body cannot occur in the three-loaded five-cycle | [Full radial D-D exclusion](RADIAL_SIDE_DD_EXCLUSION.md) | Reviewed hand closure, together with the earlier S-S and S-D arguments |
| Several mixed cyclic stress patterns are impossible | [Cyclic reductions](CYCLIC_STRESS_REDUCTIONS.md), [remaining five-cycle form](SIDE_NORMAL_MIXED_FIVE_CYCLE.md) | Conditional hand reductions; neither a complete graph classification nor a global exclusion |
| Branching components with every branch vertex loaded have a fixed catalog of 45,666 cases | [Catalog](BRANCHING_LOADED_SKELETON_INVENTORY.md), [combined exact graph certificates](BRANCHING_SELECTED_GRAPH_FILTERS.md) | Independent enumerators agree; 42,532 excluded and 3,134 remain; unloaded branch vertices are outside this subclass |
| Branching components with exactly one unloaded retained vertex have 524,870 fixed cases | [Catalog](BRANCHING_ONE_UNLOADED_INVENTORY.md), [proof decoder](BRANCHING_ONE_UNLOADED_FILTERS.md) | Independent enumerators and checkers agree; 385,071 excluded and 139,799 remain; b>=2 remains outside both catalogs |
| One unloaded branch vertex and exactly two loaded bodies cannot occur | [Complete exclusion](ONE_UNLOADED_TWO_LOADED_EXCLUSION.md) | Reviewed hand capacity bound for the forced five-square core, including arbitrary orientations of additional squares |
| A five-cycle with four loaded squares cannot use a side transmitter | [Four-loaded five-cycle](MIXED_FIVE_FOUR_LOADED.md) | Side transmitter excluded by hand in the explicitly imported radius window; the diagonal branch is now excluded above for the chosen certificate |
| Parallel four-inner cores have a line-separated or pinwheel form; narrow internal channels can be filled as virtual obstacles | [Projection graphs and channel lemma](FOUR_CORE_GENERALIZATION.md) | Hand structural reduction and exact localized pinwheel; no general completion bound |
| A solid two-by-two core, with its four centers in the closed unit disk, admits at most five additional squares | [General translated-block theorem](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md) | Hand proof for every translation and rotation; additional orientations arbitrary |
| A specified symmetric two-row core with two center norms at most `.65` has total capacity at most nine | [Two-row theorem](SYMMETRIC_TWO_ROW_COMPLETION.md) | Hand proof over the full stated parameter family; does not normalize arbitrary cores |
| The upper offsets in that two-row core may be unequal | [Asymmetric two-row theorem](ASYMMETRIC_TWO_ROW_COMPLETION.md) | Hand proof with offsets at least `1/4` and the stated lower-row displacement bound |
| The quarter-unit upper-offset restriction can be removed | [Extreme-asymmetry theorem](EXTREME_ASYMMETRIC_TWO_ROW.md) | Independently reviewed hand proof for the displayed two-row core; arbitrary cores remain open |
| The lower pair may be separated throughout the wider displacement interval | [Combined two-row theorem](SEPARATED_WIDE_TWO_ROW.md) | Reviewed hand proof for the exact displayed common-frame core; arbitrary extra orientations |
| The sharp cap beginning at `sqrt(7/2)-1` contains at most two squares, with a unique pair | [Sharp two-square cap](SHARP_TWO_SQUARE_CAP.md) | Hand proof; any stricter cap contains at most one |
| An aligned two-by-two block translated along a side direction admits at most five further squares | [Translated-block obstruction](TRANSLATED_BLOCK_OBSTRUCTION.md) | Hand proof with the four core centers in the closed unit disk; remaining orientations arbitrary |
| A solid two-by-two block with two center norms above `.9` admits at most five outer-center squares | [Localized-block obstruction](LOCALIZED_BLOCK_OBSTRUCTION.md) | Conditional hand proof allowing arbitrary translation; its application uses computational radial localization |
| Five centers in the closed unit disk are impossible for a ten-packing | [Radial weight certificate](RADIAL_WEIGHT_EXCLUSION.md), [integer checker](check_radial_weight_exclusion.py) | Earlier **computer-assisted** reduction retained for comparison; the five-inner case now has the separate finite-table hand proof above |
| Four inner centers must split into two norms at most `.65` and two above `.9` | [Radial count localization](RADIAL_COUNT_LOCALIZATION.md), [integer checker](check_radial_count_localization.py) | **Computer-assisted**, conditional on exactly four inner centers |
| Sharp lower bound from four anchors | [Four-anchor bound](FOUR_ANCHOR_BOUND.md) | Four common-frame squares with the stated coordinate gaps |
| Exact finite formulation and existence of a minimizer | [Unrestricted model](UNRESTRICTED_MODEL.md) | Arbitrary individual orientations; no sharp lower bound |

The earlier [three-column theorem](THREE_COLUMN_THEOREM.md) is retained as a
short special case; the all-parallel theorem removes its column hypothesis.
The [six-parameter family](CONSTRUCTION.md#six-parameter-family) is now proved
exhaustive within the common-coordinate class and within the four-anchor
class. Global exhaustiveness is not proved.

The hand arguments have received separate mathematical review within this
work session. The construction checker certifies the displayed witness.
The five-center proof prints its full finite table and proves why those
inequalities suffice; its separate exact checker re-enumerates the vertices,
checks the cover, and verifies every rational bound. The radial-count
certificates remain computational results with their own stated scope.
**No n=10 Lean source has been compiled or kernel-checked.**

![Ten-square construction at squared radius 9/2](construction.svg)

## Roadmap and next obligation

<!-- CASE_PROGRESS_START -->
**Main gates:** `███░░░░` **3/7 closed**.

**G3 lower-bound case ledger:** `██████████████████░░░`
**18 hand closed · 0 computer closed · 3 open / 21 terminal families.**

**C20 larger-cycle subcases:** `████████████████████▍░░░` **238/279 closed; 41 open.**

**C05 branching subclass, all branch vertices loaded:** `██████████████████████▎░` **42,532/45,666 excluded; 3,134 remain.** [Catalog and certificates](BRANCHING_SELECTED_GRAPH_FILTERS.md). This is the fixed `b=0` subledger.

**C05 branching subclass, exactly one unloaded branch vertex:** `█████████████████▌░░░░░░` **385,071/524,870 excluded; 139,799 remain.** [Catalog and proof decoder](BRANCHING_ONE_UNLOADED_FILTERS.md). At least two unloaded branch vertices remain outside these catalogs.

`█` reviewed hand deduction; `▓` reviewed computer-assisted result; `░` open. These are counts of the fixed ledger entries, **not a percentage of the proof or remaining effort**. Every currently closed family has a reviewed hand deduction; imported dependencies remain as stated in each proof.

[Open the full case tree and remaining obligations](CASE_ROADMAP.md). [Browse all 279 larger-cycle cases](CYCLE_CASES.md).
<!-- CASE_PROGRESS_END -->



The next mathematical task is a lower-bound argument covering configurations
outside the common-coordinate class. The rectification proof preserves
separation because it shrinks each square's bounding box. For a merely
physical packing those bounding boxes can overlap, so that argument does
not supply a global reduction.

The cap and corner theorems give precise unrestricted necessary conditions:
in a hypothetical packing with `q<9/2`, every central open strip of width one
meets at least six squares, and every square meets the union of the two such
perpendicular strips. These conditions have not been shown contradictory.
Finding a sharp cap triple in some frame would close the lower bound, but
no universal cap-extraction theorem is claimed.

The sharp exterior-ring theorem uses the circle of radius
`sqrt(1+1/sqrt(2))`: every square avoiding `B(0,1/2)` occupies an arc of angle
at least `pi/4`. Eight such squares must alternate two equality types and
therefore supply the four anchors. This proves that every hypothetical
ten-square packing below `9/2` has **at least three central squares**. It also
closes the complete equality classification when exactly two are central.

The center-radius strengthening proves the same minimum arc angle whenever
the square's center has norm at least `1`, even if the square intersects
`B(0,1/2)`. Its third possible equality type cannot occur in an eight-arc
ring. Consequently any smaller ten-packing must have at least three centers
in `B(0,1)`; pairwise center distances of at least one bound this count by
five. The [completed five-center moment theorem](FIVE_CENTER_LARGE_TURNS.md)
then excludes five inner centers: its strict moment bound and the inner-arc
estimate make the ten disjoint traces longer than the test circle. Its
large-turn part uses an explicit finite table, with every case and rational
vertex bound printed for inspection. Thus the remaining counts are
**3 and 4 inner centers**. The older 1,954-box radial-weight certificate
is retained as an independent computational route, not a premise of the
new moment argument.

The [large-inner-arc lemma](LARGE_INNER_ARC.md) replaces one branch of the
radial-count argument by hand. A proposed unrestricted bound of five usable
outer arcs around four inner squares is false: the exact
[gap obstruction](FOUR_CORE_GAP_OBSTRUCTION.md) allows six abstract arcs.
The [localized gap counterexample](LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md)
also defeats that bound under the two-small/two-large radial split.
The [general translated-block theorem](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md)
now excludes every solid two-by-two core whose centers lie in the closed
unit disk, without radial localization. The
[symmetric two-row theorem](SYMMETRIC_TWO_ROW_COMPLETION.md) also excludes
the physical core family containing the localized gap counterexample.
Neither theorem applies to arbitrary four-square cores. The simpler
center-only argument has its own
[exact limitation](DIAGONAL_BLOCK_CENTER_RELAXATION.md).

A [rational six-square example](SIX_CENTRAL_SQUARES.md) rules out the shortcut
that at most four or five squares can meet the small disk. It is not a
ten-square packing. The remaining argument must use the interaction between
central and exterior squares; a small central count alone is insufficient.

Two further manuscripts record a separate approach through contact forces.
[Physical tree reductions](PHYSICAL_TREE_REDUCTIONS.md) proves a cover of
all positive bridges by at most four circle-clear squares, classifies tree
components with exactly two loaded squares, and excludes stars above an
explicit radius. Its stress-existence inputs are pinned to the cited n=9
research commit. These are conditional graph results, not an exhaustive
classification of a minimizing packing.

[Staggered-chain completion](STAGGERED_CHAIN_REDUCTION.md) is now closed:
the barrier splits additional squares into two half-planes, the three-point
theorem bounds each group by three, and the sign of a slide parameter lets
the two-point theorem bound one group by two. The stronger upper-triple
rigidity conjecture remains optional and open.

The [expanded tree inventory](EXPANDED_TREE_INVENTORY.md) includes an
additional five-square family that appears beyond the earlier n=9 radius
window. Its [physical completion](KAPPA_CORE_COMPLETION.md) is now excluded
as well. Together with the origin-incidence capacity bounds, these results
exclude every nontrivial positive tree component. The lower radius window
is supplied by the explicitly cited n=8 theorem.

The [cyclic reductions](CYCLIC_STRESS_REDUCTIONS.md) exclude two-terminal
cycles and several small components. An
[entirely loaded component](ALL_LOADED_COMPONENT_RINGS.md) must be a
seven-square physical ring enclosing three inner squares. Its
[force polygon strictly contains zero](SEVEN_RING_FORCE_ORIGIN.md), its
[force-line intersections lie inside their bodies](SEVEN_RING_INTERNAL_CONCURRENCE.md),
and the actual contact points form a convex polygon enclosing the three
remaining squares. No sufficient area or circumradius bound for this polygon
has been proved. The
[common signed-offset case](REGULAR_SEVEN_LOADED_RING.md) is excluded.
For one fixed side/vertex ownership pattern,
[exact scalar equations](SEVEN_RING_ONE_CHIRALITY.md) show that equal force
magnitudes or equal frame turns force the excluded uniform ring. Simultaneous
variation is now excluded for this ownership pattern by the
[independently audited exact recurrence theorem](SEVEN_RING_GLOBAL_ACTION.md).
A separate [hand cap theorem](SEVEN_RING_RADIAL_CAP_BOUND.md) now excludes
the complete one-chirality completion pattern without that interval step.
Mixed components remain open. In the
[five-cycle normal form](SIDE_NORMAL_MIXED_FIVE_CYCLE.md), both
[two diagonal transmitters](DIAGONAL_MIXED_FIVE_CYCLE.md) and
[diagonal-then-side transmitters](DIAGONAL_SIDE_EXCLUSION.md) are excluded.
The [S-D hand exclusion](SIDE_DIAGONAL_EXCLUSION.md) now closes that
ordered transmitter choice as well. When the central loaded
square has two circle vertices, the
[full radial D-D exclusion](RADIAL_SIDE_DD_EXCLUSION.md) closes the final
transmitter type. The [mixed five-cycle status](MIXED_FIVE_CYCLE_STATUS.md)
now leaves only the four-loaded diagonal-transmitter five-cycle open.
The [S-S exclusion](SIDE_SIDE_EXCLUSION.md) closes the last three-loaded branch.
The uniform side/vertex ring is [locally isolated](SEVEN_RING_LOCAL_RIGIDITY.md),
and its [angle action](SEVEN_RING_ANGLE_ACTION.md) now has the separately
labeled [computer-assisted global classification](SEVEN_RING_GLOBAL_ACTION.md).
Other loaded-ring ownership patterns remain open. The
[planar junction construction](PLANAR_CONTACT_TORQUE_CYCLES.md) preserves
the physical forces but does not prove that every torque cycle encloses zero.

Two further conditional theorems have now passed
[independent review](TWO_ROW_EXTENSION_AUDIT.md):
[a wider row-displacement range](WIDE_DISPLACEMENT_TWO_ROW.md) and
[a separated lower pair](SEPARATED_LOWER_TWO_ROW.md). These still require
their displayed common-frame two-row cores. See [HANDOFF.md](HANDOFF.md)
for the remaining general core and cyclic-component obligations. The
[combined theorem](SEPARATED_WIDE_TWO_ROW.md) now permits both extensions
simultaneously, with their interaction checked explicitly.

Even the established equality family can have five distinct x-coordinates;
the all-parallel proof handles those configurations directly. No unproved
three-column normalization is used.

For the eventual Lean construction, the existing
[`Common/Constructions.lean`](../../SquaresInCircles/Common/Constructions.lean)
provides `axis_packing`. The new witness can be defined in a separate n=10 module
without changing `optimalRadius`, whose value at 10 is currently a placeholder.
The unrestricted formulation uses the interfaces of
[`Geometry.lean`](../../SquaresInCircles/Geometry.lean) and
[`Common/SeparatingAxes.lean`](../../SquaresInCircles/Common/SeparatingAxes.lean).

## Reproduce the checks

From the repository root, with Python 3 and no external packages:

```sh
python3 research/ten/check_construction.py --self-test
python3 research/ten/check_core_obstruction.py
python3 research/ten/check_five_center_large_turns.py
python3 research/ten/check_radial_weight_exclusion.py
python3 research/ten/check_radial_count_localization.py
python3 research/ten/check_cycle_cases.py
python3 research/ten/update_case_roadmap.py
python3 -B research/ten/plot_construction.py
```

The first command checks all 40 vertices and 45 pairs using `Fraction`, identifies
the four tight corners, and rejects deliberately overlapping, exterior, and
floating-point witnesses. Vertex containment implies whole-square containment
by convexity of the disk. The central-obstruction checker verifies six squares,
all 15 separating pairs, and strict near/far distance bounds using rational
arithmetic. The radial-weight checker proves continuous one-square bounds
using integer Riemann sums and a complete dyadic parameter cover; it uses no
floating-point arithmetic. The figure uses floating point only for drawing
and is not a proof input.

The five-center checker uses only standard-library rational arithmetic.
It verifies all 78 cells, 1,193 vertices, 42 covering roots, and both
singleton cross-references, with uniform lower bound
`200007133/50000000 > 4` on the large-turn fan branch.

This checkpoint changes only `research/ten/`. No Lean build, axiom audit,
Comparator run, or external kernel replay is claimed. Commits use `[skip ci]`
for this research-only draft, following the existing research PR convention.

The exact computer-assisted ring check and its independent sanitizer replay are
recorded in [SEVEN_RING_ACTION_AUDIT.md](SEVEN_RING_ACTION_AUDIT.md). Its
[reproduction command](SEVEN_RING_GLOBAL_ACTION.md#6-arithmetic-and-reproducibility)
uses a C++17 compiler with `__int128`. This result is separate from the hand
proof ledger and does not constitute a Lean kernel check.
