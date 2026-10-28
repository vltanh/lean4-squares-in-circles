# n=10 research handoff — updated 2026-10-28

PR: <https://github.com/vltanh/lean4-squares-in-circles/pull/12>  
Branch: `research/ten-exact-start`  
Original base: `4bea747b3efa13c869b956cb28435efaf21526fa`

**The unrestricted n=10 lower bound remains open.** The target is squared
radius `Q=9/2`, for arbitrary independently oriented unit squares with
disjoint open interiors. No n=10 Lean theorem, build, or kernel check is
claimed. This PR changes only research artifacts under `research/ten/`.

## Start here

[README.md](README.md) indexes the completed arguments and their hypotheses.
[UNRESTRICTED_MODEL.md](UNRESTRICTED_MODEL.md) states the physical model and
exact finite formulation. The exact construction at `Q` is checked by
[check_construction.py](check_construction.py); it is an upper bound.

The sharp bound and complete equality family are proved for the entire
common-coordinate-separated class, including independently oriented
squares. See [COORDINATE_RECTIFICATION.md](COORDINATE_RECTIFICATION.md) and
[ALL_PARALLEL_THEOREM.md](ALL_PARALLEL_THEOREM.md). A physical packing need
not have that separation property.

[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md) closes the
unrestricted case with at least eight centers outside the open unit disk.
The completed [five-center moment proof](FIVE_CENTER_LARGE_TURNS.md) excludes
five inner centers by an explicit finite-table argument. Thus a hypothetical
smaller ten-packing must have **exactly three or four inner centers**.
The equality classification remains open outside the completed classes.

## Snapshot at pause

This handoff preserves the remaining manuscripts as well as the completed
results. Work paused at the user's request to commit and push. No proof of
the unrestricted n=10 optimum is claimed.

| Manuscript added in this checkpoint | Status at pause |
| --- | --- |
| [Extreme upper asymmetry](EXTREME_ASYMMETRIC_TWO_ROW.md) | Independent full mathematical review passed; removes the quarter-offset restriction for the stated touching-lower-pair core with `0<t<=5/12` |
| [Seven-angle action](SEVEN_RING_ANGLE_ACTION.md) | Independent full mathematical review passed; exact reduction for one contact pattern, with no global uniqueness result |
| [Wider row displacement](WIDE_DISPLACEMENT_TWO_ROW.md) | Draft; independent audit incomplete. Proposed interval is `0<t<3/2-2^(-1/4)` |
| [Separated lower pair](SEPARATED_LOWER_TWO_ROW.md) | Draft; independent audit incomplete. Proposed extension removes lower-pair touching under the displayed bounds |

Resume by auditing the two marked drafts before applying them. Even if both
are correct, they cover specified common-frame two-row cores; there is no
argument reducing every four-inner-square core to those arrangements.

The one-chirality ring work now has the exact seven-angle action, positive
root branch, criticality equations, and derivative formulas in the linked
note. A promising unproved route is a phase-rotation bound for its nonlinear
recurrence: numerical exploration suggested a two-step bound that would
exclude nonconstant period-seven orbits. Neither that bound nor the
resulting global uniqueness assertion has been proved. Positive mixed
contact ownership patterns also remain outside this one-chirality model.

For the radial-side mixed five-cycle, two diagonal transmitters remain.
An exploratory symmetric stationary candidate overlapped at its two
transmitters, so endpoint force equations alone do not certify a physical
core. In the symmetric corner-contact case, transmitter disjointness forces
the outward angle to be at least `pi/12`. Turning separation into a full
exclusion or a capacity bound is still required; no such exclusion is
claimed in [MIXED_FIVE_CYCLE_STATUS.md](MIXED_FIVE_CYCLE_STATUS.md).

## Remaining obligations

1. **Three inner centers.** Seven outer squares consume at least `7pi/4`
   on the test circle of radius `sqrt(1+1/sqrt(2))`. Their interaction with
   the three inner squares remains open.
   [THREE_CORE_INNER_STABILITY.md](THREE_CORE_INNER_STABILITY.md) requires
   all three squares to lie wholly inside the test circle; center norms
   below one do not supply that hypothesis. Pure radial additive weights
   did not close this case in numerical exploration.
2. **Four inner centers.** Six outer arcs each have length at least `pi/4`.
   [FOUR_CENTER_WIDTH.md](FOUR_CENTER_WIDTH.md) gives core-hull width at
   least two in every direction. The separate computational
   [radial localization](RADIAL_COUNT_LOCALIZATION.md) forces two center
   norms at most `.65` and two strictly above `.9`.
   [LARGE_INNER_ARC.md](LARGE_INNER_ARC.md) proves by hand that at most two
   of four inner centers, and at most one of three, have norm at least `.9`.
   Abstract complementary-gap capacity fails even under radial localization:
   see [FOUR_CORE_GAP_OBSTRUCTION.md](FOUR_CORE_GAP_OBSTRUCTION.md) and
   [LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md](LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md).
   The [general block theorem](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md)
   nevertheless excludes every solid two-by-two core whose centers lie in
   the closed unit disk, for arbitrary translation and rotation, with no
   computational radial-count premise.
   [SYMMETRIC_TWO_ROW_COMPLETION.md](SYMMETRIC_TWO_ROW_COMPLETION.md) excludes
   the specified symmetric two-row family with two center norms at most
   `.65` and the other two at most one. Neither result normalizes arbitrary
   four-square cores to those families. The reviewed
   [extreme-asymmetry extension](EXTREME_ASYMMETRIC_TWO_ROW.md) now permits
   all upper offsets satisfying its center bounds when the lower pair
   touches. The broader proposals in the snapshot table remain drafts.
3. **Nonuniform loaded rings.** An entirely circle-loaded positive component
   of a strictly subcritical ten-packing must be a seven-square physical
   ring enclosing the other three squares:
   [ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md).
   Its contact-force polygon is strictly convex and strictly contains zero,
   by [SEVEN_RING_FORCE_CIRCULATION.md](SEVEN_RING_FORCE_CIRCULATION.md) and
   [SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md). Each body's
   two force lines concur on its positive circle-load ray.
   [SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md)
   now places every such intersection inside its closed square, including
   the two-circle-vertex case. The actual contact points form a convex
   polygon containing all three inner squares. A capacity bound for that
   polygon remains open; it is an enclosure of the free hole, not the hole
   itself, and their areas must not be confused.
   [REGULAR_SEVEN_LOADED_RING.md](REGULAR_SEVEN_LOADED_RING.md) excludes
   common signed frame offsets. The smooth stressed member has hole area
   below `231/80<3`; the radial-side endpoint has a hole inside a disk of
   radius below `5/4`; the radial-diagonal endpoint exceeds the target
   radius. General nonuniform rings remain open. For one side/vertex
   ownership pattern, [SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md)
   derives exact equations. Equal contact magnitudes or equal frame turns
   force the uniform ring, but neither equality is established in general.
   [SEVEN_RING_LOCAL_RIGIDITY.md](SEVEN_RING_LOCAL_RIGIDITY.md) proves that
   the normalized uniform scalar solution is locally isolated. No explicit
   neighborhood size or global uniqueness is claimed.
   [SEVEN_RING_ANGLE_ACTION.md](SEVEN_RING_ANGLE_ACTION.md) removes the seven
   force magnitudes and reduces this ownership pattern to critical points
   of an angle sum. It still requires the physical inequalities and
   nonneighbor separation; it does not classify all contact patterns.
4. **Mixed cyclic stress components.**
   [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md) excludes
   two-terminal components made of transmission paths and several small
   loaded graphs. Components with branching cyclic blocks, five-cycles with
   four loaded bodies, and larger mixed cycles remain open. For a whole
   five-cycle `A-U-C-V-B-A` with precisely `A,B,C` loaded, the following
   patterns are excluded: [parallel transmissions](PARALLEL_MIXED_FIVE_CYCLE.md),
   [equal-type common-corner contacts](COMMON_CORNER_SIDE_TRANSMISSIONS.md),
   and [mixed-type common-corner contacts](COMMON_CORNER_MIXED_TRANSMISSIONS.md).
   When `C` has a unique circle vertex,
   [both contacts cannot be vertices](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md).
   [SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md) excludes
   two side-normal transmissions and derives the remaining opposite-corner
   and adjacent-side-interior contact form.
   [DIAGONAL_MIXED_FIVE_CYCLE.md](DIAGONAL_MIXED_FIVE_CYCLE.md) excludes two
   diagonal transmitters in that form, so at least one must be a side
   transmitter. If the vertex transmitter is diagonal,
   [DIAGONAL_SIDE_ENDPOINT_REDUCTION.md](DIAGONAL_SIDE_ENDPOINT_REDUCTION.md)
   forces the opposite endpoint to be rotated and contacted at a vertex.
   For the reverse side-to-diagonal pattern,
   [SIDE_DIAGONAL_LEFT_ENDPOINT.md](SIDE_DIAGONAL_LEFT_ENDPOINT.md) forces a
   vertex-supported first endpoint to have an edge pointing right in C's
   frame. When C has two geometric circle vertices,
   [RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md)
   leaves only two diagonal transmitters. It uses the slightly sharper
   imported lower bound `R^2>5/2+sqrt(2)`, with the n=8 bracket dependency
   explicitly stated. [MIXED_FIVE_CYCLE_STATUS.md](MIXED_FIVE_CYCLE_STATUS.md)
   consolidates all remaining patterns; this component is not yet excluded.
   [PLANAR_CONTACT_TORQUE_CYCLES.md](PLANAR_CONTACT_TORQUE_CYCLES.md) gives a
   planar junction construction retaining the physical forces; it does not
   establish that every torque cycle encloses zero. Planarity of the simple
   body-pair graph must not be assumed.

## Recently completed branches

**Five inner centers.**
[FIVE_CENTER_LARGE_TURNS.md](FIVE_CENTER_LARGE_TURNS.md) proves
`sum |c_i|^2>=4` for five disjoint unit squares centered in the closed unit
disk, with equality only for the aligned plus. The strict inequality for
non-plus configurations and [INNER_ARC_MOMENT.md](INNER_ARC_MOMENT.md) exclude
five inner centers in a ten-packing at squared radius at most `9/2`.
[FIVE_CENTER_MOMENT_REDUCTIONS.md](FIVE_CENTER_MOMENT_REDUCTIONS.md) handles
nonextreme centers and derives the weighted separator dual.
[FIVE_CENTER_SMALL_TURNS.md](FIVE_CENTER_SMALL_TURNS.md) closes all normal
turns at most `pi/2` using three certificates. For larger turns,
[the complete appendix](FIVE_CENTER_LARGE_TURNS_TABLE.md) prints 78 cells,
42 covering trees, and 1,193 rational vertex bounds. Concavity and explicit
rational Taylor enclosures prove the bound. The companion checker verifies
the printed finite argument, including both singleton cross-references.
The older [radial-weight exclusion](RADIAL_WEIGHT_EXCLUSION.md) is retained
as a separate computer-assisted result.

**All positive tree components.**
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) pins the original
physical stress certificate and bridge reductions to n=9 research.
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md) classifies the full
positive-tree branch through `9/2`, including a five-body family near
squared radius `4.35748`. Its completion is excluded by
[KAPPA_CORE_COMPLETION.md](KAPPA_CORE_COMPLETION.md), uniformly in the slide
parameter. [STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md)
closes every S-S chain: the barrier and
[three-point theorem](WIDE_NECK_THREE_POINT_STABBING.md) give three additional
squares per half-plane, and the slide sign lets the
[two-point theorem](ONE_NECK_STABBING.md) reduce one group to two.
If a slide is zero, both groups have capacity two. The stronger upper-triple
rigidity conjecture remains optional and open.

Together with [origin-vertex bounds](THREE_ORIGIN_VERTEX_SQUARES.md) and
[one-origin bounds](ONE_ORIGIN_VERTEX_THREE_TERMINALS.md), these results
exclude every nonzero positive tree component. Every nonzero minimizing
stress component must contain a cycle. The lower radius window is imported
explicitly from n=8 at main commit `cd9127ff04e089909cc460d817ea28c4b1eb9ea9`;
its stated arithmetic dependency is recorded in the inventory. This is
not a new local Lean build or a fresh table-free derivation of that window.

**Sharper caps and physical cores.**
[SHARP_TWO_SQUARE_CAP.md](SHARP_TWO_SQUARE_CAP.md) proves that the cap
beginning at `sqrt(7/2)-1` admits only one possible pair of unit squares;
any stricter cap admits at most one. It strengthens the rational
[7/8 cap lemma](SEVEN_EIGHTHS_CAP_STABBING.md). The general block and
symmetric two-row theorems above supersede their earlier narrower cases.

## Shortcuts already ruled out

- At most five squares meeting `B(0,1/2)` is false:
  [SIX_CENTRAL_SQUARES.md](SIX_CENTRAL_SQUARES.md) gives an exact six-square
  counterexample. Distinguish intersection with a disk from a center in it.
- Four inner centers need not stay away from zero. Parallel centers
  `(-.01,-.14),(.99,-.14),(-.5,.86),(.5,.86)` are disjoint, all below unit
  norm, and the first below `.15`.
- Three inner centers need not surround zero. Parallel squares centered
  at `(+- .805,.01)` and a `pi/4` square at `(0,.92)` are disjoint with all
  center norms below one.
- Five centers strictly inside the unit disk are possible. A regular
  pentagonal arrangement of radial-diagonal squares supplies examples;
  center counting alone cannot replace the moment argument.
- The [diagonally translated block example](DIAGONAL_BLOCK_CENTER_RELAXATION.md)
  defeats a center-clearance-only capacity proof. The completed block
  theorem uses the full square geometry.
- A positive-stress seven-square ring need not have hole area below three.
  The regular radial-side ring is a counterexample; its exclusion uses
  circumradius. A radial first-entry integral can underestimate a hole
  that is not star-shaped and cannot replace its full boundary area.
- A radial square centered at `(u,0)`, `u<1`, can touch the anchors at
  `(1,+-1)` along horizontal edges. Use the complete anchored classification,
  not a claim of strict overlap at those contacts.

## Validation and trust boundary

The hand manuscripts have received separate mathematical review; this is
not formal verification. The finite-table moment proof, all tree capacity
bounds, general block and symmetric two-row theorems, loaded-ring results,
and mixed-cycle reductions have received independent review.

These standard-library checks passed during the work:

```sh
python3 research/ten/check_construction.py --self-test
python3 research/ten/check_core_obstruction.py
python3 research/ten/check_five_center_large_turns.py
python3 research/ten/check_radial_weight_exclusion.py
python3 research/ten/check_radial_count_localization.py
```

The construction check verifies 40 vertices, all 45 pairs, and three rejection
self-tests. The core-obstruction check uses exact rational arithmetic. The
large-turn moment checker verifies 78 cases, 1,193 vertices, 42 covering
roots, and two singleton leaves, with uniform lower bound
`200007133/50000000>4`. A separate rational evaluator independently checked
all its vertex inequalities. These are checks of the printed finite proof.

The older five-center radial certificate checks 1,954 parameter boxes. The
four radial-count cases check respectively 297,949, 126,591, 23,645, and
607,068 boxes. Those two radial certificates are computer-assisted proofs
with integer area bounds; they are not silently substituted for hand
arguments. No n=10 Lean compilation or kernel verification is claimed.

Keep the unrestricted lower bound and equality obligations visibly open
until every remaining physical case is covered.
