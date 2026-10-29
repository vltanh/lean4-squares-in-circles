# n=10 research handoff — updated 2026-10-29

PR: <https://github.com/vltanh/lean4-squares-in-circles/pull/12>  
Branch: `research/ten-exact-start`  
Original base: `4bea747b3efa13c869b956cb28435efaf21526fa`

**The unrestricted n=10 lower bound remains open.** The target is squared
radius `Q=9/2`, for arbitrary independently oriented unit squares with
disjoint open interiors. No n=10 Lean theorem, build, or kernel check is
claimed. This PR changes only research artifacts under `research/ten/`.

## Start here

[CASE_ROADMAP.md](CASE_ROADMAP.md) is the current finite case tree and gated
progress ledger: **17 hand-closed, 0 computer-only, and 4 open families**.
[CYCLE_CASES.md](CYCLE_CASES.md) enumerates all 279 larger mixed-cycle cases;
Its generated progress bar and proof links record every reviewed exclusion.
The bars count these fixed families, not the fraction of proof effort.

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

## Current resumed checkpoint

Research resumed from handoff commit `fb91a0517a0eedf192e11759f9bdec2a60ab46af`.
The unrestricted proof is still open. The main case ledger has **17 reviewed
hand closures and 4 open
families out of 21**; the larger-cycle subledger has **118 reviewed hand
closures and 161 open cases out of 279**. Main gates remain **3/7 closed**.
The closed counts do not measure the fraction of mathematical effort.

Latest completed work:

- C03: a hand cap proof excludes every physical ring in the fixed
  one-chirality ownership pattern, independently of the earlier interval
  action verifier.
- C15, C16 and C17: the unique-circle S-S, S-D and D-S five-cycles are
  excluded. The saved S-S candidate passed both integrated reviews;
  [SIDE_SIDE_EXCLUSION.md](SIDE_SIDE_EXCLUSION.md) is the complete proof.
  Every three-loaded five-cycle is now excluded.
- C20: [single-side uncrossing](SINGLE_SIDE_TRANSMISSION_UNCROSSING.md)
  proves radial loaded order whenever at most one D transmitter occurs.
  Its [117-case selection](single_side_cycle_batch.json) overlaps 27 earlier
  exclusions and adds 90; the separate seven-loaded D-D case makes 118.
- C19: the diagonal transmitter is wholly within squared radius `3/2` and
  occupies more than `5pi/6` on the radius-`3/8` circle. At most one other
  square can be wholly inside the test disk. This is a restriction only.

| Open family | Concrete next work |
| --- | --- |
| C04: other seven-ring ownership | Audit the 25-candidate ownership alphabet and its 34 coarse proper-contact schemes. Combine the reviewed side-support and opposite-vertex corner bounds where the spike geometry applies. Opposite-corner, radial-side, and pair-contact degeneracies still require treatment. |
| C05: branching mixed components | Audit the proposed suppressed skeleton and then enumerate or exclude its remaining graphs. Do not assume the body-pair graph is planar. |
| C19: four-loaded diagonal five-cycle | Turn its origin-containing transmitter and forced protrusions into a capacity bound, or exclude the component. |
| C20: 161 larger-cycle entries | Resolve cases with two or more D paths, and the shorter or all-S cases not excluded by the present angular budgets. Every remaining ID is explicit in CYCLE_CASES.md. |

One useful **unproved** C20 lead is now precise: a crossing between two
single-D transmission paths forces a solid block centered at `(0,v)`,
`-7/8<v<-7/10`, with two loaded lower squares and two diagonal upper
transmitters. Their other loaded endpoint contacts are `(+-1,v+1)`.
The loaded lower squares' force/torque equations might exclude this
junction, but no such exclusion has been established.

The [ownership alphabet](SEVEN_RING_OWNERSHIP_ALPHABET.md) is retained as
a **review-pending draft**. Independent review covered its first two
sections only; do not use its later classification tables as settled
premises. The [branching skeleton draft](BRANCHING_COMPONENT_SKELETON_DRAFT.md)
records the proposed seven-valued edge alphabet, degree bound, parallel
bundle restrictions, and cut constraints; its new arguments need an
independent audit before enumeration or use as premises.
The [opposite-vertex restriction](LOADED_DIAGONAL_VERTEX_RESTRICTION.md)
has two completed independent reviews: its opposite corner has squared
norm below `49/64`; the double-side bound is `53/64`. Their combination
is a local tool, not a general ring exclusion.
The former [S-S handoff candidate](SIDE_SIDE_SIDE_INTERIOR_HANDOFF.md)
has now passed full root and independent audits. Its promoted proof closes
C15; the earlier draft remains available in the handoff commit's history.
No new n=10 Lean theorem or kernel check was attempted.

## Resumed checkpoint

Work resumed from commit `9b90c5e` on 2026-10-29. Both pending two-row
extensions passed independent mathematical review; the explicit review is
recorded in [TWO_ROW_EXTENSION_AUDIT.md](TWO_ROW_EXTENSION_AUDIT.md).
No proof of the unrestricted n=10 optimum is claimed.

| Manuscript | Current status |
| --- | --- |
| [Extreme upper asymmetry](EXTREME_ASYMMETRIC_TWO_ROW.md) | Independent full mathematical review passed; removes the quarter-offset restriction for the stated touching-lower-pair core with `0<t<=5/12` |
| [Seven-angle action](SEVEN_RING_ANGLE_ACTION.md) | Independent full mathematical review passed; exact reduction; its separate global classification is now computer-assisted |
| [Wider row displacement](WIDE_DISPLACEMENT_TWO_ROW.md) | Independent full mathematical review passed; interval is `0<t<3/2-2^(-1/4)` |
| [Separated lower pair](SEPARATED_LOWER_TWO_ROW.md) | Independent full mathematical review passed; extension removes lower-pair touching under the displayed bounds |

The [combined theorem](SEPARATED_WIDE_TWO_ROW.md), independently reviewed
on 2026-10-29, permits a separated lower pair throughout the full wider
displacement interval. Its proof checks the virtual slot, center clearance,
and arc counts under both extensions at once.

Both extensions cover specified common-frame two-row cores. There is still
no argument reducing every four-inner-square core to those arrangements.

The strict one-chirality seven-ring is now excluded **by hand**. The
[chord-endpoint bound](SEVEN_RING_CAP_CHORD_BOUND.md) and
[radial cap theorem](SEVEN_RING_RADIAL_CAP_BOUND.md), both independently
reviewed, put all three inner squares in a disk of squared radius
`33/20<425/256`, below their established minimum. The independently audited
[computer-assisted angle-action theorem](SEVEN_RING_GLOBAL_ACTION.md)
remains a separate result proving uniformity in this ownership pattern;
its interval proof is no longer needed to close the hand completion case.
Other ownership patterns remain open.

The [full radial-side D-D proof](RADIAL_SIDE_DD_EXCLUSION.md) now excludes
its asymmetric smaller-radius branch too. Together with S-S and S-D, this
closes the radial-side central-body case of the three-loaded five-cycle.
The [D-S closure](DIAGONAL_SIDE_EXCLUSION.md),
[S-D closure](SIDE_DIAGONAL_EXCLUSION.md), and
[final S-S closure](SIDE_SIDE_EXCLUSION.md) close that component type. The four-loaded diagonal five-cycle remains
open, with a new [inner trace restriction](DIAGONAL_FIVE_CYCLE_INNER_TRACE.md):
at most one other square is wholly contained in the test disk.

The resumed work also proves a [parallel-core graph dichotomy and narrow-channel
filling lemma](FOUR_CORE_GENERALIZATION.md), with an exact localized pinwheel
showing why raw two-row normalization fails. The [four-loaded five-cycle
theorem](MIXED_FIVE_FOUR_LOADED.md) excludes its side transmitter throughout
the imported radius window. For loaded rings, [force ratios and physical
neighbor containment](SEVEN_RING_FORCE_RATIO.md) give new necessary bounds,
including `R cos(alpha)>1` in the one-chirality pattern. The reviewed
[spike reduction](SEVEN_RING_SPIKE_REDUCTION.md) confines protruding
inner-square vertices to explicit contact triangles cut by diameter disks.
The weaker physical cap bound now closes the one-chirality completion;
the earlier sharper target is no longer a required step for that case.

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
   touches. The broader extensions in the checkpoint table are now reviewed conditional
   theorems; the absence of a general core reduction remains the gap.
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
   radius. Other contact ownership patterns remain open. For the strict
   side/vertex one-chirality pattern, the [global action theorem](SEVEN_RING_GLOBAL_ACTION.md)
   now forces the uniform ring by an exact computer-assisted cone argument.
   The separate [hand cap theorem](SEVEN_RING_RADIAL_CAP_BOUND.md) now
   excludes the same completion pattern geometrically, so the finite cone
   lemma no longer needs a hand replacement for this case. Other ownership
   patterns still require classification or a general capacity theorem.
4. **Mixed cyclic stress components.**
   [CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md) excludes
   two-terminal components made of transmission paths and several small
   loaded graphs. Components with branching cyclic blocks, five-cycles with
   four loaded bodies and a diagonal transmitter, and larger mixed cycles
   remain open. The side-transmitter case is now excluded by the
   [four-loaded theorem](MIXED_FIVE_FOUR_LOADED.md). For a whole
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
   transmitter. The [D-S exclusion](DIAGONAL_SIDE_EXCLUSION.md) now closes
   the diagonal-then-side case. The reverse side-to-diagonal pattern is
   now closed by [SIDE_DIAGONAL_EXCLUSION.md](SIDE_DIAGONAL_EXCLUSION.md).
   When C has two geometric circle vertices,
   [RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md)
   and the [full D-D exclusion](RADIAL_SIDE_DD_EXCLUSION.md) now close that
   branch. They use the slightly sharper imported lower bound
   `R^2>5/2+sqrt(2)`, with the n=8 bracket dependency explicitly stated.
   [MIXED_FIVE_CYCLE_STATUS.md](MIXED_FIVE_CYCLE_STATUS.md) lists the remaining
   unique-circle patterns and the four-loaded diagonal cycle.
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
