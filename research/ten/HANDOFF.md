# n=10 research handoff — updated 2026-10-30

PR: <https://github.com/vltanh/lean4-squares-in-circles/pull/12>  
Branch: `research/ten-exact-start`  
Original base: `4bea747b3efa13c869b956cb28435efaf21526fa`

**The unrestricted n=10 lower bound remains open.** The target is squared
radius `Q=9/2`, for arbitrary independently oriented unit squares with
disjoint open interiors. No n=10 Lean theorem, build, or kernel check is
claimed. This PR changes only research artifacts under `research/ten/`.

## Start here

<!-- CASE_PROGRESS_START -->
**Fixed strict-lower-bound master ledger:** `███████████████████▌░░░░` **273/336 closed; 63 open.** (273 hand; 0 computer-only.) [All stable IDs and the exact remaining obligations](MASTER_CASES.md).

The denominator is frozen: 19 other terminal families + 38 branching families + 279 cycle signatures. A branching family includes every permitted graph and continuous realization for its fixed `(k,b)`. These are proof-family counts, **not a percentage of effort or of the full n=10 deliverable**. Equality and Lean verification have separate gates.
<!-- CASE_PROGRESS_END -->

[CASE_ROADMAP.md](CASE_ROADMAP.md) gives the ordered coverage tree and separate gates.
[CYCLE_CASES.md](CYCLE_CASES.md) gives the 279 cycle signatures.

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

## Final handoff checkpoint — 2026-10-30

Work is paused at the user's request. The unrestricted proof is still open.
The fixed master denominator is **336**, with **273 reviewed hand closures
and 63 open families**. No additional master ID should be created for a
research refinement. The latest main research checkpoints are
`e67bbc1fbcbfba829bb1c9044c15b4486ef683fb` (frozen master and universal patch
reductions) and `c7b306f86b82162a6b2865108a22c634a76e43f7` (shared capacity,
SS reductions, numerical research and exact obstruction examples). This
handoff commit preserves the final D-endpoint result and next obligations.

| All open IDs, grouped for shared arguments | Count | Next common obligation |
| --- | ---: | --- |
| C05 branching families | 30 | Use force/torque or completion geometry on regions with at least three terminals. Exposure and topology alone are insufficient. |
| C20 with SS | 5 | A uniform barrier/capacity theorem for arbitrary loaded SS endpoints and transmitter slides; include extra endpoint forces where possible. |
| C20 with D but no SS | 14 | Combine the new D-endpoint direction theorem with exhaustive endpoint support/circle signs and a uniform completion bound. |
| C20 with only single S paths | 14 | Stress-dependent loaded-run restrictions or uniform completion bounds; geometric angular estimates alone do not yet suffice. |

For branching, the reviewed minimum-active-body class has a simple
suppressed skeleton, every unloaded retained vertex has at least three
distinct retained neighbors, and every connected unloaded two-terminal
region is S, D, or SS. This is an existence normalization over packing and
stress pairs. It does not exclude every original realization or preserve
its raw case ID. The original unused generic-selection polynomials have
not all been proved compatible with the motions; use only the explicitly
preserved positive-normal, four-junction, loading and planar properties
until that additional compatibility is established.

The [D-endpoint restriction](DIAGONAL_ENDPOINT_NONEMPTY_PATH_DIRECTION.md),
which passed root and independent full reviews at handoff, forbids an outward second path of any width W>=1 at a degree-two loaded D
endpoint. Its single-S corollary retains only inner-corner or opposite
horizontal-side support, including radial circle-load splits. Direct
neighbors (W=0) are outside its scope. The whole LSLSLD signature remains
open and has a reproducible numerical six-body positive-stress candidate;
no internal-component impossibility should be inferred from the new lemma.

The [focused D completion handoff](SHARED_DIAGONAL_COMPLETION_HANDOFF.md)
preserves an explicitly unreviewed opposite-unique-circle argument. It is
not promoted to a theorem or used to close any ledger entry; radial
geometric circle ties remain outside that draft argument.

For LSLSLSS, the remaining central forms are U-EE, U-VE-N, U-VV-A, U-VV-O,
and radial R-VV with mixed or two-vertex SS endpoint support. U-EE requires
R²>13/3 and both source coordinates above one. U-VE-I, R-VE and radial
R-VV with E/E SS endpoints are hand excluded. The existing center-cover
certificates cover their stated center regions only. Establishing uniform
regions for every realization is still the missing step.

Validation at handoff: the master renderer and its independent audit agree
on all 336 IDs and 63 open rows; the frozen-manifest mutation check rejects
changed obligations. The cycle checker agrees by independent enumerations
on all 279 signatures. The seven-body exact checker verifies all 28 cells
(11 empty), with maximum assigned squared distance 197/200. The saved
seven-body numerical candidate JSON was reproduced identically. Published
files were compared with their remote Git blob hashes. No Lean compilation
or kernel check was run or claimed.

From this directory, regenerate/verify the research bookkeeping with:

```sh
python update_case_roadmap.py
python check_cycle_cases.py
python check_seven_body_central_hole_cover.py
```

The [reciprocal-tiling research note](RECIPROCAL_TILING_RESEARCH_HANDOFF.md)
is preserved as an unreviewed draft. It records why a convex reciprocal
tiling alone does not bound unloaded cells by k−2; further physical or
minimum-active hypotheses are needed. This note changes no status.

The old local `EXPOSED_TWO_TERMINAL_UNLOADED_PATCH.md` draft is superseded
by the published arbitrary-terminal theorem; it contains no unique pending
result. Do not restart a b=2, b=3, ... catalog sequence or a loaded-count
sequence. Use the fixed master list and aim for shared arguments.

## Current resumed checkpoint

Research resumed from handoff commit `fb91a0517a0eedf192e11759f9bdec2a60ab46af`.
The unrestricted proof is still open. The main case ledger has **19 reviewed
hand closures and 2 open
families out of 21**; the larger-cycle subledger has **246 reviewed hand
closures and 33 open cases out of 279**. Main gates remain **3/7 closed**.
The closed counts do not measure the fraction of mathematical effort.

Latest completed work:

- [Parallel patch consolidation](PARALLEL_SIDE_PATCH_CONSOLIDATION.md)
  replaces any three/four-body two-column patch or double-SS bundle by
  one SS stress path, keeping every physical square and terminal wrench.
  Combined with double-S consolidation, the stated minimum-active-body
  class has a simple skeleton and no unloaded branching region behind
  two terminals. This is a normalization, not a raw-family exclusion.
- The entire [incident U-VE-I source](INCIDENT_SIDE_SOURCE_SS_EXCLUSION.md)
  is excluded when two S paths lead to SS-separated endpoints. Arbitrary
  extra endpoint contacts are allowed, so the theorem also applies to
  branching substructures. The whole LSLSLSS signature remains open.
- [Exact obstructions](UNIVERSAL_BRANCHING_REDUCTION_OBSTRUCTIONS.md)
  show that topology and exposure alone cannot finish C05. An outerplanar
  three-sun survives the graph reductions; an explicit eight-square stress
  has exposed unloaded branches with nonparallel forces. Neither is a
  ten-square counterexample.
- The [shared completion criterion](FINITE_CENTER_COVER_CAPACITY.md) bounds
  any m-body core plus q remaining center regions by m+q squares. A reviewed
  [28-cell rational cover](SEVEN_BODY_CENTRAL_HOLE_EXCLUSION.md) gives a
  robust seven-core example, with no eighth square after an orientation
  argument. Uniform hypotheses for all realizations are still missing.
- [LSLSLSS support normalization](LSLSLSS_SUPPORT_NORMALIZATION.md) gives
  seven necessary central forms inside its existing fixed ID. R-VE is
  excluded, as is the radial R-VV subcase with E/E SS endpoint supports.
  The [U-EE source bounds](TWO_SIDE_SOURCE_WITH_SS_ENDPOINTS.md) require
  R²>13/3 and both source coordinates above one, for every slide.
- A [seven-body numerical candidate](TWO_SIDE_ONE_DOUBLE_SIDE_COMPONENT_CANDIDATE.md)
  at R²≈4.478903 has reproduced JSON, positive numerical stress and
  noncontact clearance. It is not an exact existence proof or a ten-packing.
  These results do not close a whole master entry.
- The [master ledger](MASTER_CASES.md) is frozen at 336 explicit proof families,
  with 273 hand closed and 63 open. The 30 open branching families cover all
  k and b simultaneously; the other 33 are explicit cycle signatures.
  New refinements cannot increase the denominator.
- The [three-interior-body theorem](THREE_INTERIOR_BODY_REDUCTION.md) exposes
  every center of norm at least 1/sqrt(2); at most three physical bodies
  remain inside the planar disk drawing, independently of k and b.
- The [two-terminal patch theorem](TWO_TERMINAL_UNLOADED_PATCH_REDUCTION.md)
  reduces every connected unloaded region with exactly two outside neighbors
  to one S, one D, or two to four S bodies in two columns. Its terminals
  need not be loaded or exposed in the original graph.
- [Double-S consolidation](DOUBLE_SIDE_BUNDLE_CONSOLIDATION.md) preserves
  the packing radius and all endpoint wrenches while removing one active
  transmitter. Its minimum-active-body normalization has a precisely stated
  certificate class; it does not silently extend old unused generic-polynomial
  conditions, nor close any fixed master family on its own.
- A [universal two-loaded exclusion](TWO_LOADED_COMPONENT_EXCLUSION.md)
  covers every graph and every b. A planar reciprocal-force argument
  forces all contact forces parallel; torque and the radius window give
  two S columns at squared radius 17/4, whose total capacity is at most
  nine. Remaining components have at least three loaded bodies.
- [Outer-center exposure](OUTER_CENTER_EXPOSURE_AND_WIDTH_TWO_UNIQUENESS.md)
  permits at most one distinct actual-SS or effective-width-two endpoint
  pair in the whole selected graph, independent of loaded count.
- Every whole five-cycle is hand excluded for the selected certificate.
  [C19](DIAGONAL_FIVE_CYCLE_EXCLUSION.md) uses generic contact normals
  and the reviewed nearer-endpoint obstruction.
- C20 has 246/279 hand closures. The cap budget supplies 234; the
  [SS/D](SS_DIAGONAL_SIX_CYCLE_EXCLUSION.md),
  [SS/S](SS_SIDE_SIX_CYCLE_EXCLUSION.md),
  [all-D](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md), and
  [two-D/one-S](TWO_DIAGONAL_ONE_SIDE_SIX_CYCLE_EXCLUSION.md) six-cycle
  arguments supply four more, and the
  [stronger loaded-pair angle](STRONG_DIRECT_CYCLE_BUDGET.md) adds eight.
  The 33 open IDs comprise 11 length-six,
  15 length-seven, and 7 length-eight signatures.
- C04 is [hand closed](SEVEN_RING_COMPLETE_CAPACITY.md), including every
  ownership row and radial load split. The new outer-corner theorem gives
  squared radius below 33/20; the complete enlarged-core and contact-cap
  argument places all three inner squares below 83/50, contradicting
  their exact minimum 425/256. The corner selection, cap bounds, and
  global winding argument passed root and independent reviews.
- C05's [loaded-branch catalog](BRANCHING_LOADED_SKELETON_INVENTORY.md)
  has 45,666 fixed records. [Exact graph certificates](BRANCHING_SELECTED_GRAPH_FILTERS.md)
  exclude 42,532 and leave 3,134. Independent enumerators agree on every
  record, and independent checkers validate the finite witnesses.
- C05 now also has a [one-unloaded-branch catalog](BRANCHING_ONE_UNLOADED_INVENTORY.md)
  with 524,870 fixed records. The [compact proof ledger](BRANCHING_ONE_UNLOADED_FILTERS.md)
  excludes 385,071 and leaves 139,799. Codes are stable IDs, so an
  on-demand decoder prints the case and its proof witness. Raw catalogs
  and exact remaining-case lists can be regenerated without committing
  hundreds of thousands of rows.
- The entire [two-loaded, one-unloaded-branch stratum](ONE_UNLOADED_TWO_LOADED_EXCLUSION.md)
  is hand excluded. A forced five-square core has squared radius 17/4;
  a sealed-cavity and two-half-plane capacity argument bounds its total
  completion by nine squares, with arbitrary additional orientations.
- [Planar stress selection](PLANAR_SELECTED_PHYSICAL_STRESS.md) is
  compatible with the normal restrictions used above. Select the new
  certificate before classifying its graph; an arbitrary earlier stress
  graph need not retain its edges, degrees, or components.

| Open family | Concrete next work |
| --- | --- |
| C05: branching mixed components | Close the 30 fixed open branching families in MASTER_CASES.md using structural or completion arguments across k and b. |
| C20: 33 larger-cycle entries | Prove completion bounds or contact exclusions for the explicit remaining signatures in CYCLE_CASES.md. |

The fixed open branching range is `3<=k<=7`, `0<=b<=10-k`: exactly
30 families, including every larger b without extending the denominator. Work is focused on structural arguments
covering all these pairs, rather than adding larger catalogs. The
[two-neighbor branch theorem](TWO_NEIGHBOR_UNLOADED_BRANCH_RESTRICTIONS.md)
is such a universal restriction: at most one unloaded retained vertex
has only two distinct retained neighbors. It is not a closure of C05. There is no plan to handle successive loaded
counts as separate catalogs; the priority is one structural or completion
argument for the remaining mixed family.

The open `LSLSLD` signature now has a
[reproducible numerical six-body candidate](ONE_DIAGONAL_TWO_SIDE_COMPONENT_CANDIDATE.md)
at radius about 2.03253, with positive stress and numerical clearance.
It is neither a certified exact component nor a ten-square packing. It
suggests that this branch needs a bound on the four additional squares,
and it changes no progress count.

The former D-D crossing lead is now a reviewed theorem. A crossing
forces a lower loaded square's other contact to the opposite end of its
top side; its neighbor is then a fixed northwest unit square with a vertex
outside the containing circle by squared-radius excess `2(1+v)>0`.
This proof uses degree two at the loaded endpoint and must not be applied
to branching components without that hypothesis.

The [ownership alphabet](SEVEN_RING_OWNERSHIP_ALPHABET.md) now has two
full integrated reviews, including its radial-side tables, coarse schemes,
and strict side-endpoint reduction for pure chirality. It gives 25 local
candidates; the complete capacity theorem now excludes all seven-ring
ownership families, including U4/U5 and every pair-support type. The
[branching skeleton](BRANCHING_COMPONENT_SKELETON_DRAFT.md) also passed two
full mathematical reviews of its suppression, degree, bundle, and effective
contact reductions. Both remain necessary classifications, not global
exclusion theorems.
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
[final S-S closure](SIDE_SIDE_EXCLUSION.md) close that component type. The
four-loaded diagonal five-cycle is also now excluded for the generic
selected certificate by [its nearer endpoint](DIAGONAL_FIVE_CYCLE_EXCLUSION.md).
The earlier [inner trace restriction](DIAGONAL_FIVE_CYCLE_INNER_TRACE.md)
remains one input to that proof.

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
   loaded graphs. Components with branching cyclic blocks and the remaining
   larger mixed cycles remain open. The four-loaded five-cycle is excluded
   by the [side theorem](MIXED_FIVE_FOUR_LOADED.md) and the
   [selected-certificate diagonal theorem](DIAGONAL_FIVE_CYCLE_EXCLUSION.md). For a whole
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
   [MIXED_FIVE_CYCLE_STATUS.md](MIXED_FIVE_CYCLE_STATUS.md) indexes these
   completed five-cycle branches.
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
