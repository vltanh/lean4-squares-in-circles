# n=10 research handoff — updated 2026-10-25

PR: <https://github.com/vltanh/lean4-squares-in-circles/pull/12>  
Branch: `research/ten-exact-start`  
Base inspected: `4bea747b3efa13c869b956cb28435efaf21526fa`

**The unrestricted n=10 lower bound is still open in this work.** The target
is squared radius `Q=9/2`, for arbitrary independently oriented unit squares
with disjoint open interiors. No n=10 Lean theorem, build, or kernel check is
claimed. All changes in this PR are research artifacts under `research/ten/`.

## Start here

[README.md](README.md) indexes the completed arguments and their hypotheses.
[UNRESTRICTED_MODEL.md](UNRESTRICTED_MODEL.md) states the physical model and
the exact finite formulation. The exact construction at `Q` is checked by
[check_construction.py](check_construction.py); it is an upper bound.

The strongest completed sharp hand theorem covers every packing whose pairs
are separated along one common orthogonal coordinate frame, even with
independent square orientations. See [COORDINATE_RECTIFICATION.md](COORDINATE_RECTIFICATION.md)
and [ALL_PARALLEL_THEOREM.md](ALL_PARALLEL_THEOREM.md). A physical packing need
not have that extra separation property.

The strongest unrestricted hand reduction is
[CENTER_RADIUS_REDUCTION.md](CENTER_RADIUS_REDUCTION.md): eight centers
outside the open unit disk force the four boundary anchors and the complete
attaining family. Thus a hypothetical smaller ten-square packing has exactly
three, four, or five centers in the open unit disk. The equality classification
is also open outside the completed cases.

## Remaining obligations and useful next steps

1. **Three inner centers.** Seven outer squares consume at least `7pi/4` on
   the test circle of radius `sqrt(1+1/sqrt(2))`. The remaining interaction
   with the three inner squares is not closed. The hand stability theorem in
   [THREE_CORE_INNER_STABILITY.md](THREE_CORE_INNER_STABILITY.md) requires all
   three squares to lie wholly inside that test circle; this hypothesis must
   not be inferred merely from their center norms. Pure radial additive
   weights did not close this case in numerical exploration.
2. **Four inner centers.** Six outer arcs have length at least `pi/4` each.
   [FOUR_CENTER_WIDTH.md](FOUR_CENTER_WIDTH.md) proves that the four core
   squares' hull has width at least two in every direction. The separate
   computational [radial localization](RADIAL_COUNT_LOCALIZATION.md) forces
   two center norms at most `.65` and two strictly above `.9`. Neither result
   alone excludes six outer squares. Abstract complementary-gap capacity
   does not close the problem, even with radial localization: see the exact
   counterexamples in [FOUR_CORE_GAP_OBSTRUCTION.md](FOUR_CORE_GAP_OBSTRUCTION.md)
   and [LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md](LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md).
   [TRANSLATED_BLOCK_OBSTRUCTION.md](TRANSLATED_BLOCK_OBSTRUCTION.md) closes
   the exact aligned two-by-two block class translated along a side direction.
   Also [LARGE_INNER_ARC.md](LARGE_INNER_ARC.md) proves by hand that at least
   two of four inner centers have norm strictly less than `.9`, and at most
   one of three inner centers has norm at least `.9`.
   [LOCALIZED_BLOCK_OBSTRUCTION.md](LOCALIZED_BLOCK_OBSTRUCTION.md) closes
   any solid two-by-two core satisfying the two-large-center hypothesis;
   applying that hypothesis still uses the computational certificate.
3. **Five inner centers, for a wholly hand proof.** The computer-assisted
   [radial-weight exclusion](RADIAL_WEIGHT_EXCLUSION.md) already excludes this
   case. An analytic replacement would follow from the proposed inequality
   `sum |c_i|^2>=4`, using [INNER_ARC_MOMENT.md](INNER_ARC_MOMENT.md).
   [FIVE_CENTER_MOMENT_REDUCTIONS.md](FIVE_CENTER_MOMENT_REDUCTIONS.md) proves
   that a nonextreme center forces the aligned plus configuration. Otherwise
   all five centers form a strict convex pentagon; independent outward radial
   translations preserve disjointness. The moment inequality in that remaining
   case is **unproved**. A weighted dual from the neighboring separators is
   now derived explicitly in the reductions note.
   [FIVE_CENTER_SMALL_TURNS.md](FIVE_CENTER_SMALL_TURNS.md) proves the strict
   moment bound by three rational certificates when all five normal turns
   are at most `pi/2`. Fans with larger turns remain open.
4. **Staggered contact chain: CLOSED by hand.**
   [STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md) now proves
   total capacity at most nine for all slide parameters. The barrier and
   [three-point theorem](WIDE_NECK_THREE_POINT_STABBING.md) bound each
   half-plane group by three; the sign of either slide parameter lets the
   [two-point theorem](ONE_NECK_STABBING.md) bound one group by two.
   If either slide parameter is zero, the total capacity is at most eight.
   The stronger upper-triple rigidity conjecture remains open but is no
   longer an obligation for excluding this chain.
5. **Contact-stress route.** [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md)
   gives conditional graph reductions. [THREE_ORIGIN_VERTEX_SQUARES.md](THREE_ORIGIN_VERTEX_SQUARES.md)
   closes two specified physical tree families at squared radius `17/4`.
   [ONE_ORIGIN_VERTEX_THREE_TERMINALS.md](ONE_ORIGIN_VERTEX_THREE_TERMINALS.md)
   also closes the side-plus-vertex family with at least three radial side
   terminals. Its two-terminal boundary is covered by the completed chain
   theorem. [EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md) now
   classifies the full positive-tree branch through `9/2`, including a real
   extra five-body family near squared radius `4.35748`.
   [KAPPA_CORE_COMPLETION.md](KAPPA_CORE_COMPLETION.md) proves total capacity
   at most nine for every parameter of that family. Thus every nonzero
   minimizing stress component must contain a cycle. The lower radius
   window is explicitly imported from n=8 at main commit
   `cd9127ff04e089909cc460d817ea28c4b1eb9ea9`; no new local Lean build is
   claimed. Cyclic components, possible bridges attached to them, and all
   their unstressed-square completions remain open. Planarity of the simple
   body-pair graph is not assumed.

## Shortcuts already ruled out

- Bounding the number of squares meeting `B(0,1/2)` by five is false:
  [SIX_CENTRAL_SQUARES.md](SIX_CENTRAL_SQUARES.md) gives an exact six-square
  counterexample. Distinguish intersection with a small disk from a center
  lying in it.
- Four inner centers need not stay away from the origin. Parallel squares at
  centers `(-.01,-.14),(.99,-.14),(-.5,.86),(.5,.86)` are disjoint, all four
  norms are strictly below one, and the first norm is below `.15`.
- Three inner centers need not surround zero. The parallel squares centered
  at `(+- .805,.01)` and the `pi/4` square centered at `(0,.92)` are disjoint
  and have center norms below one.
- Five centers strictly inside the unit disk are possible. A regular
  pentagonal arrangement of radial-diagonal squares supplies examples;
  center counting alone cannot replace the five-center moment argument.
- A radial square centered at `(u,0)` with `u<1` may touch the anchors at
  `(1,+-1)` along their horizontal edges. An anchor-based contradiction must
  use the complete ten-square anchored classification, not a claimed strict
  overlap there.

## Validation and trust boundary

The hand manuscripts were separately reviewed during the session; this is
mathematical review, not formal verification. The latest hand checkpoint adds
the four-center width theorem, five-center reductions, both origin-vertex
capacity bounds, and the common-slice and parameter subcases of the chain.

The following standard-library checks passed during the session:

```sh
python3 research/ten/check_construction.py --self-test
python3 research/ten/check_core_obstruction.py
python3 research/ten/check_radial_weight_exclusion.py
python3 research/ten/check_radial_count_localization.py
```

The construction check verifies 40 vertices, all 45 pairs, and three negative
self-tests. The core-obstruction check is exact rational arithmetic. The
five-center radial certificate certifies 1,954 parameter boxes. The four
radial-count cases certify respectively 297,949, 126,591, 23,645, and 607,068
boxes. The last two checks are computer-assisted proofs with integer area
bounds, not hand replacements or Lean proofs.

Keep the unrestricted lower bound and equality obligations visibly open until
an argument covers every remaining case in the stated physical model.
