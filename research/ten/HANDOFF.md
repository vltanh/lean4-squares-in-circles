# n=10 research handoff — 2026-10-23

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
   alone excludes six outer squares. A proposed route is to bound the number
   of disjoint `pi/4` arcs that fit in the complement of the four core traces
   on the test circle; this bound is **unproved**.
3. **Five inner centers, for a wholly hand proof.** The computer-assisted
   [radial-weight exclusion](RADIAL_WEIGHT_EXCLUSION.md) already excludes this
   case. An analytic replacement would follow from the proposed inequality
   `sum |c_i|^2>=4`, using [INNER_ARC_MOMENT.md](INNER_ARC_MOMENT.md).
   [FIVE_CENTER_MOMENT_REDUCTIONS.md](FIVE_CENTER_MOMENT_REDUCTIONS.md) proves
   that a nonextreme center forces the aligned plus configuration. Otherwise
   all five centers form a strict convex pentagon; independent outward radial
   translations preserve disjointness. The moment inequality in that remaining
   case is **unproved**. Summing adjacent separating-normal inequalities is
   a possible approach; elementary Cauchy bounds tried so far are too weak.
4. **Staggered contact chain.** The precise arbitrary-orientation upper-triple
   lemma in [STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md) is
   open. Its parallel and common-maximal-chord cases are proved. Any non-T
   counterexample must have at least two second-lowest vertices at height
   at least `1/2`. The straight chain has total capacity at most eight; all
   four parameter corners have capacity at most nine. Universal two-point
   stabbing cannot prove the general lemma: exact obstructions are recorded.
5. **Contact-stress route.** [PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md)
   gives conditional graph reductions. [THREE_ORIGIN_VERTEX_SQUARES.md](THREE_ORIGIN_VERTEX_SQUARES.md)
   closes two specified physical tree families at squared radius `17/4`.
   There is no exhaustive classification of a ten-square minimizer here.
   In particular, do not extend the n=9 tree inventory's smaller radius
   window to `9/2` without redoing its inequalities. Exploration found a
   possible extra five-body tree family near squared radius `4.35748`,
   described by `B+2sqrt(A-1)=1`, where
   `A=sqrt(q-1/4)-1` and `B=sqrt(q)-sqrt(2)`. Its classification and physical
   completions were not completed or audited; it is an open lead only.

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
