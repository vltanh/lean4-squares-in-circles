# Whole-original Cb882 bounds in the six retained height domains

This attachment concerns only the unchanged original
`negative-b882d8ade0cf9ea0`, in mask `001/00`, at squared radius `1105/256`.
Its exact original path is

```json
[["angle",3,0],["angle_cut",[0,"0"],1],["alternate_four_escape",[1,7],[3]]]
```

## Source domain and fresh induction

The source is `d_work/CB882_whole_height_consequence_bound3/record.json`,
SHA256 `88fe0a11aed912184b29e8868fd1317e70b5c6dbd29a6107d3651d90a687e2d8`.
It has scope `WHOLE_UNCHANGED_ORIGINAL_PARENT`. Its initial state is exactly
the independently replayed original prefix with SHA256
`3faca11f2a9bebfb813ae2c13228e4685c1bcb29352773aad967390943f8daf8`.
Its final state retains the same original identifier and exact path. There
is no selected height alternative, child restriction, separating-axis
selection, proxy selection, angle child, or C887-specific D/G premise in
this source domain.

Before any consuming tree is checked, a separate standard-library process
reinvokes the older independent source checker
`verify_cb882_whole_height_consequence_bound_pass.py`, SHA256
`a3a5758ace88998a7ddfad664b77bcb134ab84414998f8967a3009b2fc2741ad`.
That checker replays the original prefix, the two already proved
whole-original height consequences, and all three bound rounds. It checks
441 interval deductions and 1,009 printed necessary-row occurrences. The
new transport checker requires its freshly returned final state to equal
the frozen state in `CB882_WHOLE_HEIGHT_BOUND_STATE_BINDING.json`.

The source checker is older than this attachment and is invoked in a fresh
process. It has no handler for the new `certified_cb882_root_bound_` prefix.
The attachment additionally checks that none of the source's printed rows
uses this prefix or either C887 union/root transport prefix. Thus the
transported bounds are established before they are consumed; there is no
dependency on the consuming tree or on its height alternative.

## The 414 affine consequences

The certified state describes shared physical quantities of the nine
original squares. It gives 18 center-coordinate intervals, 36 frame/inset
scalar intervals, nine slope intervals, both Cartesian differences for all
36 original pairs, and both diagonal differences for all 36 pairs.

An interval `l <= v <= u` gives the two affine rows `v <= u` and
`-v <= -l`. For an original slope interval `l <= beta/alpha <= u`, the
physical frame has positive `alpha`, so the two rows are
`beta - u*alpha <= 0` and `-beta + l*alpha <= 0`. For Cartesian pair
differences the affine quantity is `x_j-x_i` or `y_j-y_i`; for diagonal
differences it is `(x_j-x_i)+(y_j-y_i)` or
`(x_j-x_i)-(y_j-y_i)`. Their exact coefficients are expanded directly by
the independent literal decoder.

This yields `2*(18+36+9+2*36+2*36) = 414` inequalities. Every coefficient
uses an original variable among indices 0 through 53. No selected-owner
product, separating-axis predicate, auxiliary coordinate, or child-only
bound is transported.

## Consumer containment

The six retained Cb882 height components are 0, 1, 2, 3, 5 and 6 of the
published complete opposite-tilt eight-case cover. Each is a subset of the
same unchanged original. The existing tree checker freshly reconstructs
each component's seed, conditional height row and complete closed domain.
The new adapter additionally requires the same original identifier and
the exact original path as a prefix at every consuming physical state.
Further proxy, separating-axis and closed-angle restrictions therefore
remain subsets of the source original and may use all 414 consequences.

The caller's stored interval box need not already be contained in the
stronger final source box: the rows are proved necessary consequences for
every physical configuration of the original. Their purpose is to impose
those newly proved bounds on the caller's relaxation. Scope and path
containment establish the logical attachment.

The complete four-way proxy, eight-way separating-axis and two-way closed
angle cover checks remain unchanged. All nine physical originals, all 36
corner and pair predicates, original edge/cone constraints, strict CD,
and shared closed faces remain in scope. This attachment proves no new
original exclusion by itself and has zero original-cell and mask credit.
