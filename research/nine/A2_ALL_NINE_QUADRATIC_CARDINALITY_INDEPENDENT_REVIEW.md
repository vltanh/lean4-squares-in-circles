# Independent review of the all-nine quadratic cardinality family

November 3, 2026. **ACCEPTED in the stated necessary-row scope.**
This is an independent review by the global-mask agent. The separate
standard-library checker imports neither the producer, its existing
independent checker, a moment generator, nor a numerical solver.
It gives zero original-cell and zero mask closure credit.

## Reviewed sources and exact geometric scope

- Producer: `quadratic_global_nine_cardinality.py`, SHA-256
  `790143245268508ec74f6d7d777e1e01a87efb8715a9141450eb5e2b957593e3`.
- Hand proof: `ALL_NINE_QUADRATIC_CARDINALITY_HAND_PROOF.md`, SHA-256
  `aa3e3523af9dfb8986eca0a5ef740c5099964e76811dd6e0dbb9bd16f8b2859a`.
- Separate checker: `independent_nine_cardinality_global_review.py`.
- Literal comparison tables: `all_nine_cardinality_literal_row_tables.json`.
- Exact report: `all_nine_cardinality_global_review.json`.

The physical premise is nine actual original unit squares, with independent
orthonormal frames, pairwise disjoint open interiors, and all original corners
in the closed disk of squared radius `1105/256`. The position intervals must
already be valid on the unchanged original parent. No mask, contact,
force, common orientation, common separator, or selected near pair is assumed.

The accepted arc theorem in
`SMALLER_CENTRAL_DISKS_NINE_UNIT_CAPACITY.md` supplies at least
two distinct squares meeting the open `23/100` disk and excludes any original
containing that entire closed disk. The latter gives each center norm
strictly greater than `27/100`. The reviewed arc theorem retains the
weak-clearance endpoint and the closed containing-circle equality case.

## Radial bounds and equality endpoints

Let `q_i=x_i^2+y_i^2`. The weak row `q_i>=729/10000` follows from the strict
center exclusion. Its use of a weak inequality is a safe relaxation.

The four actual corner bounds give

`q_i+1/2+|c_i·u_i|+|c_i·v_i|<=1105/256`.

Since the last two terms sum to at least `sqrt(q_i)`, monotonicity on the
nonnegative half-line and the exact reserve

`(91/60)^2+91/60+1/2-1105/256=31/57600>0`

prove `q_i<(91/60)^2`. Intersecting this upper bound with the exact box-square
upper bound yields a valid `q_i<=M_i` for the whole parent.

If square i is near, its center is less than `23/100+1/sqrt(2)` from the
origin. Thus

`q_i<U=61473/70000`,

using the strict rational inequality `sqrt(2)<99/70`.

Consequently, a box lower bound `m_i>=U` proves non-nearness, **including
m_i=U**. The producer correctly gives that test priority. A bound `M_i<=U`
is used only to select the universal indicator upper bound one. It does
**not** assert nearness. Equality `M_i=U` never enters a denominator.

## Cardinality argument and complete finite family

For every remaining label with `M_i>U`, define

`f_i=(M_i-q_i)/(M_i-U)`.

Every denominator is positive. The bound `q_i<=M_i` gives `f_i>=0` for
every physical configuration. A near original has `q_i<U`, hence `f_i>1`.
Writing e_i for its actual near indicator, both `e_i<=f_i` and `e_i<=1`
therefore hold. The indicators are mathematical devices; they are not
introduced as independently selectable relaxation variables.

The original all-nine theorem gives `sum e_i>=2`. Exact far labels contribute
zero. Labels represented by constants contribute at most one each. If C is
the number of those constants and K the remaining radial labels, the
unconditional inequality is

`sum_(i in K) f_i >=2-C`.

When C=0, replacing any one f_j by the other valid upper bound one also gives

`sum_(i in K, i!=j) f_i >=1`.

These are every nontrivial choice within this specific upper-bound family:
any choice with at least two constants has a left side already at least two,
because all remaining f_i are nonnegative. When C=1 only the all-radial
choice for the remaining labels is nontrivial. When C>=2 the family adds
nothing. Empty selected sets correctly produce a contradictory constant row
if fewer than two labels could possibly be near.

This is completeness of the finite family of indicator upper-bound choices.
It is **not** a claim that these rows capture every geometric consequence
of central nearness, or that a feasible relaxed point determines actual near
originals.

Expanding each retained inequality gives exactly

`sum q_i/(M_i-U) <= sum M_i/(M_i-U)-required`.

The producer's signs, constants, selected labels, omission guards, and
classification order agree with this derivation.

## Polynomial and moment-index reconstruction

The new checker first reconstructs the semantic polynomial in the original
center variables: the only monomials are `x_i^2` and `y_i^2`. It then enumerates
all pairs `(a,b)`, `0<=a<=b<54`, lexicographically and assigns indices beginning
at54. This independently reproduces the shared moment convention without
using the producer's closed-form diagonal-index formula.

All coefficient lists, right sides, complete row-name lists, and audit guards
are compared exactly with the exported producer tables using rational
arithmetic. No floating-point tolerance enters this comparison.

A physical packing embeds into the lift by `Y_ab=z_a*z_b`. The new rows are
necessary for that embedding. The review does not assert that every feasible
relaxed moment table has rank one or comes from actual original squares.

## Four requested states checked

| Original | Radial rows | Cardinality rows | Total | Exact far labels | Constant-indicator labels |
|---|---:|---:|---:|---|---|
| `negative-95371f658da581d0` |18|7|25|A,D,E|none|
| `positive-a4979e5f2a7e8734` |18|6|24|A,D,E,G|none|
| `negative-0e4fa3209b6f7b12` |18|1|19|A,D,E|F|
| `negative-6ad5eef3b91c1fbd` |18|1|19|A,D,E|F|

All **87 rows pass** the separate semantic-polynomial and lifted-index
comparison. For every state, the checker also verifies that the positions
copied into the moment record equal the referenced original parent's final
positions, that the parent file has the recorded SHA-256, and that its
existing exact independent review certifies that same file hash.

The four previous bound inductions were not rerun in this check; their
existing exact reviews are bound by their certificate hashes. This review
checks the newly added family, its full physical scope, and the exact
source-position linkage.

## Acceptance boundary

The producer and hand proof are accepted as a family of necessary,
unconditional all-nine inequalities on every certified whole-parent box.
No near pair is selected, no descendant case is omitted, and all square
moments belong to the same originals.

A full original closure still requires a separately checked positive exact
contradiction for the complete moment certificate, including its other
physical rows and any weighted residual correction. This review supplies
no such terminal and changes no original, mask, or positional-root status.
The frozen global central-capacity evidence package has not been modified.
