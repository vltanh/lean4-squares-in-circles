# Shared physical capacity closes three complete original cells

November 3, 2026. The same exhaustive 231-cell cover of `001/00` now has
**171 CLOSED / 60 OPEN**, up from 168/63. The three new exclusions use
one finite, acyclic whole-parent bound induction and introduce **zero
new case splits**. They preserve every original ID and ancestor path.
The separate whole-mask ledger remains **8 CLOSED / 24 OPEN**.

The current mask, its reversal `100/00`, A.2, the unrestricted lower
bound, equality classification and final manuscript remain OPEN.
No Lean compilation, Lake or CI was run. Independent arithmetic and
source review are not human or proof-kernel verification.

## 1. Original caller and exact scope

The caller is exactly `D_001/00^lt` in the
[coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md): nine physical
unit squares, all 36 corner constraints, all 36 physical pair constraints,
the five original center-cone comparisons, actual AB/BC/EF/FG, and the
strictly weak CD bit, for every squared radius `q < 1105/256`.

The previously accepted low-gap theorem excludes
`|y_D-y_C| <= 2/3`. The existing common reflection and ordering of the
two extras normalize the complement to `y_D-y_C > 2/3` and `x_H <= x_I`.
The certified cover of that normalized complement has the same 231
original closed paths. No new hypothesis is added to the caller.

| Newly closed original ID | Inherited coordinate deductions | New deductions | New rounds | Final rows |
|---|---:|---:|---:|---:|
| `positive-033850931bb6d4ef` | 76 | 575 | 3 | 7 |
| `positive-3cd9c2a7981effa2` | 76 | 580 | 3 | 7 |
| `positive-b696531e6d132c9e` | 33 | 196 | 2 | 2 |
| **Total** | **185** | **1,351** | | **16** |

All three were OPEN in the immutable pre-continuation register. Each
certificate excludes its complete original parent directly. There are
no newly introduced child domains or unresolved complements inside a
claimed closure. The [current register](gates/A2_00100_FIXED_FRONTIER.json)
and [delivery manifest](computer_assisted/a2_00100_shared_capacity_manifest.json)
bind the exact paths, sources, certificates and reports.

## 2. The shared geometric inputs

### Entire inset separation, without choosing an alternative

For any pair of original squares, put `x=x_j-x_i`, `y=y_j-y_i` and
`g=g_i+g_j`, where each `g_i` is the halfwidth of the centered aligned
inset of that same original square. Nonoverlap implies
`max(|x|,|y|) >= g`. Hence for every rational `-1 <= t <= 1`,

    x^2+y^2-2txy >= (1-t^2)g^2.

If `|x|>=g`, subtracting the right side gives
`(y-tx)^2+(1-t^2)(x^2-g^2)>=0`; the other case is symmetric.
Thus the inequality keeps all signed inset alternatives and their
contact faces. Secants on previously proved difference intervals and
the tangent `g^2>=2cg-c^2` give exact affine necessary rows.

The [complete hand proof](INSET_SEPARATION_QUADRATIC_FAMILY_HAND_PROOF.md)
also proves that the *entire* rational family is equivalent to inset
separation. A finite table is only a necessary relaxation. Its
[independent review](INSET_SEPARATION_QUADRATIC_AFFINE_INDEPENDENT_REVIEW.md)
checks the affine signs and physical variables. The complementary
diamond family described in that hand proof is not used in these
three v1 certificates.

### Three physical originals in a narrow strip

For any three independently oriented unit squares with pairwise disjoint
open interiors, suppose the original centers satisfy

    y_L <= y_M <= y_U,
    max(x_L,x_M,x_U)-min(x_L,x_M,x_U) <= W <= 7/10.

Writing `V=y_U-y_L` and `Delta=x_U-x_L`, the
[shared capacity theorem](THREE_ORIGINAL_NARROW_STRIP_CAPACITY_HAND_PROOF.md)
proves

    V + (5/14)Delta^2 >= min(2,208/75-(29/15)W).

The proof keeps the middle physical square and the endpoint originals'
incircles. A rounded-square slice argument, seven positive rational
Bernstein coefficients, and derived projection guards cover every
middle orientation. A certified interval `Delta in [l,u]` gives the
affine consequence obtained by replacing `Delta^2` with
`(l+u)Delta-lu`. Axis interchange and reflection preserve the theorem.
The [independent hand review](THREE_ORIGINAL_NARROW_STRIP_INDEPENDENT_REVIEW.md)
checks all geometry and boundary cases; its scalar companion passes
17 exact rational checks.

These are reusable physical consequences, not new mask predicates.
Each application below derives its entire order and strip guard from
the unchanged original parent. The third square matters even though
the resulting row contains only the two endpoint coordinates.

## 3. A finite induction, with every bound proved before use

Each proof starts from its independently replayed historical coordinate
prefix and the original path. In one round, the verifier reconstructs
the accepted physical rows on the old state, intersects only already
proved frame and difference intervals, and builds the new inset and
guarded capacity rows from that state.

An optimizer proposes nonnegative rational multipliers. The proof is
the printed rational sum: every coefficient residual is paid using a
proved absolute variable bound, and each proposed upper bound is
rounded outward. Every deduction in a round uses the **same old row
matrix**. The improved bounds are then installed simultaneously.
The original unit-frame identities justify the slope inversions before
the next round. Thus no bound supports its own premises.

The independent replayer reconstructs the new row formulas, all guard
intervals, exact sums, residual payments, frame inversions and state
updates. It imports neither the numerical discovery producer nor the
new row generators. The accepted frozen v14 physical row collector
and its analytic dependencies remain explicitly bound inputs.

## 4. The first two cells share one exact seven-row contradiction

For both `positive-033850931bb6d4ef` and
`positive-3cd9c2a7981effa2`, the induction proves horizontal order
`x_A < x_H < x_I` and vertical center width

    W = 401055/1048576 < 2/5

for the same original A, H and I. The capacity theorem therefore has
right side 2. Its affine row combines with the original CD cone,
the C/I center-distance secant, the inward-row predecessor budget and
three proved coordinate differences.

The [complete seven-row hand table](SHARED_CAPACITY_SEVEN_ROW_HAND_TABLE.md)
prints a positive rational combination whose eight coordinate
coefficients cancel **exactly**. Its weighted right side is

    -2315620317940810579/12533921283739484160 < 0.

Consequently the necessary rows imply `0 < 0`. The independently
replayed numerical-discovery weights provide an alternative final
certificate with paid-residual reserve

    8929382507225583434487/1511157274518286468382720 > 0.

The short exact dependence simplifies the final hand table; it does
not replace the complete original-parent induction proving its rows.

These two originals are the only previously OPEN fixed descendants of
the common early path

    angle(D, positive)
    angle_cut(A, 0, nonpositive)
    inward_row_escape(H,I), child 9.

The fixed register contains 14 descendants of that path: 12 already
closed and these two newly closed. The accepted baseline forest covers
all other terminal siblings. Thus the entire indicated early A branch
is now closed, including its shared faces. This is a consequence of
the existing cover, not a newly invented external progress unit.

## 5. The third cell has a two-line terminal proof

For `positive-b696531e6d132c9e`, the complete induction proves

    x_F = x_I = x_H,       y_F <= y_I <= y_H,
    y_H-y_F <= 228339/131072.

The three-square theorem at width zero gives `y_H-y_F >= 2`.
Equivalently, each consecutive pair's original incircles gives a
vertical gap at least one; adding the two inequalities gives the same
lower bound. Since

    2-228339/131072 = 33805/131072 > 0,

the entire original parent is impossible. The stored final certificate
uses one-half of each of the two opposite rows, so its exact reserve
is `33805/262144`, with all coefficients zero.

## 6. Independent acceptance and reproducibility

Each complete parent has an independent physical/state replay. The
first two also have separate fixed-parent reviews by different agents;
the root freshly extracted their frozen portable archive and reran
every deduction. A separate standard-library arithmetic reader,
without any geometry or producer imports, checked all printed sums.
Five semantic damaged controls were rejected: changed original path,
unproved installed bound, understated strip width, altered frame
inference and altered final multiplier.

The delivery manifest identifies the portable evidence and exact
commands. The portable complete-parent verifier needs only Python's
standard library. The archived discovery sources are byte-bound
evidence; the verifier does not execute them. All ancestor identities,
contact cases, tied endpoints and closed predecessor complements are
retained. The scope remains the original strict-radius caller, including
its strict CD bit. A positive terminal reserve does not by itself remove
those hypotheses or settle the whole mask's closed-Q boundary.

## 7. Exact accounting and remaining work

| Fixed early family | OPEN before | Newly closed | OPEN after |
|---|---:|---:|---:|
| A: positive D, nonpositive A, inward-row escapes | 17 | 3 | 14 |
| B: negative D, nonpositive A, F-height branches | 30 | 0 | 30 |
| C: negative D, nonnegative A, alternative-chain escapes | 10 | 0 | 10 |
| D: positive D, nonnegative A, alternative-chain escapes | 6 | 0 | 6 |
| **Total** | **63** | **3** | **60** |

The cumulative addition beyond the first 53 original-cell proofs is
118; `53+118=171`. No original ID or path is changed. Every unfinished
attempt remains attached to its original OPEN parent.

The frozen v1 method was tested on **all 63 initially OPEN originals**,
with at most three new simultaneous bound rounds per original and no
new splits. It produced exactly the three complete proofs above; its
other 60 trials remain OPEN. The
[complete pass summary](computer_assisted/shared_capacity_initial_63_pass_summary.json)
records every original ID and trial hash. Those OPEN trials are numerical
discovery records, not physical configurations or exclusion certificates.

There is no new whole-mask closure, positional-root exclusion or
roadmap-gate closure. The historical positional count remains 5,838
closed-Q exclusions and 2,077 OPEN among 7,915 stable IDs, with equality
root 7820 retained. All 15 roadmap IDs are unchanged. Completion still
requires the entire remaining original domain, followed by the other
fixed masks or a valid global theorem subsuming them.
