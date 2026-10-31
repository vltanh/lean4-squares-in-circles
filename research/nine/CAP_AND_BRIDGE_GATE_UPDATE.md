# n=9 — cap rigidity and radial-bridge continuation

**Base read:** PR #11, branch `research/nine-tablefree-hand`, commit
`a6b37a74769908a64cef5835550f0ec04191eb98`.
**Latest source reconciliation:** `028a63b4fc963eb78d776a7f42ff3606e651e816`
adds the radial bridge/leaf reduction, credited below as an existing input.
**Delivery:** hand manuscripts imported to draft PR #11 on 2026-10-23 through the connected GitHub app. Their separate exact-regression script and JSON report remain available in the conversation's local proof package, but have **not** been committed to the repository; they are finite checks, not a universal proof. Independent full audit, Lean compilation and CI remain outstanding.

The unrestricted sharp n=9 lower bound, its full equality classification,
and the audit/formalization/integration gates remain **OPEN**. The
following named implications now have written hand derivations. They
are not independently audited or Lean-verified.

## A. New terminal mathematics without common separating axes

Source: `UNRESTRICTED_THREE_SQUARE_CAP.md`.

| Subgate | Exact implication | State |
|---|---|---|
| CAP.1 | Every unit square in `x²+y² <= Q`, `y >= 7/16` cuts a segment of length at least one from `[-3/2,3/2] × {5/4}`; every non-axis-aligned square cuts strictly more | Written hand proof |
| CAP.2 | Three physically interior-disjoint squares in that cap force q=Q, all three axis frames, and exact outer centers `(±1,15/16)` | Written hand proof, full equality |
| CAP.3 | At q<Q, in **every frame** at least five of nine squares meet the central strip `|y|<7/16`; their vertical interval order has height at most two | Written unconditional necessary condition |
| CAP.N | An exact nine-square q=Q packing has **no** three-square sharp cap in **any** direction | Exact counterexample to universal cap extraction at equality |

The only general-purpose calculus in CAP.1 is circle-boundary concavity
and one monotone cubic. All auxiliary comparisons are displayed exact
identities/inequalities. There is no interval cover or angle grid in the
proof. The regression script is not a theorem premise.

Source: `SOLID_FOUR_ROW_UNRESTRICTED_NINE.md`.

| Subgate | Exact implication | State |
|---|---|---|
| ROW.1 | For a solid contiguous four-square aligned row in q<=Q, each of the other five squares is wholly above or below it; no square can wrap around an end | Written hand proof from physical nonoverlap and corner bounds |
| ROW.2 | Every physical nine-square completion of such a row has q=Q, even with arbitrary oblique separators among the five remaining squares | Written sharp whole-class theorem |
| ROW.3 | In a seven-square seam pattern, horizontal projection separation is needed for the four-group but **not** for the three-group | Written sharp terminal theorem |

The row in ROW.1–2 is **solid**: four equal-height, aligned, edge-to-edge
squares. It is not an arbitrary staggered four-projection chain. This
restriction is explicit, not a newly assumed global normal form.

## B. Physical stress reduction: star exclusion and the two-loaded tree core

Source: `SMALL_TREE_STRESS_CORES.md`.

The research branch advanced during this continuation. Its commit
`028a63b4fc963eb78d776a7f42ff3606e651e816` already contains
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`: radial bridges, a four-square
central bridge cover, an off-origin vertex/vertex normal selection,
and the exact side/diagonal loaded-leaf forms. **Those existing results
are not counted as new work here.** The new uses are:

| Subgate | Exact implication | State |
|---|---|---|
| TREE.1 | A tree component with exactly two loaded bodies, in `79/40 <= R <= sqrt(Q)`, is a four-square side-normal path at `q=17/4`, with two possible transverse sliders | Written complete core normal form in that window |
| TREE.2 | Under the physical certificate's permitted normal selection, **no star component** can exist in that window, regardless of its number of leaves or other unstressed squares | Written whole-family exclusion |
| TREE.3 | The flat-middle subcase of TREE.1 cannot have five additional physical squares at its radius | Written consequence of ROW.2 |

TREE.2 uses just three cases: zero, one, or two diagonal leaves.
More diagonal leaves are impossible because a pair of opposite ones
would prescribe the wrong hub width. The side-only case is a weighted
second-moment contradiction; one diagonal forces opposite contact
heights farther apart than a side length; two adjacent diagonals trap
the hub inside a radius smaller than every side-leaf contact radius.
There is no orientation mesh or graph enumeration.

**Remaining TREE.1 boundary:** the two internal center offsets may vary
independently in `[-1/2,1/2]`. Setting both to zero without proof would
lose real possible cores. The full staggered-core completion problem
remains open. Trees with several branching bodies or longer arms, and
cyclic cores, are not excluded by the star theorem.

**Dependency boundary:** the lower-radius window is explicit. The
repository's n=8 result can supply it, but the current main-branch n=8
proof has computational dependencies. These are hand implications
under the stated window, not a hidden table-free proof of that prior
lower bound.

## C. Exact regressions executed locally

`check_three_square_cap.py` uses Python's standard-library `Fraction`.
`THREE_SQUARE_CAP_EXACT_CHECK.json` records source SHA-256 hashes,
execution times, Python version, and exit code zero. The executed checks
include:

- 101 exact rational instances of the displayed algebraic identities;
- 3,174 admissible rational one-square cap witnesses, including 3,154
  non-axis-aligned squares, with exact clipped section bounds;
- four exact cap-equality triples, including middle-square sliders;
- the exact capless record packing: all 36 pairs and circle bounds;
- three physical four-body radial-path stress witnesses, one diagonal
  leaf witness, and the unequal side-leaf load negative control;
- a five-square plus-star counterexample below the explicit tree window;
- a lower-floor counterexample showing the exact cap threshold cannot
  simply be weakened while retaining the same sharp conclusion.

These are **finite regression checks**. They do not replace the
all-angle/all-position proofs in the manuscripts and do not prove
unrestricted n=9 optimality. No Lean or CI was run.

## D. The real remaining global gates

1. **Stress-core completion, not just stationarity.** The existing
   27-atom physical incidence reduction and radial bridges, together
   with the discrete transmitters and TREE.1–2, constrain minimizing
   cores. One still must cover all
   loaded/branching/cyclic cores **and** their unstressed-square
   completions. Zero stress does not remove a square from the count.
2. **The staggered two-loaded tree class.** TREE.1 reduces this whole
   class to a four-square path at q=17/4. ROW.2 closes only its solid
   row subcase. A whole-class five-square completion contradiction
   would remove the remaining tree class; proving a finite collection
   of tiny offset windows would not suffice.
3. **A sharp global combination.** CAP.3 is valid in every direction
   for a hypothetical subcritical packing. Its interval antichains
   are **not** automatically horizontally separable. Combine this
   geometric constraint with physical incidence/torque information,
   or prove another exhaustive sharp invariant.
4. **Equality and verification.** CAP.N shows cap extraction alone
   is not an exhaustive equality theorem. The signed matched-chain
   families remain conditional until global necessity is established.
   Independent mathematical audit, Lean compilation and public
   integration still follow the actual global lower bound.

The common-coordinate-separable branch already closed in the repository
must not be mislabeled open. Conversely, none of CAP.1–3 or TREE.1–3
licenses marking the arbitrary-oblique global gate closed.