# n=9 — proof status, not a case counter

**[Single proof-first deep roadmap](DEEP_GATED_ROADMAP.md)** · [structured proof gates](gates/ACTIVE_ROADMAP.json) · [draft PR #11](https://github.com/vltanh/lean4-squares-in-circles/pull/11)

## Actual mathematical status

| Deliverable | Status |
|---|---|
| Attaining nine-square construction at squared radius 1105/256 | **Available as previous source** |
| Unrestricted lower bound for **all** nine-square packings | **OPEN** |
| Complete independent exact computer-assisted proof certificate | **OPEN** |
| All q=1105/256 equality packings classified | **OPEN** |
| Hand proof or compact exact tables | **LATER** |
| Lean / CI formalization | **DEFERRED** |

**One active gate: `D.1.a`** — an exact direct semialgebraic model of all nine physical unit squares (9 square poses, 36 corner tests, 36 pairwise SAT disjunctions). The immediate deliverable is a faithful polynomial-disjunction emitter and mathematical equivalence proof, **not a claimed global solver result**.

**Primary attempt:** direct exact computer certification of all `R²<1105/256` packings, with a proof-producing feasibility pilot (`D.3`). **Fallback:** globally exhaustive stress/geometry route using the existing three-cut theorem as a conditional input, *not* an original-case scoreboard. Either fully proved route is sufficient; they are alternatives.

All old original coarse/fine/exterior progress counts and duplicated trackers are **retired and deleted from this PR branch** (recoverable via Git history). Historical mathematical proofs and certificates are retained for reuse; the [old cyclic case source](CYCLIC_CELL_LEDGER.md) is *not* current progress. No new sharp theorem follows from this bookkeeping change.

An unsat solver report without certificate, finite pose sample, partial branch tree or fixed `Q-ε` bound is not a proof. Preserve any undecided full-nine root; only complete exact coverage with independent verifier can close necessity. Equality is separate. **No Lean, Lake or CI.**
