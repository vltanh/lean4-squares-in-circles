# PR #10 — canonical table-free Lean source handoff

**Reconciled:** 2026-10-22 (America/Chicago). **Branch:** `formalize/eight-uncompiled-draft`. **PR:** [#10](https://github.com/vltanh/lean4-squares-in-circles/pull/10), base `research/eight-proof`. **Latest public proof-writing checkpoint:** [`e542f7ae`](https://github.com/vltanh/lean4-squares-in-circles/commit/e542f7aeee45b4f6e8f8919b1ddf3ceca3fcd062). Always re-fetch live HEAD before editing.

> **Verdict:** the unrestricted n=8 table-free hand proof now has an **end-to-end uncompiled Lean source draft**: `high_GA_BT2_exclusion : HighGABT2Exclusion`, an unconditional `table_free_sharp_source_entry : SharpSourceEntry`, and a public geometric sharp theorem routing through that source. **Lean has not been run, and none of these are kernel verified.** A written proof body and a verified formal theorem are different deliverables. The PR must not be marked proved or merged before G9.

## 0. First action

Read [the nested gated roadmap](TABLEFREE_EXECUTION_GATES_2026_10_22.md). It uses four statuses: H = hand mathematical argument, D = Lean body drafted, J = assembled into actual public import route, V = ordinary Lean kernel verified. G0–G8 currently have D/J source paths; G9 V is not started. No native kernel, `native_decide`, external scripts or new axioms are permitted.

## 1. Exact source chain

```text
original seven-word normalization and physical SourceDomain
  -> G/T same-radius necessary transports and signed scalar exclusion
  -> GlobalGAHighBT2Complete.high_GA_BT2_exclusion
  -> GlobalGAHighOwnerExit.sharp_source_entry_of_BT2_exclusion
  -> GlobalGAHighSourceComplete.table_free_sharp_source_entry
  -> TableFree.table_free_original_rigidity
  -> GeometricModel.SharpAssembly.origin_sharp_rigidity
  -> origin_sharp_lower_bound / SharpEquality.sharp_uniqueness
  -> GeometricModel.Theorem.optimum
  -> SquaresInCircles.optimum 8
```

The necessary E move is performed on an actual original `SourceDomain` *before* A moves. The moved A cycle is used only for valid necessary inequalities. The actual q, true source H/D anchors, signed TD0/TD2 error, all originally selected physical witnesses and weak ties are retained or recovered. The original-radius dual is applied to the actual input, not to an artificial endpoint.

## 2. Source-writing commits and theorem names

| Gate | Proof-writing commit | Actual source result | Status |
|---|---|---|---|
| BT2.3.7 | [`13ea9627`](https://github.com/vltanh/lean4-squares-in-circles/commit/13ea96275d03679a688fdaf19cf5035dffc96188) | Negative A with nonnegative selected E, both short/long E charge regimes (`negative_A_nonnegative_E_positive_TD2_raw_false`) | D |
| BT2.3.8 | [`34a4773e`](https://github.com/vltanh/lean4-squares-in-circles/commit/34a4773ed3623ca004dca7f6e1f7510ac512eaf6) | E-first/A-second source and actual GA2/AB0 secondary cases | D |
| Source name repair | [`a9a0d973`](https://github.com/vltanh/lean4-squares-in-circles/commit/a9a0d9737307903dd457c1572df6461e3715b048) | Raw vs core-E theorem names disambiguated | D |
| BT2.3.9 | [`dfe7be58`](https://github.com/vltanh/lean4-squares-in-circles/commit/dfe7be58e2e852fb0c77373280a90a50e0857437) | Joint genuine negative A/E positive TD2 (`negative_A_negative_E_positive_TD2_false`), real DE3/EH1 and EH0 secondary | D |
| BT2.3.10 | [`9a95c1f1`](https://github.com/vltanh/lean4-squares-in-circles/commit/9a95c1f1ce23eabf0f1c12813709b98e29f3a1fa) | Core E-first all-T/ all-A sign dispatcher (`core_E_all_T_false`) | D |
| G4 source | [`304501f6`](https://github.com/vltanh/lean4-squares-in-circles/commit/304501f64c52971ca4c4470b5d293adc4e68e9d7) | Whole-domain `high_GA_BT2_exclusion` | D/J |
| G7 | [`d89955c7`](https://github.com/vltanh/lean4-squares-in-circles/commit/d89955c703a5b187554314dc1ec0c6f4c4506642) | Unconditional `table_free_sharp_source_entry` | D/J |
| G8 | [`739d9428`](https://github.com/vltanh/lean4-squares-in-circles/commit/739d9428c84a25ce60afeb65e308f94a9b8a470b) | Remove `Candidate.capture` from `GeometricModel.SharpAssembly` and use original-q table-free source rigidity | D/J |
| G8 | [`b57bc3ca`](https://github.com/vltanh/lean4-squares-in-circles/commit/b57bc3ca42b5b1847fab92daf353fdda639eec69) | Replace obsolete `via_capture` entry callers in `TableFree.EntryReduction` | D/J |
| G8 | [`e542f7ae`](https://github.com/vltanh/lean4-squares-in-circles/commit/e542f7aeee45b4f6e8f8919b1ddf3ceca3fcd062) | Root `SquaresInCircles.lean` no longer imports legacy `Eight.Theorem`; public `GeometricModel` route; stage axiom audit commands | D/J |

## 3. Current gate ledger

| Gate | Source status | Verified status |
|---|---|---|
| G0 Stationary sharp datum and five-parameter equality | Drafted | Not verified |
| G1 Original-boundary/normal transport | Drafted and joined | Not verified |
| G2 All seven quarter-word exclusions | Drafted and joined | Not verified |
| G3 Original source, signs and owners | Drafted and joined | Not verified |
| G4 Exhaustive high-GA/BT2 and G/T terminal source matrix | Drafted and joined | Not verified |
| G5 Hard terminal and actual anchor loss | Drafted and joined | Not verified |
| G6 Original recovered source, weak selected-normal equality | Drafted and joined | Not verified |
| G7 Unconditional `SharpSourceEntry` | Drafted and joined | Not verified |
| G8 Unrestricted radius and complete equality family, public import swap | Drafted and joined | Not verified |
| **G9 Lean/Mathlib ordinary kernel checking, repair, trust/dependency audit** | **Pending** | **Not run** |

## 4. Remaining obligations

1. Audit the exact imported signatures and namespace, all real sign/tie endpoints and whether the moved E/A/G/T records are treated only as allowed necessary cycles. Fix any concrete source errors found. The new files have **not been typechecked**.
2. Traverse the complete transitive public module import graph from `SquaresInCircles/Eight/GeometricModel/Theorem.lean` and `SquaresInCircles.lean`. Ensure the new route has no `Eight.Theorem`, `Candidate.Capture` or `Generated.AffineBudgets` path; keeping a separate legacy module is fine.
3. Once *separately authorized* to compile, run standard Lean/Mathlib on the public theorem and equality family; resolve every elaboration error without `sorry`, axioms, native compiler trust or generated lookup.
4. Run the staged `AxiomAudit.lean` commands only after compilation. Require standard `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, and a proven capture-free dependency route.
5. Keep PR #10 open until source and kernel verification succeed. Do not describe this drafted source as a verified theorem.

## 5. Source references

The [full table-free hand theorem](HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md), [global original-owner hand argument](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md), and [original equality pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md) remain canonical mathematical references. [Old 21-Oct gate ledger](TABLEFREE_LEAN_CLOSURE_ROADMAP_2026_10_21.md), older snapshots in `STATUS.md`, and archived reports are historical, not current source status.
