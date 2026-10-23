# Source recovery after the executor reset

This is a recovery manifest, not a proof or an audit. The executor returned at
the older local snapshot `874971c` (corresponding remote checkpoint `bb8b49da`).
Root reported that hundreds of later drafts were absent. The function store was
also reset. The exact three-lemma patch below survived in the agent's visible
conversation and was materialized on request. No other lost source was rebuilt.
No Lean, lake, tests, CI, typechecking, or source audit was run.

## Source restored in this recovery

`SquaresInCircles/Eight/TableFree/SecondOuterNegativeThreeStationaryAlgebra.lean`
contains the retained, uncompiled proof scripts:

- `stationary_radius_curvature`: from `0 < k < .928`, `p < -.221`, and
  `t < -.742`, proves `-1 + t/k^3 - 3*p^2/k^4 < -2`.
- `stationary_projection_lower`: for `1.752 < u < 1.765`,
  `.5 ≤ w ≤ .92`, `-.5 ≤ z ≤ -.4`, and `1.077 < v`, proves
  `(Q-u)/(u*(Q+1-2*u)) + (w/u)*z/((Q+1-2*u)*v) > .687`.
- `inverse_factor_lower`: if `u > 0` and `Q+1-2*u > 0`, proves
  `(Q-u)/(u*(Q+1-2*u)) > .8`.

Here `Q = 9789/2500`. These are rational estimates only; the geometric
invocations and final NegativeThree theorem are not restored by this file.

## Missing hard-chain source: retained manifest and interfaces

The following names and API shapes were retained from the source-recovery
agent's pre-reset context. They record previously reported draft work, not
kernel-checked theorems. This is not an exhaustive dependency inventory, and
individual file presence has not been audited against the restored snapshot.
All Lean basenames below belong under `SquaresInCircles/Eight/TableFree/`.

| File | Retained role / API |
| --- | --- |
| `HardClassReduction.lean` | `HardInput.reduce_to_nonpositive`, `hard_radius_lower_bound`, `hard_anchor_rigidity`, `no_anchor_inside`, `no_hard_strict_loss` |
| `HardClassSharpness.lean` | `hard_middle_rigidity`, `hard_middle_signs`, `hard_middle_tangent_bounds`, `hard_source_nonpositive`, `hard_class_sharp`, `no_strict_zero_contact`, `hard_source_totals` |
| `HardSourceWitnesses.lean` | `hard_physical_source`, `hard_boundary_source_equality`, `hard_boundary_original_witnesses`; reconstructs original physical frames, centers, selected normals, and zero selected slack |
| `NegativeEntryObstructions.lean` | `one_negative_G_false`, `one_negative_T_false`, `both_negative_primaries_false`, `negative_or_hard_terminal_entry` |
| `SourceAwarePreprocessing.lean` | `GPairSourceOutput`, `TPairSourceOutput`, `preprocess_G_pair_with_source`, `preprocess_T_pair_with_source` |
| `PrimarySourceRecovery.lean` | source-aware pair preprocessing, `NormalizedBoundaryInput.pullback_hard_primaries`, `source_sharp_after_primary_preprocessing`, `boundary_original_witnesses_after_primary_preprocessing` |

The central retained statements, for `I : SignedCycle.HardInput q`, were:

- `hard_radius_lower_bound hqL : qStar ≤ q`, with `hqL : qLow ≤ q`.
- `hard_anchor_rigidity hqL hq : q = qStar ∧ AllAnchorsOn qStar I.cycle`,
  with `hq : q ≤ qStar`. The conclusion concerns the original anchors.
- `hard_class_sharp hqL hq` gives `q = qStar`,
  `θA = θB`, `θG = θH`, `θT = θD`, `θE = θD`, `θA = θD`,
  `θH - θD = FiveCorner.selected.angle`, all five original anchor circles,
  and zero slack for every owner in `terminalOwners`.
- `no_strict_zero_contact hqL hq i hi j hj` excludes positive original
  slack when `i = H ∨ i = T` and `j = 0 ∨ j = 2`.

`GPairSourceOutput` wrapped the actual `GPairOutput` and retained two facts.
If original GA0 was already feasible, the output point and frame were literally
the originals. If original GA0 was absent but the *actual output* had GA0, then
either `0 < θA-θH` or its retained HG inequality was strict. The premise referred
to actual output feasibility, not merely the selected owner label. The T record
was the exact reflected dual. Pair preprocessing preserved all anchor points
and frames, actual retained weak axes, and both variation bounds.

`NormalizedBoundaryInput.pullback_hard_primaries` applied these traces to an
actual hard pair descendant. The descendant's sharp frame totals excluded the
positive-total alternatives; `no_strict_zero_contact` excluded the strict
alternatives. This recovered original GA0 and BT2. Sharpness was then applied
fresh to the original cycle. The physical wrapper used
`I.cycle = SignedCycle.atFrame F`, with `F` fixing original θA to zero, and
`Candidate.OwnerRestriction C SignedCycle.normalOwners`. Its result comprised
original `StationaryFrames`, terminal owner restriction, the original selected
physical normal on each edge, and zero original selected SAT margin.

Retained supporting module names (exact dependency edges were not preserved):
`HardMiddleAlignment`, `HardSplitCap`, `HardSplitCycle`,
`OrderedCancelingCycle`, `PositiveCancelingOuter`, `CanonicalHardEndpoint`,
`AlignedChainBounds`, `AlignedCycleBounds`, `EInteriorGeometry`, `EContactCurve`,
`AlignedMixedE`, `EZeroFunctions`, `MiddlePositiveContraction`, `MiddleBelowCycle`,
`NegativeNoncancelingBarrier`, `NegativeNoncancelingOuter`,
`NegativeNoncancelingCycle`, `PositiveNoncancelingOuter`, and
`PositiveNoncancelingCycle` (all `.lean`). Retained joining APIs included
`HardInput.align_ordered_canceling_outer`, `HardSplitCycle.exists_split_aligned`,
and `HardSplitCycle.exists_split_strict_loss`.

Recovery must retain the original radius and original physical witnesses.
Strict circle loss belongs to the rigid anchor ledger; G and T are free and
must never provide a strict-loss obstruction. Negative-entry constructions
used actual H/D losses. No generated `Candidate.capture` shortcut or assumed
endpoint rigidity may replace the missing geometric arguments.

## NegativeThree family: pre-reset status and final remaining proof

Scope: second word `0011011`, edge3 outer/outer signs `(-,-)`, reflected to
edge5 signs `(+,+)`. The target is the original-axis bound
`phi - T(b) + K(B) > .89777 > .89765` on both angle halves.

Seven uncompiled drafts had been reported ready before the reset:
`SecondOuterNegativeThreeFirstOwners`, `SecondOuterNegativeThreeReferences`,
`SecondOuterNegativeThreeShape`, `SecondOuterNegativeThreeSpeed`,
`SecondOuterNegativeThreeAligned`, `SecondOuterNegativeThreeDiagonal`, and
`SecondOuterNegativeThreeSourceOwners` (all `.lean`). They covered original
owners 0 and 1 in both halves, owner 2 above alignment, and owner 3 in both
halves. These bodies are not reconstructed in this recovery.

The remaining case was original owner 2 below alignment. Put

\[
 U=\sqrt{Q-(b+\tfrac12)^2},\quad W=b+\tfrac12,\quad
 B_*(b,x)=\tfrac12-(U-1)\cos x+W\sin x,
\]
\[
 v=(U-1)\sin x+W\cos x,\quad
 k=(W/U)\cos x+\sin x,\quad
 C=\pi/2-x-T(b)+K(B_*).
\]

Study the actual compact contact domain
`0 ≤ b ≤ d`, `0 ≤ x ≤ .7`, `0 ≤ B_* ≤ d`. The inactive part `B_* < 0`
continues monotonically to `B_* = 0`. Interior minima are excluded as follows.

- For `B_* ≥ .1`, angular stationarity gives
  `Cxx = v^2 * (K'' - (B_*-.5)*(K')^3) < 0`, using the previously drafted
  `K_stationary_curvature`.
- For `B_* ≤ .1`, angular stationarity and the circle identity give
  `u(B) = (Q+1-(B-.5)^2-(K')^(-2))/2`. The restored curvature estimate,
  the existing fixed K references, and one strong-concavity tangent give
  `1.752 < u < 1.765`. Hence `.394 < b < .42` and `v > 1.077`.
  The exact identity
  `k/v = (Q-u)/(u*(Q+1-2*u)) + (W/u)*(B-.5)/((Q+1-2*u)*v)`
  and the restored quotient estimate give `k/v > .687`.
  Since `T'(b) ≤ T'(.394) < .68`, the source derivative is positive.

The actual six boundaries are `b=0`, `b=d`, `B_*=0`, `B_*=d`, `x=0`,
and `x=.7`. Retained simplifications for their unfinished translation:

1. Alignment uses the earlier actual aligned bound. The zero-source angular
   derivative is negative, so its endpoint at `.7` suffices.
2. At diagonal source, `v^2 > 1.95`, `K'' < -.221`, `K' < .928`, and
   `B_*-.5 ≥ -.4` give uniform negative angular curvature directly.
3. On zero target, the hand note's angle barrier `x < .571-.72*b` needs
   no tangent-function estimate. For `y=b1-b`, use
   `A0 > .02+.48*y`, `D0 < .571`, `cos(C0) > 5/6`, and
   `sin(C0) ≤ C0 < .00184+.72*y` in
   `F'' = cos(C0)*A0 - sin(C0)*D0`. The result is positive on `0≤y<.791`.
   The coarse whole-arc bound `T(b)-.72*b < .071` already gives cost `>.8988`.
4. On diagonal target, the restored `inverse_factor_lower` replaces the
   angular-speed estimates. The exact square identity is
   `Q-u-(4/5)*u*(Q+1-2*u) = (8/5)*(u-7707/5000)^2+1783401/15625000`.
   Thus the inverse-contact cost increases with source b on the actual
   `b>.75` arc, because `-ContactInverse.first > .8 > T'(b)`.
5. The fixed-angle boundary is the sharp remaining scalar gate. The hand
   proof uses whole-interval `J''' < -.36`, `J'(.4) > .06`,
   `J''(.4) > .24`, and the single reference at `b=.275034`:
   `J > .8977814`, `abs J' < 1e-6`. The cap endpoint has
   `J(bmax) > .8977831`. Strong convexity and concavity of J' cover the
   entire interval; no scalar table is needed.

After restoring the lost prerequisites, the work still required is to connect
these estimates to actual contact derivatives, prove the six boundary bounds,
assemble the compact minimum argument, restore the original inequality,
and join all owners, reflection, and the actual cycle wrapper.

Primary hand sources:
`HAND_WRONG_0011011_EDGE3_NEGATIVE_WITHOUT_TABLES.md` in this directory and
`../WRONG_0011011_EDGE3_NEGATIVE_OUTER_QUARTER_HAND_PROOF.md`.

Reusable lost geometry was in `SecondWord.NegativeTwo.TargetContact`:
`B_source_hasDerivAt`, `k_source_hasDerivAt`, `B_angle_hasDerivAt`,
`B_source_monotone`, `B_angle_monotone`, and `norm_identity`.
`NegativeTwo.ContactInverse.angle_hasDerivAt hb hz` differentiated
`angle z` at source b, with `hb : b ∈ Icc 0 d` and
`hz : z ∈ Icc (-.5) .4`; `original_angle` recovered the actual contact angle.
