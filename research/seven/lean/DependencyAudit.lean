import research.seven.lean.ReplacementChecks
import Lean
import Lean.Util.CollectAxioms

/-!
Local validation command. This is NOT a mathematical premise or a positivity
certificate. Run it after the proof files elaborate. It inspects accepted
constants and rejects dependencies on the old results being replaced.

Importing a module that contains an old theorem is not itself a failure:
this audit follows expression dependencies, rather than import filenames.
-/
open Lean Elab Command

namespace SevenHumanAudit

private def roots : Array Name := #[
  ``SquaresInCircles.Seven.Human.arc_curvature_polynomial_pos,
  ``SquaresInCircles.Seven.Human.arcEnvelopeSecond_le_neg_eighth,
  ``SquaresInCircles.Seven.Human.arc_envelope_bound,
  ``SquaresInCircles.Seven.Human.marker_vertical_endpoint,
  ``SquaresInCircles.Seven.Human.ratio_derivative_lt_one,
  ``SquaresInCircles.Seven.Human.ratio_zero_lt,
  ``SquaresInCircles.Seven.Human.ratio_zero_lt_twelfth_tangent,
  ``SquaresInCircles.Seven.Human.circleTarget_decreases,
  ``SquaresInCircles.Seven.Human.inward_turn_profile,
  ``SquaresInCircles.Seven.Human.opposite_axial_scalar,
  ``SquaresInCircles.Seven.Human.axial_target_support,
  ``SquaresInCircles.Seven.Human.sideTarget_negative_pos,
  ``SquaresInCircles.Seven.Human.radialPolynomial_pos,
  ``SquaresInCircles.Seven.Human.radialE_pos,
  ``SquaresInCircles.Seven.Human.inward_circular_pos,
  ``SquaresInCircles.Seven.Human.transition_u_bounds,
  ``SquaresInCircles.Seven.Human.diagonal_angle_coarse,
  ``SquaresInCircles.Seven.Human.side_transition_trade,
  ``SquaresInCircles.Seven.Human.transition_profile_reserve,
  ``SquaresInCircles.Seven.Human.diagonal_value_reserve,
  ``SquaresInCircles.Seven.Human.side_selected_label_gt,
  ``SquaresInCircles.Seven.Human.side_selected_a_lt,
  ``SquaresInCircles.Seven.Human.axial_sum_lt,
  ``SquaresInCircles.Seven.Human.side_target_zero_gt_one,
  ``SquaresInCircles.Seven.Human.clearance_support_pos
]

-- Single-backtick names intentionally allow an old declaration to have been
-- deleted later. The check is about forbidden names encountered in a proof.
private def forbidden : Array Name := #[
  `sorryAx,
  `Lean.ofReduceBool,
  `SquaresInCircles.Seven.bernstein_pos,
  `SquaresInCircles.Seven.arcCurvaturePolynomial_pos,
  `SquaresInCircles.Seven.arcEnvelopeSecond_neg,
  `SquaresInCircles.Seven.arcEnvelope_bound,
  `SquaresInCircles.Seven.marker_vertical_endpoint,
  `SquaresInCircles.Seven.inward_turn_profile,
  `SquaresInCircles.Seven.opposite_axial_scalar,
  `SquaresInCircles.Seven.axial_target_support,
  `SquaresInCircles.Seven.sideTarget_negative_pos,
  `SquaresInCircles.Seven.radialPolynomial_pos,
  `SquaresInCircles.Seven.radialE_pos,
  `SquaresInCircles.Seven.inward_circular_pos,
  `SquaresInCircles.Seven.side_selected_label_gt,
  `SquaresInCircles.Seven.side_selected_a_lt,
  `SquaresInCircles.Seven.axial_sum_lt,
  `SquaresInCircles.Seven.side_transition_trade,
  `SquaresInCircles.Seven.Boundary.J_bounds,
  `SquaresInCircles.Seven.Boundary.transition_bounds,
  `SquaresInCircles.Seven.Boundary.transition_coarse,
  `SquaresInCircles.Seven.Boundary.rd_bounds,
  `SquaresInCircles.Seven.Boundary.test_point,
  `SquaresInCircles.Seven.Boundary.transitionF_pos,
  `SquaresInCircles.Seven.Boundary.diagonal_value_pos,
  `SquaresInCircles.Seven.Boundary.diagonal_angle_bounds,
  `SquaresInCircles.Seven.Boundary.ratio_derivative_lt_one,
  `SquaresInCircles.Seven.Boundary.ratio_zero_lt,
  `SquaresInCircles.Seven.Boundary.circleTarget_decreases
]

private structure WalkState where
  seen : NameSet := {}
  visited : Nat := 0
  bad : Array Name := #[]
  missing : Array Name := #[]

private abbrev WalkM := StateT WalkState CoreM

private partial def visit (name : Name) : WalkM Unit := do
  if (← get).seen.contains name then
    return
  modify fun s => { s with seen := s.seen.insert name, visited := s.visited + 1 }
  if forbidden.contains name then
    modify fun s => { s with bad := s.bad.push name }
  let env ← getEnv
  let collectExpr (e : Expr) : WalkM Unit := e.getUsedConstants.forM visit
  -- As in Lean.Util.CollectAxioms, inspect the accepted kernel environment.
  match env.checked.get.find? name with
  | some (.axiomInfo v) => collectExpr v.type
  | some (.defnInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo v) => collectExpr v.type
  | some (.recInfo v) => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM visit
  | none => modify fun s => { s with missing := s.missing.push name }

elab "#audit_human_proofs" : command => do
  let allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let axs ← liftCoreM (Lean.collectAxioms root)
    let unexpected := axs.filter fun ax => !allowedAxioms.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms for {root}: {unexpected}"
  let (_, state) ← liftCoreM ((roots.forM visit).run {})
  unless state.missing.isEmpty do
    throwError "Dependency audit is incomplete; unavailable constants: {state.missing}"
  unless state.bad.isEmpty do
    throwError "Replacement proof depends on excluded original results: {state.bad}"
  logInfo m!"Checked {roots.size} replacement roots and {state.visited} reachable constants."
  logInfo "No excluded original result was reached; axiom sets are subsets of the allowed standard set."

end SevenHumanAudit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#audit_human_proofs
