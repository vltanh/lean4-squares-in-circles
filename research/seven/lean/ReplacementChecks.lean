import research.seven.lean.MarkerEnvelope
import research.seven.lean.BoundaryRatio
import research.seven.lean.TurnProfiles
import research.seven.lean.ForwardAxial
import research.seven.lean.ForwardSide
import research.seven.lean.InwardOpposite
import research.seven.lean.TransitionProfiles
import research.seven.lean.BreakpointProfiles

/-!
Interface checks, not a report of executed tests. Elaborating this file checks
that the replacement theorems have the intended hypotheses and conclusions.
It imports no public/root optimum theorem to establish a local replacement.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

-- A: original polynomial interface.
example {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < Seven.arcCurvaturePolynomial x := arc_curvature_polynomial_pos hx

-- B and N: original boundary derivative and optional original initial bound.
example {s : ℝ} (hs : 0 ≤ s ∧ s ≤ Boundary.s0) :
    Boundary.ratioD s < 1 := ratio_derivative_lt_one hs

example : Boundary.ratio 0 < (51 : ℝ)/200 := ratio_zero_lt

example : Boundary.ratio 0 < 2-Real.sqrt 3 := ratio_zero_lt_twelfth_tangent

example {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4) :
    AntitoneOn (Boundary.circleTarget t) (Icc 0 Boundary.s0) := circleTarget_decreases ht

-- C: the original complete turn interval, including zero.
example {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    z/50 ≤ Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z) :=
  inward_turn_profile hz

-- D: strictness is retained on the closed domain.
example {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    0 < 1-4*Real.pi/15+(4/5)*z-(Real.sqrt 3-1)*Real.sin z-
      (1/2)*(1-Real.cos z) := opposite_axial_scalar hz

-- E1/E2: one theorem covers both sides of the derived pi/6 switch.
example {A v z : ℝ} (h : Admissible A v) (hA : label A v=axial v)
    (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-
      (A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := axial_target_support h hA hz

-- E3: do not extend this strict inequality to the zero-turn contact.
example {A v z : ℝ} (h : Admissible A v) (hT : label A v=side A v)
    (hz : 0 < z ∧ z < 1) : 0 < Seven.sideTarget A v (-z) :=
  sideTarget_negative_pos h hT hz

-- F: the polynomial and completed-square interfaces remain unchanged.
example {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 5/8) :
    0 < Seven.radialPolynomial z := radialPolynomial_pos hz

example {z : ℝ} (hz : 0 < z ∧ z ≤ 5/8) (v : ℝ) :
    0 < Seven.radialE z v := radialE_pos hz v

example {a u A v z : ℝ} (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : z=label a u+label A v-Real.pi/6)
    (hz : 0 < z ∧ z ≤ 5/8) (hv : v ≤ 3/10) :
    0 < Seven.inwardOpposite a A v z := inward_circular_pos h h' hT hA he hz hv

-- J: original profile statements, plus explicit stronger reserves.
example {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Boundary.td) :
    0 < Boundary.transitionF t := transitionF_pos ht

example {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Boundary.td) :
    (1 : ℝ)/32000 < Boundary.transitionF t := transition_profile_reserve ht

example : 0 < Boundary.diagonalValue := diagonal_value_pos

-- K deliberately changes an INTERNAL constant, not the marker statement.
example {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    Seven.arcEnvelope x ≤ Real.pi/6+(353 : ℝ)/648 := arc_envelope_bound hx

example {a u : ℝ} (h : Admissible a u) :
    label a u+(801 : ℝ)/1600 < Real.arccos (a-1/2) := marker_vertical_endpoint h

-- L replaces the precision-only helpers by sufficient geometric domains.
example : (29 : ℝ)/100 < Boundary.u0 ∧ Boundary.u0 < 207/710 := transition_u_bounds

example : (3 : ℝ)/5 < Boundary.diagonalAngle ∧ Boundary.diagonalAngle < 5/8 := by
  simpa only [Boundary.diagonalAngle] using diagonal_angle_coarse

example {a u : ℝ} (h : Admissible a u) (hT : label a u=side a u) :
    (12/25 : ℝ)*(u-Boundary.u0) ≤ Boundary.a0-a := side_transition_trade h hT

-- M: unchanged state statements.
example {a u : ℝ} (h : Admissible a u) (hT : label a u=side a u) :
    (9 : ℝ)/25 < label a u := side_selected_label_gt h hT

example {a u : ℝ} (h : Admissible a u) (hT : label a u=side a u) :
    a < (9 : ℝ)/8 := side_selected_a_lt h hT

example {a u : ℝ} (h : Admissible a u) (hA : label a u=axial u) :
    a+u < (113 : ℝ)/80 := axial_sum_lt h hA

-- G: the private target is expressed explicitly for integration.
example {A v : ℝ} (h : Admissible A v) (hT : label A v=side A v) :
    1 < (A+1/2)*Real.cos (gap-label A v)+
      (1/2-v)*Real.sin (gap-label A v) := side_target_zero_gt_one h hT

end SquaresInCircles.Seven.Human

#print axioms SquaresInCircles.Seven.Human.arc_curvature_polynomial_pos
#print axioms SquaresInCircles.Seven.Human.arc_envelope_bound
#print axioms SquaresInCircles.Seven.Human.marker_vertical_endpoint
#print axioms SquaresInCircles.Seven.Human.circleTarget_decreases
#print axioms SquaresInCircles.Seven.Human.inward_turn_profile
#print axioms SquaresInCircles.Seven.Human.opposite_axial_scalar
#print axioms SquaresInCircles.Seven.Human.axial_target_support
#print axioms SquaresInCircles.Seven.Human.sideTarget_negative_pos
#print axioms SquaresInCircles.Seven.Human.inward_circular_pos
#print axioms SquaresInCircles.Seven.Human.transitionF_pos
#print axioms SquaresInCircles.Seven.Human.diagonal_value_pos
#print axioms SquaresInCircles.Seven.Human.transition_u_bounds
#print axioms SquaresInCircles.Seven.Human.side_selected_label_gt
#print axioms SquaresInCircles.Seven.Human.side_selected_a_lt
#print axioms SquaresInCircles.Seven.Human.axial_sum_lt
#print axioms SquaresInCircles.Seven.Human.ratio_zero_lt_twelfth_tangent
