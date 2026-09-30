import SquaresInCircles.Six.Analytic.FixedPairPolynomialError

/-!
# From explicit endpoint algebra to the actual analytic pair gap

The full perturbation loss is at most
25/10^6 + 14/10^6 + 15/10^6 + 5/10^6 + 476/10^7 + 51/10^6,
which is strictly below the paid 1/5000. The error estimate is global on the
stated pair domain. Only its values at the geometrically forced endpoints
are used to close the concavity argument.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair.Polynomial
open Stress Normalization PairTaylor

private def actualLinear (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  threshold n w+
    (if u=0 ∨ u=3 then ((northForce no u n w).1-(northForce no u n w).2)/2 else 0)+
    ((westForce wo u n w).1-(westForce wo u n w).2)/2-
    penalty no wo n w-pairBase-line w-(1/1000)*|n|

private lemma gap_components (no wo : Bool) (u : Fin 4) (n w : ℝ) :
    gap no wo u n w=actualLinear no wo u n w-
      northRadius u*Real.sqrt ((northForce no u n w).1^2+(northForce no u n w).2^2)-
      Six.radius*Real.sqrt ((westForce wo u n w).1^2+(westForce wo u n w).2^2) := by
  unfold gap minorant actualLinear northUpper northRadius northVertex
  split_ifs <;> ring

private lemma actualLinear_lower {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) :
    linearPart no wo u n w-59/1000000≤actualLinear no wo u n w := by
  have hN := north_vector_error hd u
  have hW := west_vector_error hd u
  have hNhalf := abs_le.mp (half_linear_difference hN.1 hN.2)
  have hWhalf := abs_le.mp (half_linear_difference hW.1 hW.2)
  have hT := abs_le.mp (threshold_error hd)
  have hP := abs_le.mp (penalty_error hd)
  have hNc :
      (if u=0 ∨ u=3 then ((northVector no u n w).1-(northVector no u n w).2)/2 else 0)-7/500000≤
      (if u=0 ∨ u=3 then ((northForce no u n w).1-(northForce no u n w).2)/2 else 0) := by
    split_ifs
    · linarith [hNhalf.1]
    · norm_num
  dsimp [actualLinear,linearPart]
  linarith only [hNc,hWhalf.1,hT.1,hP.2,base_bound]

private lemma north_root_upper {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) :
    northRadius u*Real.sqrt ((northForce no u n w).1^2+(northForce no u n w).2^2)≤
      northScale u*Real.sqrt (northSquare no u n w)+119/2500000 := by
  have he := north_vector_error hd u
  have hl := length_le_of_coordinate_errors (by norm_num : (0:ℝ)≤7/500000) he.1 he.2
  have hc := northScale_bounds u
  have hp := mul_le_mul hc.2.1 hl (Real.sqrt_nonneg _) hc.2.2.1
  have hcost := mul_le_mul_of_nonneg_right hc.2.2.2
    (by norm_num : (0:ℝ)≤2*(7/500000))
  change northRadius u*Real.sqrt ((northForce no u n w).1^2+(northForce no u n w).2^2)≤
    northScale u*(Real.sqrt (northSquare no u n w)+2*(7/500000)) at hp
  nlinarith only [hp,hcost]

private lemma west_root_upper {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) :
    Six.radius*Real.sqrt ((westForce wo u n w).1^2+(westForce wo u n w).2^2)≤
      circleUpper*Real.sqrt (westSquare wo u n w)+51/1000000 := by
  have he := west_vector_error hd u
  have hl := length_le_of_coordinate_errors (by norm_num : (0:ℝ)≤3/200000) he.1 he.2
  have hc := circle_bounds
  have hp := mul_le_mul hc.2.1 hl (Real.sqrt_nonneg _) hc.2.2.1
  have hcost := mul_le_mul_of_nonneg_right hc.2.2.2
    (by norm_num : (0:ℝ)≤2*(3/200000))
  change Six.radius*Real.sqrt ((westForce wo u n w).1^2+(westForce wo u n w).2^2)≤
    circleUpper*(Real.sqrt (westSquare wo u n w)+2*(3/200000)) at hp
  nlinarith only [hp,hcost]

/-- Uniform analytic error control. This is valid at every point of Domain,
not a statement inferred from endpoint samples. -/
theorem polynomial_lower_bound {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) :
    budget no wo u n w-northScale u*Real.sqrt (northSquare no u n w)-
      circleUpper*Real.sqrt (westSquare wo u n w)≤gap no wo u n w := by
  have hlin := actualLinear_lower hd u
  have hN := north_root_upper hd u
  have hW := west_root_upper hd u
  rw [gap_components]
  dsimp [budget]
  linarith

/-- Three explicit scalar inequalities after two sign-checked squarings.
This is an ordinary real proposition, not the result of a certificate engine. -/
def EndpointAlgebra (no wo : Bool) (u : Fin 4) (n w : ℝ) : Prop :=
  0<budget no wo u n w ∧
    squareN no u n w+squareW wo u n w<(budget no wo u n w)^2 ∧
    4*squareN no u n w*squareW wo u n w<
      ((budget no wo u n w)^2-squareN no u n w-squareW wo u n w)^2

/-- Exact polynomial/rational endpoint algebra implies positivity of the
actual gap through the proved Taylor and perturbation inequalities. -/
theorem positive_of_endpoint_algebra {no wo : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no wo n w) (he : EndpointAlgebra no wo u n w) : 0<gap no wo u n w := by
  have hroots := scaled_two_roots_lt he.1 (northScale_bounds u).2.2.1 circle_bounds.2.2.1
    (show 0≤northSquare no u n w by dsimp [northSquare]; positivity)
    (show 0≤westSquare wo u n w by dsimp [westSquare]; positivity) he.2.1 he.2.2
  have hbound := polynomial_lower_bound hd u
  linarith

end SquaresInCircles.Six.Analytic.FixedPair.Polynomial
