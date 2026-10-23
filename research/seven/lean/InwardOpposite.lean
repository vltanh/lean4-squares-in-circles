import research.seven.lean.PolynomialBounds
import research.seven.lean.StateBounds
import SquaresInCircles.Seven.InwardOppositeMinima

/-!
F: adapters to the original polynomial and quadratic statements.
Neither old positivity theorem is used. The discriminant identity below is
reproved by ring normalization of the displayed polynomial definitions.
-/
noncomputable section
namespace SquaresInCircles.Seven.Human

/-- The unchanged production polynomial interface, proved by monotonicity. -/
theorem radialPolynomial_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 5/8) :
    0 < Seven.radialPolynomial z := by
  simpa only [Seven.radialPolynomial,radialP] using radial_polynomial_pos hz

lemma radial_square_identity (z v : ℝ) :
    4*(Seven.radialK z+3/8)*Seven.radialE z v =
      (2*(Seven.radialK z+3/8)*v+(Seven.radialL z-(3/5)*z))^2+
      z*Seven.radialPolynomial z := by
  unfold Seven.radialE Seven.radialK Seven.radialL Seven.radialB Seven.radialPolynomial
  ring

/-- Strict positivity is asserted only for positive turn, as in production. -/
theorem radialE_pos {z : ℝ} (hz : 0 < z ∧ z ≤ 5/8) (v : ℝ) :
    0 < Seven.radialE z v := by
  have hz2 : z^2 < (1 : ℝ) := by nlinarith [hz.1,hz.2]
  have hsin : 0 < z-z^3/6 := by
    have hp := mul_pos hz.1 (show 0 < 1-z^2/6 by linarith)
    nlinarith
  have hK : 0 < Seven.radialK z := by
    unfold Seven.radialK
    exact mul_pos (by norm_num) hsin
  have hp := mul_pos hz.1 (radialPolynomial_pos ⟨hz.1.le,hz.2⟩)
  have hid := radial_square_identity z v
  have hs := sq_nonneg (2*(Seven.radialK z+3/8)*v+(Seven.radialL z-(3/5)*z))
  have hfactor : 0 < 4*(Seven.radialK z+3/8) := by linarith
  have hproduct : 0 < 4*(Seven.radialK z+3/8)*Seven.radialE z v := by linarith
  by_contra hn
  have hnon : Seven.radialE z v ≤ 0 := le_of_not_gt hn
  have hbad := mul_nonpos_of_nonneg_of_nonpos hfactor.le hnon
  linarith

/--
The downstream circular support theorem uses the new quadratic positivity.
The retained circle/Taylor comparison lemmas are algebraic bounds, not either
of the replaced Bernstein-based positivity statements.
-/
theorem inward_circular_pos {a u A v z : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : z=label a u+label A v-Real.pi/6)
    (hz : 0 < z ∧ z ≤ 5/8) (hv : v ≤ 3/10) :
    0 < Seven.inwardOpposite a A v z := by
  have hupper := Boundary.a_le_circle h'
  have hquad := Seven.circle_quadratic_upper ⟨h'.u_nonneg,hv⟩
  have hAupper : A-1/2 ≤ Real.sqrt 3-1-(15/52)*v-(15/52+1/42)*v^2 := by
    linarith
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower])
  have hmul := mul_le_mul_of_nonneg_right hAupper hs0
  have hW := Human.side_remainder_quadratic h hT
  have hwarg : label a u-Real.pi/6=z-(5/4)*v := by
    rw [hA] at he
    dsimp [axial] at he
    linarith
  rw [hwarg] at hW
  have htrig := Seven.radial_trig_lower ⟨hz.1.le,hz.2⟩ h'.u_nonneg
    (r := Real.sqrt 3-1)
    ⟨by linarith [sqrt_three_coarse.1],by linarith [sqrt_three_coarse.2]⟩
  have hp := Human.radialE_pos hz v
  rw [Seven.inward_opposite_side_identity hT hA he,abs_of_nonneg hs0]
  dsimp [Seven.radialE] at hp
  linarith

end SquaresInCircles.Seven.Human
