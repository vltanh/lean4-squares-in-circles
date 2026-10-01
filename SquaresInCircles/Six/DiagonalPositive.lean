import SquaresInCircles.Six.CanonicalMargins

/-!
# The angle of D is positive

In a normalized packing `-2/5 < d ≤ π/4`, and `d ≠ 0`. For `d = -v < 0`, the D
pin gives `b > 13/100 + (47/100) v`. D is separated from the central square
along its own axis and not along the west side of C, so the difference of the
two margins, `(1 - cos v)(a - cx) - sin v (b + cy)`, is positive; the bound on
`b` and polynomial bounds on `sin v` and `cos v` make it negative.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization Normalization.Certificates

lemma fixedPin_diagonal_coordinates : fixedPin 3 = (-(9/10)*hStar,-(9/10)*hStar) := by
  have hc : Real.cos ((5/4:ℝ)*Real.pi) = -hStar := by
    rw [show (5/4:ℝ)*Real.pi=Real.pi/4+Real.pi by ring,Real.cos_add_pi,
      Real.cos_pi_div_four]
    rfl
  have hs : Real.sin ((5/4:ℝ)*Real.pi) = -hStar := by
    rw [show (5/4:ℝ)*Real.pi=Real.pi/4+Real.pi by ring,Real.sin_add_pi,
      Real.sin_pi_div_four]
    rfl
  simp [fixedPin,hc,hs]

lemma small_positive_sine_lower {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2/5) :
    (24/25)*v ≤ Real.sin v := by
  have hsq := mul_nonneg (sub_nonneg.mpr hv)
    (show 0 ≤ (2:ℝ)/5+v by linarith)
  have hcube := mul_nonneg hv0
    (show 0 ≤ (4:ℝ)/25-v^2 by nlinarith)
  have hs := Real.sin_ge_sub_cube hv0
  nlinarith

lemma small_cosine_linear_lower {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2/5) :
    1-v/5 ≤ Real.cos v := by
  have hp := mul_nonneg hv0 (sub_nonneg.mpr hv)
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]

lemma diagonal_pin_transverse_lower {a b v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 2/5)
    (hpin : openSquare (orientedSquare (Real.pi-v) a b) (fixedPin 3)) :
    13/100+(47/100)*v < b := by
  have hp := (abs_lt.mp hpin.2).2
  rw [orientedSquare_localY,fixedPin_diagonal_coordinates] at hp
  simp only [Real.sin_sub,Real.cos_sub,Real.sin_pi,Real.cos_pi,
    zero_mul,neg_one_mul,zero_sub] at hp
  have hs := small_positive_sine_lower hv0 hv
  have hc := small_cosine_linear_lower hv0 hv
  have hsum : 1+(19/25)*v ≤ Real.cos v+Real.sin v := by linarith
  have hsum0 : 0 ≤ Real.cos v+Real.sin v := by linarith
  have hprod := mul_nonneg
    (show 0 ≤ hStar-7/10 by linarith [hStar_lower]) hsum0
  nlinarith

/-- For `0 < v ≤ 2/5`, a square at phase `π - v` with `a ≤ rho0` that holds the
D pin has `(1 - cos v)(a - x) - sin v (b + y) < 0` for `x, y ≥ 0`. -/
lemma negative_diagonal_gap {a b x y v : ℝ}
    (hv0 : 0 < v) (hv : v ≤ 2/5) (ha : a ≤ rho0)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpin : openSquare (orientedSquare (Real.pi-v) a b) (fixedPin 3)) :
    (1-Real.cos v)*(a-x)-Real.sin v*(b+y) < 0 := by
  have hb := diagonal_pin_transverse_lower hv0.le hv hpin
  have hs := small_positive_sine_lower hv0.le hv
  have hs0 : 0 ≤ Real.sin v := by linarith
  have hc0 : 0 ≤ 1-Real.cos v := by linarith [Real.cos_le_one v]
  have ha' : a-x ≤ 9/8 := by linarith [rho0_upper]
  have hprodA := mul_nonneg (sub_nonneg.mpr ha') hc0
  have hcos := Real.one_sub_sq_div_two_le_cos (x := v)
  have hprodB := mul_le_mul
    (show (13:ℝ)/100+(47/100)*v ≤ b+y by linarith)
    hs (show 0 ≤ (24:ℝ)/25*v by positivity)
    (show 0 ≤ b+y by linarith)
  have hvSq := mul_nonneg hv0.le (sub_nonneg.mpr hv)
  nlinarith

namespace Normalization.NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

/-- The angle of D is positive. -/
theorem diagonal_angle_pos : 0 < P.diagonalAngle := by
  have hown := P.diagonal_own
  have hne : P.diagonalAngle ≠ 0 := by
    simpa [diagonalAngle,helperAngle,matchingCardinal,cardinalCenter] using
      P.own_angle_ne_zero 3 hown
  by_contra! hnonpos
  have hneg : P.diagonalAngle < 0 := lt_of_le_of_ne hnonpos hne
  let v := -P.diagonalAngle
  have hv0 : 0 < v := by dsimp [v]; linarith
  have hv : v ≤ 2/5 := by
    have hd := P.diagonal_angle_bounds.1
    dsimp [v]
    linarith
  have hphase : P.phase 3=Real.pi-v := by dsimp [v,diagonalAngle]; ring
  have hpin : openSquare (orientedSquare (Real.pi-v) (P.radial 3) (P.transverse 3))
      (fixedPin 3) := by simpa only [hphase] using P.pin 3
  have hbad := negative_diagonal_gap hv0 hv (P.contained 3).a_le_rho0
    P.box.1.1 P.box.2.1 hpin
  have hgap := P.canonical_gap_pos 3 hown
  rw [hphase,show Real.pi-v=Real.pi+(-v) by ring,
    show matchingCardinal 3 = CentralAxis.west from rfl,own_minus_west,
    Real.cos_neg,Real.sin_neg] at hgap
  change 0 < (1-Real.cos v)*(P.radial 3-P.center.1)+(-Real.sin v)*(P.transverse 3+P.center.2)
    at hgap
  nlinarith

lemma diagonal_angle_range : 0 < P.diagonalAngle ∧ P.diagonalAngle ≤ Real.pi/4 :=
  ⟨P.diagonal_angle_pos,P.diagonal_angle_bounds.2⟩

end Normalization.NormalizedPacking
end SquaresInCircles.Six
