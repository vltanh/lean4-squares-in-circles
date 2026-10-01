import SquaresInCircles.Six.Analytic.DiagonalHalfBound

/-!
# The first axes across a phase gap of at most `11/10`

Two exterior squares with phases `q` apart, the first with a radial coordinate
at most `ρ0` and the second with one at least `aMin` and a transverse
coordinate of absolute value below `1/2`, are not separated along the axis
`-e₁` of the first square as soon as `cos q ≥ 9/20`: the projection of the
centre difference stays below the threshold `1/2 + (|cos q| + |sin q|)/2`. With
the roles exchanged, the same holds for the axis `e₁` of the second square. The
Taylor bound of `cos` at `11/10` gives `cos q ≥ 9/20` for `|q| ≤ 11/10`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma cosine_lower_eleven_tenths {q : ℝ} (hq : |q|≤11/10) : 9/20≤Real.cos q := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg q)
    (show (11:ℝ)/10≤Real.pi by linarith [Real.pi_gt_d2]) hq
  have hp := Seven.cos_lower_six (x := (11:ℝ)/10) (by norm_num)
  rw [Real.cos_abs] at hc
  norm_num at hp
  linarith

lemma inward_primary_cosine_bound {a A B q : ℝ}
    (ha : a≤rho0) (hA : aMin≤A) (hB : |B|<1/2) (hq : 9/20≤Real.cos q) :
    a-A*Real.cos q+B*Real.sin q<1/2+angularWidth q := by
  have hA0 : 0≤A+1/2 := by dsimp [aMin] at hA; linarith [rho0_upper]
  have hp := mul_le_mul_of_nonneg_left hq hA0
  have hb : B*Real.sin q≤|B| *|Real.sin q| := by
    simpa only [abs_mul] using le_abs_self (B*Real.sin q)
  have hb' := mul_le_mul_of_nonneg_right hB.le (abs_nonneg (Real.sin q))
  dsimp [angularWidth]
  rw [abs_of_nonneg (show 0≤Real.cos q by linarith)]
  dsimp [aMin] at hA
  nlinarith [rho0_upper]

lemma destination_primary_cosine_bound {a b A q : ℝ}
    (hA : A≤rho0) (ha : aMin≤a) (hb : |b|<1/2) (hq : 9/20≤Real.cos q) :
    A-a*Real.cos q-b*Real.sin q<1/2+angularWidth q := by
  have hh := inward_primary_cosine_bound (a := A) (A := a) (B := -b)
    hA ha (by simpa only [abs_neg] using hb) hq
  nlinarith only [hh]

end SquaresInCircles.Six.Analytic
