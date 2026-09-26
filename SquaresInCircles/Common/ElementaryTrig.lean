import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Small-angle estimates used by the occupied-arc proofs

All decimal-looking constants below are exact rational numbers.  In particular,
no floating-point evaluation, external solver, or `native_decide` is used.
The five-square auxiliary radius is `5/6`, which keeps both the strip and
radial-extension estimates rational.
-/
noncomputable section
open Set
namespace SquaresInCircles

lemma pi_lt_22_over_7 : Real.pi < (22:ℝ)/7 := by
  linarith [Real.pi_lt_d4]

lemma arcsin_ge_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.arcsin x := by
  simpa [Real.sin_arcsin (by linarith) hx1] using Real.sin_le (Real.arcsin_nonneg.mpr hx0)

lemma arcsin_le_self_of_nonpos {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 0) :
    Real.arcsin x ≤ x := by
  have hh := arcsin_ge_self (show 0 ≤ -x by linarith) (show -x ≤ 1 by linarith)
  rw [Real.arcsin_neg] at hh
  linarith

/-- A deliberately non-sharp, polynomial upper bound on `[0,3/5]`. -/
lemma arcsin_le_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3/5) :
    Real.arcsin x ≤ x+x^3/4 := by
  rcases hx0.eq_or_lt with rfl | hx
  · norm_num
  have hx3 := pow_pos hx 3
  have ht : x+x^3/4 ≤ 109/100*x := by nlinarith [mul_nonneg hx0 (sub_nonneg.2 hx1)]
  rw [Real.arcsin_le_iff_le_sin ⟨by linarith,by linarith⟩
    ⟨by linarith [Real.pi_pos],by linarith [Real.two_le_pi]⟩]
  have hcube := pow_le_pow_left₀ (by positivity) ht 3
  nlinarith [Real.sin_gt_sub_cube (x := x+x^3/4) (by positivity)]

/-- A two-point arcsine comparison, from the concavity of the sine. -/
lemma arcsin_sum_gt_of_sin_lt {u v θ : ℝ}
    (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi/2)) (hs : Real.sin θ < (u+v)/2) :
    2*θ < Real.arcsin u+Real.arcsin v := by
  have hA := Real.arcsin_nonneg.mpr hu.1
  have hB := Real.arcsin_nonneg.mpr hv.1
  have hA' := Real.arcsin_le_pi_div_two u
  have hB' := Real.arcsin_le_pi_div_two v
  have hc := strictConcaveOn_sin_Icc.concaveOn.2 ⟨hA,by linarith [Real.pi_pos]⟩
    ⟨hB,by linarith [Real.pi_pos]⟩ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  simp only [smul_eq_mul,Real.sin_arcsin (by linarith [hu.1]) hu.2,
    Real.sin_arcsin (by linarith [hv.1]) hv.2] at hc
  by_contra hn
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθ.2
    (show 1/2*Real.arcsin u+1/2*Real.arcsin v ≤ θ by linarith)
  linarith

/-- The crude cosine Taylor bound is sufficient with auxiliary radius `5/6`. -/
lemma cos_gt_401_500 {t : ℝ} (ht : |t| ≤ Real.pi/5) :
    (401:ℝ)/500 < Real.cos t := by
  have habs : |t| < (22:ℝ)/35 := by linarith [pi_lt_22_over_7]
  have ht' := abs_lt.mp habs
  have hsq : t^2 < ((22:ℝ)/35)^2 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  linarith

lemma sin_pi_fifth_lt_three_fifths : Real.sin (Real.pi/5) < 3/5 := by
  have hc := cos_gt_401_500 (t := Real.pi/5)
    (by rw [abs_of_nonneg (by positivity)])
  have hu := Real.sin_sq_add_cos_sq (Real.pi/5)
  by_contra hn
  nlinarith [Real.cos_le_one (Real.pi/5)]

end SquaresInCircles
