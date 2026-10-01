import SquaresInCircles.Seven.Analysis

/-!
# Taylor polynomials of `sin` and `cos` on `|x| ≤ 6/7`

The Taylor polynomials `sinP` of degree 7 and `cosP` of degree 6 approximate
`sin` and `cos` within `10⁻⁶` and `10⁻⁵` on `|x| ≤ 6/7`. On `[0, ∞)` they are
lower bounds, and with the next terms `x⁹/9!` and `x⁸/8!` added they are upper
bounds, each remainder having the derivative of the previous one. Lipschitz
bounds for absolute values, positive parts and products are added.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.PairTaylor

def sinP (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
def cosP (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720

@[simp] lemma sinP_neg (x : ℝ) : sinP (-x)=-sinP x := by dsimp [sinP]; ring
@[simp] lemma cosP_neg (x : ℝ) : cosP (-x)=cosP x := by dsimp [cosP]; ring

lemma cos_upper_eight {x : ℝ} (hx : 0≤x) : Real.cos x≤cosP x+x^8/40320 := by
  have hh := Seven.nonneg_of_deriv_nonneg
    (fun t => cosP t+t^8/40320-Real.cos t)
    (by dsimp [cosP]; fun_prop) (by norm_num [cosP])
    (fun t ht => by
      have hs := Seven.sin_lower_seven ht
      simp (disch := fun_prop) [cosP]
      linarith) hx
  linarith

lemma sin_upper_nine {x : ℝ} (hx : 0≤x) : Real.sin x≤ sinP x+x^9/362880 := by
  have hh := Seven.nonneg_of_deriv_nonneg
    (fun t => sinP t+t^9/362880-Real.sin t)
    (by dsimp [sinP]; fun_prop) (by norm_num [sinP])
    (fun t ht => by
      have hc := cos_upper_eight ht
      dsimp [cosP] at hc
      simp (disch := fun_prop) [sinP]
      linarith) hx
  linarith

private lemma sin_error_nonneg {x : ℝ} (hx0 : 0≤x) (hx1 : x≤6/7) :
    |Real.sin x-sinP x|≤1/1000000 := by
  have hlo : sinP x≤Real.sin x := Seven.sin_lower_seven hx0
  have hhi := sin_upper_nine hx0
  have hp := pow_le_pow_left₀ hx0 hx1 9
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  norm_num at hp
  nlinarith

private lemma cos_error_nonneg {x : ℝ} (hx0 : 0≤x) (hx1 : x≤6/7) :
    |Real.cos x-cosP x|≤1/100000 := by
  have hlo : cosP x≤Real.cos x := Seven.cos_lower_six hx0
  have hhi := cos_upper_eight hx0
  have hp := pow_le_pow_left₀ hx0 hx1 8
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  norm_num at hp
  nlinarith

theorem sin_error {x : ℝ} (hx : |x|≤6/7) : |Real.sin x-sinP x|≤1/1000000 := by
  by_cases h : 0≤x
  · exact sin_error_nonneg h ((le_abs_self x).trans hx)
  · have hx' : -x≤6/7 := by simpa only [abs_of_neg (lt_of_not_ge h)] using hx
    have hh := sin_error_nonneg (show 0≤-x by linarith) hx'
    rw [Real.sin_neg,sinP_neg] at hh
    have he : -Real.sin x-(-sinP x)=-(Real.sin x-sinP x) := by ring
    simpa only [he,abs_neg] using hh

theorem cos_error {x : ℝ} (hx : |x|≤6/7) : |Real.cos x-cosP x|≤1/100000 := by
  by_cases h : 0≤x
  · exact cos_error_nonneg h ((le_abs_self x).trans hx)
  · have hx' : -x≤6/7 := by simpa only [abs_of_neg (lt_of_not_ge h)] using hx
    have hh := cos_error_nonneg (show 0≤-x by linarith) hx'
    simpa only [Real.cos_neg,cosP_neg] using hh

lemma sin_error_coarse {x : ℝ} (hx : |x|≤6/7) : |Real.sin x-sinP x|≤1/100000 :=
  (sin_error hx).trans (by norm_num)

lemma absolute_lipschitz (x y : ℝ) : |(|x|-|y|)|≤|x-y| := by
  have hx : |x|≤|x-y|+|y| := by
    simpa only [sub_add_cancel] using abs_add_le (x-y) y
  have hy : |y|≤|x-y|+|x| := by
    have h := abs_add_le (y-x) x
    rw [sub_add_cancel,abs_sub_comm] at h
    exact h
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma positivePart_lipschitz (x y : ℝ) : |max x 0-max y 0|≤|x-y| := by
  by_cases hx : 0≤x <;> by_cases hy : 0≤y
  · rw [max_eq_left hx,max_eq_left hy]
  · rw [max_eq_left hx,max_eq_right (le_of_not_ge hy),sub_zero,abs_of_nonneg hx]
    have h := (abs_le.mp (le_refl |x-y|)).2
    linarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_left hy,zero_sub,abs_neg,abs_of_nonneg hy]
    have h := (abs_le.mp (le_refl |x-y|)).1
    linarith
  · rw [max_eq_right (le_of_not_ge hx),max_eq_right (le_of_not_ge hy),sub_self,abs_zero]
    exact abs_nonneg _

lemma product_difference (a b x y : ℝ) :
    |a*x-b*y|≤|a-b| *|x|+|b| *|x-y| := by
  have he : a*x-b*y=(a-b)*x+b*(x-y) := by ring
  rw [he]
  simpa only [abs_mul] using abs_add_le ((a-b)*x) (b*(x-y))

lemma half_linear_difference {x y X Y e : ℝ}
    (hx : |x-X|≤e) (hy : |y-Y|≤e) : |(x-y)/2-(X-Y)/2|≤e := by
  have hxb := abs_le.mp hx
  have hyb := abs_le.mp hy
  apply abs_le.mpr
  constructor <;> linarith [hxb.1,hxb.2,hyb.1,hyb.2]

end SquaresInCircles.Six.Analytic.PairTaylor
