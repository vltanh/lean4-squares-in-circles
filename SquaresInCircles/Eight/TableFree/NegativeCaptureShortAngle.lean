module

public import SquaresInCircles.Eight.TableFree.NegativeCaptureData
public import SquaresInCircles.Eight.TableFree.NegativeCaptureStress

/-!
# Exact short-angle constants and norm perturbations for negative capture

Uncompiled reconstruction.  Alternating Taylor bounds control the one
fixed geometric angle 3/200.  The global norm inequality is proved by
positive squaring, so no lower bound on a changing radicand is needed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.NegativeCaptureShortAngle

def r : ℝ := 3/200
def σ : ℝ := (NegativeCaptureData.sigma:ℝ)
def χ : ℝ := (NegativeCaptureData.chi:ℝ)
def error : ℝ := 1/100000000000

theorem sin_close : |Real.sin r-σ|<1/1000000000000 := by
  have hl := sin_lower_seven (show (0:ℝ)≤3/200 by norm_num)
  have hu := sin_upper_five (show (0:ℝ)≤3/200 by norm_num)
  norm_num at hl hu
  apply abs_lt.mpr
  dsimp [r,σ,NegativeCaptureData.sigma]
  constructor <;> norm_num <;> linarith

theorem cos_close : |Real.cos r-χ|<1/1000000000000 := by
  have hl := cos_lower_six (show (0:ℝ)≤3/200 by norm_num)
  have hu := cos_upper_four (show (0:ℝ)≤3/200 by norm_num)
  norm_num at hl hu
  apply abs_lt.mpr
  dsimp [r,χ,NegativeCaptureData.chi]
  constructor <;> norm_num <;> linarith

theorem constants : (99/100:ℝ)<χ ∧ χ≤1 ∧ 0≤σ ∧ σ<1/50 ∧
    (99/100:ℝ)<Real.cos r := by
  have hc := cos_lower_two (show (0:ℝ)≤3/200 by norm_num)
  norm_num at hc
  norm_num [χ,σ,r,NegativeCaptureData.chi,NegativeCaptureData.sigma]
  linarith

theorem sine_lower : (1499/100000:ℝ)<Real.sin r := by
  have hs := sin_close
  have hl := (abs_lt.mp hs).1
  norm_num [σ,NegativeCaptureData.sigma] at hl
  linarith

theorem sec_close : |1/Real.cos r-1/χ|<2/1000000000000 := by
  obtain ⟨hχ,hχ1,hσ,hσ1,hc⟩ := constants
  have hc0 : 0<Real.cos r := by linarith
  have hχ0 : 0<χ := by linarith
  have hp : 0<Real.cos r*χ := mul_pos hc0 hχ0
  have hp' : (98/100:ℝ)<Real.cos r*χ := by nlinarith
  rw [show 1/Real.cos r-1/χ=(χ-Real.cos r)/(Real.cos r*χ) by
    field_simp [hc0.ne',hχ0.ne']; ring,abs_div,abs_of_pos hp]
  apply (div_lt_iff₀ hp).2
  rw [abs_sub_comm]
  linarith [cos_close]

theorem tan_close : |Real.tan r-σ/χ|<2/1000000000000 := by
  obtain ⟨hχ,hχ1,hσ,hσ1,hc⟩ := constants
  have hc0 : 0<Real.cos r := by linarith
  have hχ0 : 0<χ := by linarith
  have hp : 0<Real.cos r*χ := mul_pos hc0 hχ0
  have hp' : (98/100:ℝ)<Real.cos r*χ := by nlinarith
  have hs := mul_le_mul_of_nonneg_right sin_close.le hχ0.le
  have hcos := mul_le_mul_of_nonneg_left cos_close.le hσ
  have hn := abs_add ((Real.sin r-σ)*χ) (σ*(χ-Real.cos r))
  rw [abs_mul,abs_mul,abs_of_pos hχ0,abs_of_nonneg hσ,abs_sub_comm χ] at hn
  have hnum : |(Real.sin r-σ)*χ+σ*(χ-Real.cos r)|<
      (103/100)*(1/1000000000000:ℝ) := by nlinarith
  rw [Real.tan_eq_sin_div_cos,
    show Real.sin r/Real.cos r-σ/χ=
      ((Real.sin r-σ)*χ+σ*(χ-Real.cos r))/(Real.cos r*χ) by
        field_simp [hc0.ne',hχ0.ne']; ring,
    abs_div,abs_of_pos hp]
  apply (div_lt_iff₀ hp).2
  linarith

theorem product_error {a z : ℝ} (ha : |a|≤1)
    (hz : |z|<1/1000000000000) : |a*z|≤1/1000000000000 := by
  rw [abs_mul]
  have hh := mul_le_mul ha hz.le (abs_nonneg z) (by norm_num : (0:ℝ)≤1)
  simpa using hh

theorem shifted_cos_error (α : ℝ) :
    |Real.cos (α-r)-(Real.cos α*χ+Real.sin α*σ)|≤error := by
  rw [Real.cos_sub,
    show Real.cos α*Real.cos r+Real.sin α*Real.sin r-
      (Real.cos α*χ+Real.sin α*σ)=
        Real.cos α*(Real.cos r-χ)+Real.sin α*(Real.sin r-σ) by ring]
  have h1 := product_error (Real.abs_cos_le_one α) cos_close
  have h2 := product_error (Real.abs_sin_le_one α) sin_close
  have hh := abs_add (Real.cos α*(Real.cos r-χ)) (Real.sin α*(Real.sin r-σ))
  dsimp [error]
  linarith

theorem shifted_sin_error (α : ℝ) :
    |Real.sin (α-r)-(Real.sin α*χ-Real.cos α*σ)|≤error := by
  rw [Real.sin_sub,
    show Real.sin α*Real.cos r-Real.cos α*Real.sin r-
      (Real.sin α*χ-Real.cos α*σ)=
        Real.sin α*(Real.cos r-χ)-Real.cos α*(Real.sin r-σ) by ring]
  have h1 := product_error (Real.abs_sin_le_one α) cos_close
  have h2 := product_error (Real.abs_cos_le_one α) sin_close
  have hh := abs_sub (Real.sin α*(Real.cos r-χ)) (Real.cos α*(Real.sin r-σ))
  dsimp [error]
  linarith

theorem norm_coordinate_perturbation (a x y : ℝ) :
    Real.sqrt (a^2+x^2)≤Real.sqrt (a^2+y^2)+|x-y| := by
  have hx := Real.sq_sqrt (show 0≤a^2+x^2 by positivity)
  have hy := Real.sq_sqrt (show 0≤a^2+y^2 by positivity)
  have hyabs : |y|≤Real.sqrt (a^2+y^2) := by
    nlinarith [sq_abs y,Real.sqrt_nonneg (a^2+y^2),abs_nonneg y,sq_nonneg a]
  have hcross : y*(x-y)≤Real.sqrt (a^2+y^2)*|x-y| := by
    calc
      y*(x-y)≤|y*(x-y)| := le_abs_self _
      _=|y|*|x-y| := abs_mul _ _
      _≤Real.sqrt (a^2+y^2)*|x-y| :=
        mul_le_mul_of_nonneg_right hyabs (abs_nonneg _)
  have hn : 0≤Real.sqrt (a^2+y^2)+|x-y| := by positivity
  nlinarith [sq_abs (x-y),Real.sqrt_nonneg (a^2+x^2)]

theorem norm_perturbation (x y x' y' : ℝ) :
    Real.sqrt (x^2+y^2)≤Real.sqrt (x'^2+y'^2)+|x-x'|+|y-y'| := by
  have h1 := norm_coordinate_perturbation x y y'
  have h2 := norm_coordinate_perturbation y' x x'
  rw [add_comm (y'^2) (x^2),add_comm (y'^2) (x'^2)] at h2
  linarith

theorem support_perturbation (x y x' y' : ℝ) :
    NegativeCaptureStress.support x y≤NegativeCaptureStress.support x' y'+
      (5/2)*(|x-x'|+|y-y'|) := by
  have hR0 : 0≤NegativeLargeDECalculus.R := Real.sqrt_nonneg _
  have hQ : qTrial≤4 := by norm_num [qTrial]
  have hR2 : NegativeLargeDECalculus.R≤2 := by
    nlinarith [NegativeLargeDECalculus.radius_sq]
  have hh := mul_le_mul_of_nonneg_left (norm_perturbation x y x' y') hR0
  have hm := mul_le_mul_of_nonneg_right hR2
    (add_nonneg (abs_nonneg (x-x')) (abs_nonneg (y-y')))
  have hx := (abs_le.mp (le_refl |x-x'|)).1
  have hy := (abs_le.mp (le_refl |y-y'|)).1
  dsimp [NegativeCaptureStress.support,NegativeLargeDEStress.support]
  nlinarith

end SquaresInCircles.Eight.TableFree.NegativeCaptureShortAngle
