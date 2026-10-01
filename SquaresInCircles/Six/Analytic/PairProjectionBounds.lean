import SquaresInCircles.Six.Normalization.CenterRadius

/-!
# Uniform projection estimates for the W/D ordering argument

The primary estimate uses the center-radius bound and the single rational
inequality (277/200)(1519/3200) > 1113/1000-1/2. The cosine lower bound
1519/3200 is exactly 1-(41/40)^2/2.

The forward transverse estimate uses |b|,|B| <= 117/250 < 1/2. There are no
support-branch choices and no scalar checks indexed by a partition.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma primary_projection_bound {A B a c s : ℝ}
    (hchart : ContainedChart A |B|)
    (hA : 177/200 ≤ A) (hB : |B| ≤ 1/2)
    (ha0 : 177/200 ≤ a) (ha1 : a ≤ rho0)
    (hc : 1519/3200 ≤ c) (hunit : c^2+s^2=1) :
    |A*c+B*s-a| < 1/2+(c+|s|)/2 := by
  have hc0 : 0 ≤ c := by linarith
  have hp := projection_abs_le_rho0 (chart_center_radius_sq hchart) hunit
  have hpu := (abs_le.mp hp).2
  have hBs : -(|B| *|s|) ≤ B*s := by
    have h := neg_le_abs (B*s)
    rw [abs_mul] at h
    linarith
  have hBu := mul_le_mul_of_nonneg_right hB (abs_nonneg s)
  have hAc := mul_le_mul_of_nonneg_right
    (show (277:ℝ)/200 ≤ A+1/2 by linarith) hc0
  have hC := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 277/200 by norm_num)
  have hnum : (1113:ℝ)/1000-1/2 < (277/200)*(1519/3200) := by norm_num
  apply abs_lt.mpr
  constructor
  · nlinarith only [hBs,hBu,hAc,hC,hnum,ha1,rho0_upper]
  · nlinarith only [hpu,ha0,rho0_upper,hc0,abs_nonneg s]

lemma forward_transverse_bound {A B b c s : ℝ}
    (hA : 0 ≤ A) (hB : |B| ≤ 117/250) (hb : |b| ≤ 117/250)
    (hc : 0 ≤ c) (hs : 0 ≤ s) :
    -A*s+B*c-b < 1/2+(c+s)/2 := by
  have hAv := mul_nonneg hA hs
  have hBc := mul_le_mul_of_nonneg_right ((le_abs_self B).trans hB) hc
  have hbm := (neg_le_abs b).trans hb
  nlinarith only [hAv,hBc,hbm,hc,hs]

lemma reversed_phase_trig {e : ℝ} (he : 0 ≤ e ∧ e ≤ 41/40) :
    (1519/3200 ≤ Real.cos e) ∧ 0 ≤ Real.sin e ∧
      (Real.cos e)^2+(Real.sin e)^2=1 := by
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  refine ⟨?_,?_,?_⟩
  · nlinarith [Real.one_sub_sq_div_two_le_cos (x := e)]
  · exact Real.sin_nonneg_of_nonneg_of_le_pi he.1 (by linarith [he.2,Real.pi_gt_d2])
  · nlinarith [Real.sin_sq_add_cos_sq e]

end SquaresInCircles.Six.Analytic
