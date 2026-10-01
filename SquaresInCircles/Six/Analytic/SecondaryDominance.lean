import SquaresInCircles.Six.Analytic.PrimaryCosineBound
import SquaresInCircles.Six.Analytic.HighDiagonalProfile

/-!
# A secondary separator can replace a primary one on the D/S first quadrant

Small gaps exclude the primary axes outright. For larger gaps up to pi/2,
(1-sin q)<=2 cos q/5 and the high-D radial/transverse bounds show that each
primary work is no greater than one of the two forward secondary works.
Thus the required result is existence of a secondary separator; a primary
need not be falsely declared impossible when it ties one at q=pi/2.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma large_gap_cosine_ratio {q : ℝ} (hq : 11/10≤q ∧ q≤Real.pi/2) :
    0≤Real.cos q ∧ 0≤1-Real.sin q ∧ 1-Real.sin q≤(2/5)*Real.cos q := by
  have hc := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],hq.2⟩
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(11:ℝ)/10 by linarith [Real.pi_pos]) hq.2 hq.1
  have hl := Real.sin_ge_sub_cube (x := (11:ℝ)/10) (by norm_num)
  norm_num at hl
  have hs : 4/5≤Real.sin q := by linarith
  have hs1 : 0≤1-Real.sin q := sub_nonneg.mpr (Real.sin_le_one q)
  have hfactor := mul_nonneg hs1 (show 0≤29*Real.sin q-21 by linarith)
  have hsq : (5*(1-Real.sin q))^2≤(2*Real.cos q)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq q]
  refine ⟨hc,hs1,?_⟩
  by_contra! h
  have hp := mul_pos
    (show 0<5*(1-Real.sin q)-2*Real.cos q by linarith)
    (show 0<5*(1-Real.sin q)+2*Real.cos q by linarith)
  nlinarith

/-- The inward D-primary work is bounded by the forward S-secondary work. -/
lemma inward_Dprimary_le_Ssecondary {a b A B q : ℝ}
    (ha : a≤rho0) (hb : |b|≤23/100) (hA : aMin≤A) (hB : |B|≤U0)
    (hq : 11/10≤q ∧ q≤Real.pi/2) :
    a-A*Real.cos q+B*Real.sin q≤B+a*Real.sin q-b*Real.cos q := by
  obtain ⟨hc,hs0,hratio⟩ := large_gap_cosine_ratio hq
  have hlow : 657/1000≤A-b := by
    have hbb := (abs_le.mp hb).2
    dsimp [aMin] at hA
    linarith [rho0_upper]
  have hhigh : a-B≤1581/1000 := by
    have hBB := (abs_le.mp hB).1
    linarith [rho0_upper,U0_lt_117_250]
  have h1 := mul_nonneg (sub_nonneg.mpr hlow) hc
  have h2 := mul_nonneg (sub_nonneg.mpr hhigh) hs0
  have h3 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0:ℝ)≤1581/1000)
  nlinarith only [h1,h2,h3,hc]

/-- The destination S-primary work is bounded by the forward D-secondary work. -/
lemma Sprimary_le_Dsecondary {a b A B q : ℝ}
    (ha : 128/125≤a) (hb : |b|≤23/100) (hA : A≤rho0) (hB : |B|≤U0)
    (hq : 11/10≤q ∧ q≤Real.pi/2) :
    A-a*Real.cos q-b*Real.sin q≤A*Real.sin q+B*Real.cos q-b := by
  obtain ⟨hc,hs0,hratio⟩ := large_gap_cosine_ratio hq
  have hlow : 139/250≤a+B := by
    have hBB := (abs_le.mp hB).1
    linarith [U0_lt_117_250]
  have hhigh : A+b≤1343/1000 := by
    have hbb := (abs_le.mp hb).2
    linarith [rho0_upper]
  have h1 := mul_nonneg (sub_nonneg.mpr hlow) hc
  have h2 := mul_nonneg (sub_nonneg.mpr hhigh) hs0
  have h3 := mul_le_mul_of_nonneg_left hratio (by norm_num : (0:ℝ)≤1343/1000)
  nlinarith only [h1,h2,h3,hc]

end SquaresInCircles.Six.Analytic
