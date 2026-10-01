import SquaresInCircles.Six.Analytic.DiagonalCoreBounds

/-!
# Separation along the secondary axis of D at a small angle

Let a square lie in the disk and outside the core disk, with centre `(a, b)` in
its frame, and let `0 ≤ q ≤ π/4`. Then
`a sin q - b cos q ≤ aMin sin q + U0 cos q`: over the centres allowed by the
disk and the core, the maximum is at the corner `(aMin, U0)` where the line
`a = aMin` meets the circle, since `R0 sin q ≤ 5/2 - rho0`. With the bound
`|b_D| < 229/1000` on the transverse coordinate of D, it follows that W or S,
at an angle `q` from D, is not separated from D along the secondary axis of D
(`nonnegative_W_Dsecondary_excluded`).
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma quarter_trig_bounds {q : ℝ} (hq : 0≤q ∧ q≤Real.pi/4) :
    0≤Real.sin q ∧ 0≤Real.cos q ∧ Real.sin q≤Real.cos q ∧ Real.sin q≤3/4 := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hq.1 (by linarith [hq.2,Real.pi_pos])
  have hc0 : 0≤Real.cos q := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hq.1,Real.pi_pos],by linarith [hq.2,Real.pi_pos]⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤q by linarith [hq.1,Real.pi_pos])
    (show Real.pi/4≤Real.pi/2 by linarith [Real.pi_pos]) hq.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hq.1
    (show Real.pi/4≤Real.pi by linarith [Real.pi_pos]) hq.2
  rw [Real.sin_pi_div_four] at hs
  rw [Real.cos_pi_div_four] at hc
  have hroot : Real.sqrt (2:ℝ)/2≤3/4 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  exact ⟨hs0,hc0,hs.trans hc,hs.trans hroot⟩

lemma core_secondary_projection {a b q : ℝ}
    (hc : ContainedChart a |b|) (hcore : AvoidsCore a |b|)
    (hq : 0≤q ∧ q≤Real.pi/4) :
    a*Real.sin q-b*Real.cos q≤aMin*Real.sin q+U0*Real.cos q := by
  let l := 5/2-rho0
  have hl : 0<l := by dsimp [l]; linarith [rho0_upper]
  have ha : l≤a+1/2 := by
    have hh := hc.aMin_le hcore
    dsimp [l,aMin] at *
    linarith
  have ht := quarter_trig_bounds hq
  have hp := mul_le_mul R0_lt_1689_1000.le ht.2.2.2 ht.1
    (by norm_num : (0:ℝ)≤1689/1000)
  have hbranch : R0*Real.sin q≤l := by dsimp [l]; nlinarith [rho0_upper]
  have hbox : (a+1/2)^2+(|-b|+1/2)^2≤Q0 := by simpa only [abs_neg] using hc.containment
  have h := circle_support_above_primary hl ha hbox ht.1 ht.2.1
    (Real.sin_sq_add_cos_sq q) hbranch
  dsimp [l,aMin,U0] at h ⊢
  nlinarith only [h]

lemma nonnegative_W_Dsecondary_excluded {a b bd q : ℝ}
    (hc : ContainedChart a |b|) (hcore : AvoidsCore a |b|)
    (hq : 0≤q ∧ q≤Real.pi/4) (hbd : bd<229/1000) :
    a*Real.sin q-b*Real.cos q+bd<1/2+angularWidth q := by
  have ht := quarter_trig_bounds hq
  have hproj := core_secondary_projection hc hcore hq
  have hamin : aMin≤89/100 := by dsimp [aMin]; linarith [rho0_lower]
  have hA := mul_le_mul_of_nonneg_right hamin ht.1
  have hB := mul_le_mul_of_nonneg_right normalization_transverse_upper_sharp.le ht.2.1
  rw [angularWidth,abs_of_nonneg ht.2.1,abs_of_nonneg ht.1]
  nlinarith only [hproj,hA,hB,hbd,ht.2.2.1,ht.2.2.2]

end SquaresInCircles.Six.Analytic
