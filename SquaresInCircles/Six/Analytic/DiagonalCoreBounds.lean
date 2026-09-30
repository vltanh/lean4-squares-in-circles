import SquaresInCircles.Six.Analytic.SmallDiagonalCardinalExclusion

/-!
# Quantitative D bounds after the analytic d>1/2 reduction

On [1/2,pi/4], cos d+sin d is increasing. D's actual OWN separator therefore
imposes the radial profile at 1/2 throughout this interval. The previous
whole-interval scalar profile then gives |bD|<229/1000, and an explicit Taylor
endpoint gives aD>41/40. Neither conclusion assumes a final D-edge source.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma own_front_profile_quarter {a b cx cy d : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (hd : 0≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    1+(387/1000)*(Real.cos d+Real.sin d)≤a+1/2 := by
  have hc0 : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1 (by linarith [hd.2,Real.pi_pos])
  have hcx : 0≤1/2-cx-387/1000 := by dsimp [c0] at hx; linarith [rho0_upper]
  have hcy : 0≤1/2-cy-387/1000 := by dsimp [c0] at hy; linarith [rho0_upper]
  have hX := mul_nonneg hcx hc0
  have hY := mul_nonneg hcy hs0
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
    abs_neg,abs_of_nonneg hc0,abs_of_nonneg hs0] at hown
  nlinarith only [hown,hX,hY]

lemma own_profile_at_half {a b cx cy d : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    1+(387/1000)*(Real.cos (1/2)+Real.sin (1/2))≤a+1/2 := by
  have hprofile := own_front_profile_quarter hx hy ⟨by linarith [hd.1],hd.2⟩ hown
  have hmono := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  nlinarith only [hprofile,hmono]

lemma own_radial_after_half {a b cx cy d : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) : 41/40<a := by
  have hprofile := own_profile_at_half hx hy hd hown
  have hs := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  have hc := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  nlinarith only [hprofile,hs,hc]

lemma own_transverse_after_half {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy : cy≤c0)
    (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) : |b|<229/1000 := by
  have hprofile := own_profile_at_half hx hy hd hown
  have h := sharp_front_transverse (d := (1:ℝ)/2) (by constructor <;> norm_num)
    hprofile hc.containment
  nlinarith only [h]

/-- These bounds are outputs for every actual normalized packing. -/
theorem normalized_diagonal_core_bounds {R : ℝ} (P : NormalizedPacking R) :
    1/2<P.diagonalAngle ∧ 41/40<P.radial 3 ∧ |P.transverse 3|<229/1000 := by
  have hd := normalized_diagonal_gt_half P
  have hphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hown := P.own_separator 3 P.diagonal_own
  rw [hphase] at hown
  have hrange := And.intro hd.le P.diagonal_angle_range.2
  exact ⟨hd,own_radial_after_half P.box.1.2 P.box.2.2 hrange hown,
    own_transverse_after_half (P.contained 3) P.box.1.2 P.box.2.2 hrange hown⟩

end SquaresInCircles.Six.Analytic
