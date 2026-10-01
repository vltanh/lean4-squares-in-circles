import SquaresInCircles.Six.Analytic.FrozenTrigStress
import SquaresInCircles.Six.Analytic.SharpFrontProfile
import SquaresInCircles.Six.Stress.Support
import SquaresInCircles.Six.Analytic.TransverseProfileBounds
import SquaresInCircles.Six.Analytic.ConstrainedCircleSupport
import SquaresInCircles.Six.Analytic.PrimaryClassification
import SquaresInCircles.Six.Analytic.DiagonalHalfBound

/-!
# The coordinates of D

In a normalized packing D is separated from C along its own axis, at phase
`π + d` with `1/2 < d ≤ π/4`. For `0 ≤ d ≤ π/4` that separation and the box of
the centre of C give the radial profile
`1 + (387/1000)(cos d + sin d) ≤ a + 1/2`, and `cos d + sin d` increases on
`[1/2, π/4]`, so the profile holds with `d = 1/2`. Taylor bounds at `1/2` then
give `a > 41/40`, and the containment of D in the disk gives `|b| < 229/1000`.
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
  have e1 : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
  have e2 : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
  simp only [centralMargin,centralNormal,angularWidth,e1,e2,
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

/-- In a normalized packing, D has angle `d > 1/2`, radial coordinate more than
`41/40` and transverse coordinate less than `229/1000` in absolute value. -/
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
