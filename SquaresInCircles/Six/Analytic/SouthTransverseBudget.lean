module
public import SquaresInCircles.Six.Analytic.SmallDiagonalSecondary

@[expose] public section

/-!
# The signed S transverse budget in the unchanged normalized frame

This is the exact coordinate counterpart of the negative-W estimate. Only
scalar identities are reflected: neither the packing nor D's chosen half-window
is changed. OWN and cardinal cases retain their actual central-separator
hypotheses. The resulting W/S difference bound is necessary, not a proof of
the still-missing individual angle tails or candidate D-edge classification.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma south_own_as_west (s a b cx cy : ℝ) :
    centralMargin .own (Real.pi-s) a (-b) cy cx =
      centralMargin .own (3*Real.pi/2+s) a b cx cy := by
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    Real.cos_add,Real.sin_add,south_cos,south_sin,zero_mul,one_mul,neg_one_mul,
    zero_add,add_zero,abs_neg]
  ring

lemma south_cardinal_as_west (s a b cx cy : ℝ) :
    centralMargin .west (Real.pi-s) a (-b) cy cx =
      centralMargin .south (3*Real.pi/2+s) a b cx cy := by
  simp only [centralMargin,centerX,centerY,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    Real.cos_add,Real.sin_add,south_cos,south_sin,zero_mul,one_mul,neg_one_mul,
    zero_add,add_zero,abs_neg]
  ring

/-- Positive S tilt consumes its positive transverse reserve, for either
central bit. No D-edge source is used to establish the budget. -/
theorem normalized_south_transverse_budget {R : ℝ} (P : NormalizedPacking R) :
    P.transverse 4 < 47/100-(2/3)*max (P.helperAngle 4) 0 := by
  by_cases hs : P.helperAngle 4 ≤ 0
  · rw [max_eq_right hs,mul_zero,sub_zero]
    have hb := (P.contained 4).u_le_U0 (P.avoidsCore 4)
    linarith [le_abs_self (P.transverse 4),U0_lt_117_250]
  · have hs0 : 0 ≤ P.helperAngle 4 := le_of_not_ge hs
    rw [max_eq_left hs0]
    have hphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
    have hc : ContainedChart (P.radial 4) |-(P.transverse 4)| := by
      simpa only [abs_neg] using P.contained 4
    cases hbit : P.ownBits 4
    · have hangle := abs_lt.mp (P.cardinal_angle 4 hbit)
      have hcard : 0 ≤ centralMargin .west (Real.pi-P.helperAngle 4)
          (P.radial 4) (-P.transverse 4) P.center.2 P.center.1 := by
        rw [south_cardinal_as_west,← hphase]
        exact P.cardinal_separator 4 hbit
      have h := cardinal_west_negative_transverse hc P.box.2.2
        ⟨hs0,hangle.2.le⟩ hcard
      simpa only [neg_neg] using h
    · have hown : 0 ≤ centralMargin .own (Real.pi-P.helperAngle 4)
          (P.radial 4) (-P.transverse 4) P.center.2 P.center.1 := by
        rw [south_own_as_west,← hphase]
        exact P.own_separator 4 hbit
      have h := own_west_negative_transverse hc P.box.2.2 P.box.1.1
        ⟨hs0,P.helper_windows.2.2.2.2.le⟩ hown
      rw [abs_neg] at h
      exact (le_abs_self _).trans_lt h

/-- The two one-sided budgets combine with their correct signs. This is the
signed difference consumed by D-edge work, not an absolute-value surrogate. -/
theorem normalized_wing_transverse_difference {R : ℝ} (P : NormalizedPacking R) :
    P.transverse 4-P.transverse 2 < 47/50-
      (2/3)*(max (-P.helperAngle 2) 0+max (P.helperAngle 4) 0) := by
  have hw := normalized_west_transverse_budget P
  have hs := normalized_south_transverse_budget P
  linarith

end SquaresInCircles.Six.Analytic
