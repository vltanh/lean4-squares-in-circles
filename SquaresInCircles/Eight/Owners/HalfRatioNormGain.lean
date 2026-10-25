module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Sole.NormGain

/-!
# Eight squares: monotonicity of the norm gain on the entire half-ratio cone

The exact squared comparison only needs
2r >= z(1+r²). On r in [1/2,1] and z in [0,.7] this follows
from a single quadratic inequality. Thus the coefficient comparison
also applies at the frame cap when r is smaller than sin(.7).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HalfRatioNormGain
open SoleNormGain VaryingBFunctions VaryingBComparison
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope

theorem gain_nonnegative {r z : ℝ} (hr : r∈Icc (1/2:ℝ) 1)
    (hz : z∈Icc 0 frameCap) : 0≤gain r z := by
  have hS := OrdinaryCurvatureBounds.shape_pos r
  have hN := root_pos r hz
  have hS2 := OrdinaryCurvatureBounds.shape_sq r
  have hN2 := root_sq r hz
  have hz7 : z≤7/10 := hz.2
  have hr0 : 0≤r := by linarith [hr.1]
  have hr2 : r^2≤(3/2)*r-1/2 := by
    nlinarith [mul_nonneg (show 0≤r-1/2 by linarith [hr.1]) (sub_nonneg.mpr hr.2)]
  have hinner : 0≤2*r-z*(1+r^2) := by
    have hm := mul_le_mul_of_nonneg_right hz7 (show 0≤1+r^2 by positivity)
    nlinarith [hr.1]
  have hnum : 0≤1-r*z := by
    have hm := mul_le_mul hr.2 hz7 hz.1 (by norm_num : (0:ℝ)≤1)
    nlinarith
  have hp := mul_nonneg (mul_nonneg (sq_nonneg r) hz.1) hinner
  have hid : (root r z)^2-((1-r*z)*OrdinaryCurvatureBounds.shape r)^2=
      r^2*z*(2*r-z*(1+r^2)) := by
    rw [mul_pow,hS2,hN2]
    ring
  have hcomp : (1-r*z)*OrdinaryCurvatureBounds.shape r≤root r z := by
    rw [← hid] at hp
    exact (pow_le_pow_iff_left₀ (mul_nonneg hnum hS.le) hN.le two_ne_zero).1 (by linarith)
  have hdiv : (1-r*z)/root r z≤1/OrdinaryCurvatureBounds.shape r := by
    apply (div_le_div_iff₀ hN hS).2
    simpa only [one_mul] using hcomp
  dsimp [gain]
  linarith

theorem larger_monotone {R p a b s : ℝ}
    (hR : 0≤R) (hp : 0<p) (hpa : p≤a) (hab : a≤b) (hbp : b≤2*p)
    (hs : s∈Icc 0 frameCap) : normGain R p a s≤normGain R p b s := by
  have ha : 0<a := hp.trans_le hpa
  have hx (x : ℝ) (hxx : x∈Icc a b) : 0<x ∧ p/x∈Icc (1/2:ℝ) 1 := by
    have hxp : 0<x := ha.trans_le hxx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_one hxp).2 (hpa.trans hxx.1)⟩⟩
    linarith [hxx.2]
  have hmono : MonotoneOn (fun x => normGain R p x s) (Icc a b) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hxx
      exact (normGain_hasDerivAt_large hp (hx x hxx).1 hs).continuousAt.continuousWithinAt
    · intro x hxx
      exact normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs
    · intro x hxx
      exact mul_nonneg hR (gain_nonnegative (hx x (Ioo_subset_Icc_self hxx)).2 (sin_mem hs))
  exact hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

end SquaresInCircles.Eight.HalfRatioNormGain
