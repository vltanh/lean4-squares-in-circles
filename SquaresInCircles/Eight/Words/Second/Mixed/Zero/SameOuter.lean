module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.Data
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveOuter

/-!
# Eight squares: both positive-outer/positive-core zero rows

The original source-secondary separator
forces the angle above `.46`.  A whole-arc lower affine bound for the
outer label then leaves one elementary quadratic in the frame angle.
This includes both core pieces, the arc endpoints and all weak contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.SameOuter
open CommonQuarter CorePairGeometry Arithmetic

lemma original_angle {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) : (23/50:ℝ)<x := by
  have hcut := ShortMixedZero.PositiveOuter.original_cuts hs ht hx hm
  have hp : x∈Icc 0 (7/10) := ⟨by linarith [hcut.1],(abs_le.mp hx).2⟩
  have tr := positive_trig hp
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg tr.2.2.1]
    ring
  have hm' := hm
  norm_num [Eight.forwardMargin] at hm'
  rw [hw,hcut.2.1] at hm'
  have hBc := mul_nonneg (CoreAngleEndpoint.state_bounds ht).2.2.1
    (show 0≤Real.cos x by linarith [tr.1])
  have hb : b<(9/10:ℝ) :=
    (outer_bounds hs).2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2
  by_contra! hn
  have hsine := Real.sin_le hp.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsquare := pow_le_pow_left₀ hp.1 hn 2
  nlinarith

theorem original (r : SameRow) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (17953/20000:ℝ)<x+(sourceLabel r).outer b-outerC r-outerG r*B := by
  have hangle := original_angle hs ht hx hm
  have hp : x∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hx).2⟩
  have tr := positive_trig hp
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg tr.2.2.1]
    ring
  have hm' := hm
  norm_num [Eight.forwardMargin] at hm'
  rw [hw] at hm'
  have hc := CoreAngleEndpoint.state_bounds ht
  have hA := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hg := outer_coefficients r
  have hB := mul_nonneg hc.2.2.1
    (show 0≤Real.cos x-outerG r by linarith [hg.2.1,tr.1])
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hline := source_affine_lower r hb
  have hloss := mul_le_mul_of_nonneg_left
    (show b≤(9/10:ℝ) from hb.2.trans outer_endpoint_bounds.2.2.2.le)
    (show 0≤1-sourceSlope r by linarith [hg.2.2.2])
  have hsine := Real.sin_le hp.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hquad : (11/12:ℝ)*(23/50)-(23/50:ℝ)^2/4≤(11/12)*x-x^2/4 := by
    have hprod := mul_nonneg (show 0≤x-23/50 by linarith)
      (show 0≤11/12-(x+23/50)/4 by linarith [hp.2])
    nlinarith
  rw [source_zero] at hline
  generalize outerG r = G at hB ⊢
  fin_cases r <;> norm_num [sourceSlope,outerC] at hline hloss hquad ⊢ <;>
    nlinarith only [hm',hA,hB,hline,hloss,hsine,hcos,hquad]

end SquaresInCircles.Eight.SecondWord.MixedZero.SameOuter
