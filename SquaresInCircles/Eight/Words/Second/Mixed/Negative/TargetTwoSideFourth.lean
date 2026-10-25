module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoSideDiscriminant

/-!
# Eight squares: one global negative fourth derivative for the side discriminant

The positive double-angle harmonic is concave on the whole interval.
Its two endpoints supply the uniform reserve that dominates every
positive term of the fourth derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
open CommonQuarter CorePairGeometry Arithmetic

def pay (x : ℝ) : ℝ := -16*C*Real.cos (2*x)+(3093051/250000)*Real.sin (2*x)
def payD (x : ℝ) : ℝ := 32*C*Real.sin (2*x)+(3093051/125000)*Real.cos (2*x)

lemma pay_hasDerivAt (x : ℝ) : HasDerivAt pay (payD x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (hc.const_mul (-16*C)).add (hs.const_mul (3093051/250000)) using 1
  · funext y
    simp only [pay,Pi.add_apply,Function.comp_apply]
  · dsimp [payD]
    ring

lemma payD_hasDerivAt (x : ℝ) : HasDerivAt payD (-4*pay x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (hs.const_mul (32*C)).add (hc.const_mul (3093051/125000)) using 1
  · funext y
    simp only [payD,Pi.add_apply,Function.comp_apply]
  · dsimp [pay]
    ring

lemma double_trig {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0≤Real.sin (2*x) ∧ 0≤Real.cos (2*x) :=
  ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) (by linarith [hx.2,pi_hand_enclosure.1]),
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,pi_hand_enclosure.1]⟩⟩

lemma pay_nonnegative {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : 0≤pay x := by
  have hp := mul_nonneg (show 0≤ -16*C by linarith [C_bounds.2]) (double_trig hx).2
  have hq := mul_nonneg (by norm_num : (0:ℝ)≤3093051/250000) (double_trig hx).1
  dsimp [pay]
  linarith

lemma pay_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : (51/25:ℝ)<pay x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (7/10)) pay :=
    concave_of_deriv2 (fun x _ => pay_hasDerivAt x) (fun x _ => payD_hasDerivAt x)
      (fun x hx => by linarith [pay_nonnegative hx])
  apply concave_gt_of_endpoints hc hx
  · norm_num [pay]
    linarith [C_bounds.2]
  · have hs := HighOrderTaylor.S15_le_sin (x := (7/5:ℝ)) (by norm_num)
    norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7] at hs
    have hp := mul_nonneg (show 0≤ -16*C by linarith [C_bounds.2])
      (double_trig (show (7/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)).2
    norm_num [pay]
    norm_num at hp
    linarith

theorem fourth_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : E4 x<0 := by
  have hpay := pay_lower hx
  have ht := positive_trig hx
  have hA := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (show 0≤A by norm_num [A])
  have hB := mul_nonpos_of_nonpos_of_nonneg (show B≤0 by norm_num [B]) ht.2.2.1
  have hlast := mul_nonneg hx.1 (double_trig hx).2
  dsimp [E4,pay,A,B,H,q] at *
  nlinarith

lemma third_antitone : AntitoneOn E3 (Icc (0:ℝ) (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun x _ => (E3_hasDerivAt x).continuousAt.continuousWithinAt)
    (fun x _ => E3_hasDerivAt x)
    (fun x hx => (fourth_negative (Ioo_subset_Icc_self hx)).le)

end SquaresInCircles.Eight.SecondWord.MixedTwo.NegativeTarget.Side
