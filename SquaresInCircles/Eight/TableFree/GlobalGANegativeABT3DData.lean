module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEnvelope

/-!
# The wider signed D envelope required by negative A and positive BT3

Uncompiled Section 3 of the negative-A BT3 note.  The actual sorted
support is unchanged.  Its new constants are k*=.68, alpha=.67 and
C*=1.2.  Positivity is proved only on the branches where it is used;
the reversed mixed quadrant is handled directly by diagonal support.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3

abbrev K : ℝ := 17/25
abbrev Cmax : ℝ := 6/5
abbrev slope : ℝ := 67/100
def vstar (n : ℝ) : ℝ := V R K 1 n

theorem forward_force_positive {c t n : ℝ} (hc : c∈Icc 1 Cmax)
    (ht : t∈Icc 0 frameCap) (hn : n∈Icc 0 frameCap) :
    0<forceA c t (-n) ∧ 0<forceB c t (-n) := by
  have ht' := transport_trig ht
  have hn' := transport_trig hn
  have hs := mul_nonneg (by linarith [hc.1] : 0≤c) ht'.2.2.1
  have hcos := mul_le_mul_of_nonneg_right hc.1 (by linarith [ht'.1] : 0≤Real.cos t)
  dsimp [forceA,forceB]
  rw [Real.cos_neg,Real.sin_neg]
  constructor <;> linarith [ht'.1,hn'.1,hn'.2.2.2.1]

theorem positive_force_positive {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) :
    0<forceA c x y ∧ 0<forceB c x y := by
  have hx' := transport_trig hx
  have hy' := transport_trig hy
  have hs := mul_nonneg (by linarith [hc.1] : 0≤c) hx'.2.2.1
  have hcos := mul_pos (by linarith [hc.1] : 0<c) (by linarith [hx'.1] : 0<Real.cos x)
  dsimp [forceA,forceB]
  constructor <;> linarith [hy'.1,hy'.2.2.1]

theorem negative_force_positive {c n t : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) (ht : t∈Icc 0 n) :
    0<forceA c (-t) (-(n-t)) ∧ 0<forceB c (-t) (-(n-t)) := by
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hn.2⟩
  have hy : n-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1,hn.2]⟩
  have hnt := transport_trig hn
  have htt := transport_trig ht'
  have hyt := transport_trig hy
  have hcos := mul_le_mul_of_nonneg_right hc.1 (by linarith [htt.1] : 0≤Real.cos t)
  have hlast : 0<1-c*Real.sin n := by
    have hm := mul_le_mul_of_nonneg_right hc.2 hnt.2.2.1
    dsimp [Cmax] at hm
    linarith [hnt.2.2.2.1]
  have hf : 0<Real.cos (n-t)-c*Real.sin t := by
    by_cases ht0 : t=0
    · simpa [ht0] using (show 0<Real.cos n by linarith [hnt.1])
    have hst : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne ht.1 (Ne.symm ht0))
      (by dsimp [frameCap] at ht'; linarith [ht'.2,Real.pi_gt_three])
    have hsn : 0<Real.sin n := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ht.2,lt_of_le_of_ne ht.1 (Ne.symm ht0)])
      (by dsimp [frameCap] at hn; linarith [hn.2,Real.pi_gt_three])
    have hid : Real.sin n*(Real.cos (n-t)-c*Real.sin t)=
        Real.cos n*Real.sin (n-t)+(1-c*Real.sin n)*Real.sin t := by
      rw [Real.cos_sub,Real.sin_sub]
      nlinarith [congrArg (fun z : ℝ => z*Real.sin t) (Real.sin_sq_add_cos_sq n)]
    have hfirst := mul_nonneg (by linarith [hnt.1] : 0≤Real.cos n) hyt.2.2.1
    have hsecond := mul_pos hlast hst
    have hprod : 0<Real.sin n*(Real.cos (n-t)-c*Real.sin t) := by linarith
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos hsn.le (le_of_not_gt hh)
    linarith
  dsimp [forceA,forceB]
  simp only [Real.sin_neg,Real.cos_neg]
  exact ⟨by linarith,by linarith [htt.1,hyt.2.2.2.1]⟩

theorem one_angle_lower {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) : vstar n≤D c 0 (-n) := by
  have hp := forward_force_positive (t:=0) hc (by norm_num [frameCap]) hn
  have hsup := sortedSupport_le_clipped hp.1.le hp.2.le
  have hminor := PositiveTD.negative_D_support_minorant
    (k:=K) (c:=c) (by norm_num [K])
    (by constructor <;> dsimp [Cmax,K] at hc ⊢ <;> linarith [hc.1,hc.2]) hn
  have hA : forceA c 0 (-n)=Real.cos n := by
    simp only [forceA,Real.sin_zero,mul_zero,zero_add,Real.cos_neg]
  have hB : forceB c 0 (-n)=c-Real.sin n := by
    simp only [forceB,Real.cos_zero,mul_one,Real.sin_neg]
    ring
  rw [hA,hB] at hsup
  have hclip : clippedSupport 1 c=(1+c)*GlobalGA.Secondary.diagonal := by
    simp only [clippedSupport,hc.1,↓reduceIte,diagonalSupport]
  simp only [PositiveTD.dSupportIncrement,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg,
    hclip] at hminor
  simp only [DEnvelope.vstar,PositiveBT3.D,hA,hB,edgeWidth_zero,sub_self,mul_zero,zero_add]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope
