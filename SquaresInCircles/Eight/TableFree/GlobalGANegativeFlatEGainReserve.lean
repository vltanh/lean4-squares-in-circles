module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEGainData

/-!
# The baseline pays the complete E angle

Uncompiled transcription of Section 4.2 of the negative-flat-E note.
The cosine-multiplied reserve has convex first derivative. Its right
derivative is negative, so its minimum is at an intrinsic endpoint.
Both endpoint reserves are the exact fractions in the hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
open Arithmetic

def F (s : ℝ) : ℝ := (baseline+a-charge*s)*Real.cos s+K*Real.sin s-a
def Fd (s : ℝ) : ℝ := (K-charge)*Real.cos s+(charge*s-baseline-a)*Real.sin s
def Fdd (s : ℝ) : ℝ := (2*charge-K)*Real.sin s+(charge*s-baseline-a)*Real.cos s
def Fddd (s : ℝ) : ℝ := (3*charge-K)*Real.cos s+(baseline+a-charge*s)*Real.sin s

theorem F_hasDerivAt (s : ℝ) : HasDerivAt F (Fd s) s := by
  convert (((((hasDerivAt_id s).const_mul charge).const_sub (baseline+a)).
    mul (Real.hasDerivAt_cos s)).add ((Real.hasDerivAt_sin s).const_mul K)).sub_const a
    using 1 <;> dsimp [F,Fd] <;> ring

theorem Fd_hasDerivAt (s : ℝ) : HasDerivAt Fd (Fdd s) s := by
  convert ((Real.hasDerivAt_cos s).const_mul (K-charge)).add
    (((((hasDerivAt_id s).const_mul charge).sub_const baseline).sub_const a).
      mul (Real.hasDerivAt_sin s)) using 1 <;> dsimp [Fd,Fdd] <;> ring

theorem Fdd_hasDerivAt (s : ℝ) : HasDerivAt Fdd (Fddd s) s := by
  convert ((Real.hasDerivAt_sin s).const_mul (2*charge-K)).add
    (((((hasDerivAt_id s).const_mul charge).sub_const baseline).sub_const a).
      mul (Real.hasDerivAt_cos s)) using 1 <;> dsimp [Fdd,Fddd] <;> ring

theorem Fddd_positive {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<Fddd s := by
  have hc := cosine_pos hs
  have ht := transport_trig hs
  have hfirst : 0<(3*charge-K)*Real.cos s := mul_pos (by norm_num [charge,K]) hc
  have hcoeff : 0≤baseline+a-charge*s := by
    dsimp [baseline,a,charge,frameCap] at *
    linarith [hs.2]
  have hsecond := mul_nonneg hcoeff ht.2.2.1
  dsimp [Fddd]
  linarith

theorem Fd_convex : ConvexOn ℝ (Icc 0 frameCap) Fd := by
  have hh : ConcaveOn ℝ (Icc 0 frameCap) (fun s => -Fd s) :=
    concave_of_deriv2 (fun s _ => (Fd_hasDerivAt s).neg)
      (fun s _ => (Fdd_hasDerivAt s).neg)
      (fun s hs => by linarith [Fddd_positive hs])
  simpa only [neg_neg] using hh.neg

theorem Fd_cap_negative : Fd frameCap<0 := by
  have ht := cap_trig_bounds
  have hp := mul_le_mul_of_nonneg_left ht.2.2.2.2
    (by norm_num [K,charge] : 0≤K-charge)
  have hn := mul_le_mul_of_nonpos_left ht.2.1
    (by norm_num [charge,baseline,a,frameCap] : charge*frameCap-baseline-a≤0)
  have he : (K-charge)*capC8+(charge*frameCap-baseline-a)*capS7=
      -(34023000872689/432000000000000:ℝ) := by
    norm_num [K,charge,baseline,a,capC8,capS7,cos8,sin7,frameCap]
  dsimp [Fd]
  linarith

theorem F_zero : F 0=baseline := by norm_num [F]

theorem F_cap_positive : (1/1000:ℝ)<F frameCap := by
  have ht := cap_trig_bounds
  have hc := mul_le_mul_of_nonneg_left ht.2.2.2.1
    (by norm_num [baseline,a,charge,frameCap] : 0≤baseline+a-charge*frameCap)
  have hs := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num [K] : 0≤K)
  have he : (baseline+a-charge*frameCap)*capC6+K*capS7-a=
      (24007209959/21600000000000:ℝ) := by
    norm_num [baseline,a,charge,K,capC6,capS7,sin7,frameCap]
  dsimp [F]
  linarith

theorem F_positive {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<F s := by
  have hh := SplitConcavityTools.minimum_of_convex_derivative
    (fun s _ => F_hasDerivAt s) Fd_convex Fd_cap_negative.le hs
  have hmin : 0<min (F 0) (F frameCap) := lt_min
    (by rw [F_zero]; norm_num [baseline]) (by linarith [F_cap_positive])
  exact hmin.trans_le hh

theorem baseline_gain_positive {s : ℝ} (hs : s∈Icc 0 frameCap) :
    0<baseline+g s-charge*s := by
  have hc := cosine_pos hs
  have he : Real.cos s*(baseline+g s-charge*s)=F s := by
    dsimp [g,F]
    field_simp [hc.ne']
    ring
  have hh := F_positive hs
  rw [← he] at hh
  exact (mul_pos_iff_of_pos_left hc).1 hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
