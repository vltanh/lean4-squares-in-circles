module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Scalar
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TD
public import SquaresInCircles.Eight.Owners.GA.Positive.ANegativeTDGain

/-!
# Eight squares: the fixed-stress linear reserves used with the E-primary total

These are
the original negative-A secant gain and the nonpositive-T chord,
including their displayed rational reserves after the angular charge.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PairedE
open Candidate Secondary

theorem negative_A_linear {s a b : ℝ} (hs : s∈Icc 0 frameCap)
    (ha : 447/800≤a) (hb : b≤283/200) :
    (71983/1000000)*s≤NegativePrimary.primaryIncrement (-s) a b := by
  have ht := transport_trig hs
  have hc : 0<Real.cos s := by linarith [ht.1]
  have hsin := ht.2.2.1
  have hcos : 0≤1-Real.cos s := sub_nonneg.mpr (Real.cos_le_one s)
  have hhalf := PositiveANegativeTD.one_sub_cos_upper hs
  have htan := PositiveANegativeTD.sine_ge_angle_cos hs
  have hap := mul_le_mul_of_nonneg_right ha hsin
  have hbp := mul_le_mul_of_nonneg_right hb hcos
  have hnum : (1121983/1000000)*s*Real.cos s≤
      l*((a+1/2)*Real.sin s+(1/2-b)*(1-Real.cos s)) := by
    norm_num [l]
    nlinarith only [hap,hbp,hhalf,htan]
  have hid : NegativePrimary.primaryIncrement (-s) a b*Real.cos s=
      l*((a+1/2)*Real.sin s+(1/2-b)*(1-Real.cos s))-
        Secondary.charge*s*Real.cos s := by
    rw [NegativePrimary.primaryIncrement,edgeWidth_negative_formula hs]
    simp only [Real.sin_neg,Real.cos_neg]
    field_simp [hc.ne']
    ring
  refine le_of_mul_le_mul_right ?_ hc
  rw [hid]
  dsimp [Secondary.charge]
  linarith

theorem negative_A_linear_signed {d a b : ℝ} (hd : d≤0)
    (hsmall : |d|≤frameCap) (ha : 447/800≤a) (hb : b≤283/200) :
    (71983/1000000)*(-d)≤NegativePrimary.primaryIncrement d a b := by
  simpa only [neg_neg] using negative_A_linear
    (show -d∈Icc 0 frameCap from ⟨neg_nonneg.mpr hd,(neg_le_abs d).trans hsmall⟩) ha hb

theorem phi_chord {w : ℝ} (hw : w∈Icc 0 frameCap) :
    (409/700)*w≤Real.sin w+Real.cos w-1 := by
  let f : ℝ→ℝ := fun x => Real.sin x+Real.cos x-1-(409/700)*x
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) f := by
    apply concave_of_deriv2
      (f':=fun x => Real.cos x-Real.sin x-409/700)
      (f'':=fun x => -Real.sin x-Real.cos x)
    · intro x hx
      have h : HasDerivAt (fun x => Real.sin x+Real.cos x-1-(409/700)*x)
          (Real.cos x+-Real.sin x-0-(409/700)*1) x :=
        ((((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).sub
          (hasDerivAt_const x (1:ℝ))).sub ((hasDerivAt_id x).const_mul (409/700)))
      exact h.congr_deriv (by ring)
    · intro x hx
      have h : HasDerivAt (fun x => Real.cos x-Real.sin x-409/700)
          (-Real.sin x-Real.cos x-0) x :=
        ((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).sub
          (hasDerivAt_const x (409/700:ℝ))
      exact h.congr_deriv (by ring)
    · intro x hx
      have ht := transport_trig hx
      linarith [ht.1,ht.2.2.1]
  have hz : 0≤f 0 := by norm_num [f]
  have hh : 0≤f frameCap := by
    have hs := sin_lower_seven (x:=frameCap) (by norm_num [frameCap])
    have hc := cos_lower_six (x:=frameCap) (by norm_num [frameCap])
    simp only [f,frameCap] at hs hc ⊢
    norm_num at hs hc ⊢
    linarith
  have hm := hconc.min_le_of_mem_Icc (by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hw
  have hf := (le_min hz hh).trans hm
  dsimp [f] at hf
  linarith

theorem nonpositive_T_linear {z : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hcore : P.AvoidsCore)
    (hz : z≤0) (hsmall : |z|≤frameCap) :
    (83/700)*(-z)≤tdIncrement z P := by
  let w := -z
  have hw : w∈Icc 0 frameCap := ⟨neg_nonneg.mpr hz,(neg_le_abs z).trans hsmall⟩
  have ht := transport_trig hw
  have hphi := phi_chord hw
  have hphi0 : 0≤Real.sin w+Real.cos w-1 := by nlinarith [hw.1]
  have hhalf := SignedPoint.primary_gt_half hs hcore
  have hy := mul_le_mul_of_nonpos_right (abs_le.mp hs.2).1
    (show Real.cos w-1≤0 by linarith [ht.2.1])
  have hp := mul_nonneg (show 0≤P.a-1/2 by linarith) hphi0
  have hz' : z= -w := by dsimp [w]; ring
  rw [tdIncrement,hz',edgeWidth_negative_formula hw]
  simp only [Real.sin_neg,Real.cos_neg]
  dsimp [GlobalGA.Secondary.charge,w] at *
  nlinarith

end SquaresInCircles.Eight.GlobalGA.PairedE
