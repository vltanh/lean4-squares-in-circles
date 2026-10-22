module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowGConstants

/-!
# The low negative-DE same-block alternatives

Uncompiled transcription of Section 6, equations (33)--(34), of the
angle companion. The G same-block term is differentiated at the actual
E magnitude, with both signed budgets retained. The H and B terms use
the stated exact same-block surplus inequalities, including zero mass.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSame
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds
open NegativeAPositiveTD (Curvature)

theorem sine_linear {t : ℝ} (ht : t∈Icc 0 frameCap) : (23/25)*t≤Real.sin t := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) frameCap) (fun x => Real.sin x-(23/25)*x) := by
    apply concave_of_deriv2
      (fun x _ => (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).const_mul (23/25)))
      (fun x _ => (Real.hasDerivAt_cos x).sub_const (23/25))
    intro x hx
    exact neg_nonpos.mpr (transport_trig hx).2.2.1
  have hh := hc.min_le_of_mem_Icc (by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  have hcap : 0≤Real.sin frameCap-(23/25)*frameCap := by
    have hs := OrdinaryNegativeEnvelope.cap_sin_lower
    norm_num [frameCap]
    linarith
  simp only [Real.sin_zero,mul_zero,sub_zero,min_eq_left hcap] at hh
  linarith

def ordinary (θ s : ℝ) : ℝ := mixedBlock R (Explicit.k .low θ) (Explicit.l .low θ)
  (frameCap-θ) (frameCap-s)
def ordinaryFirst (θ s : ℝ) : ℝ :=
  Explicit.l .low θ*Real.sin (frameCap-s)-
    R*normD1 (Explicit.k .low θ) (Explicit.l .low θ) (s-θ)

theorem ordinary_hasDerivAt {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 frameCap) : HasDerivAt (ordinary θ) (ordinaryFirst θ s) s := by
  have hr := Explicit.low_ranges hθ
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hh := (mixedN_hasDerivAt (by linarith [hr.1] : 0<Explicit.k .low θ)
    (by linarith [hr.2.2.1] : 0<Explicit.l .low θ) hP hN).comp s
    ((hasDerivAt_id s).const_sub frameCap)
  convert hh using 1
  · rfl
  · dsimp [ordinaryFirst,mixedNDerivative]
    rw [show frameCap-θ-(frameCap-s)=s-θ by ring]
    ring

theorem combined_derivative_positive {θ s D : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap)
    (hD : (209/200:ℝ)<D) : 0<D+ordinaryFirst θ s := by
  have hr := Explicit.low_ranges hθ
  have hk : 0<Explicit.k .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
  have hkl : Explicit.k .low θ≤Explicit.l .low θ := by linarith [hr.2.1,hr.2.2.1]
  have hqp : Explicit.l .low θ≤2*Explicit.k .low θ := hr.2.2.2.2.2.2.2.le
  have ht : |s-θ|≤frameCap := by
    rw [abs_le]
    constructor <;> norm_num [frameCap] at * <;> linarith [hs.1,hs.2,hθ.1,hθ.2]
  have hn := Curvature.norm_slope_signed_tangent hk hl ht
  have hzero := LowG.zero_slope_upper hθ
  have hC := LowG.curvature_lower hθ
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  by_cases horder : θ≤s
  · have hcurv := mul_le_mul_of_nonneg_right hC.le (sub_nonneg.mpr horder)
    have hsin := sine_linear hN
    have hlower := mul_le_mul_of_nonneg_right hr.2.2.1.le (transport_trig hN).2.2.1
    have hslope : R*normD1 (Explicit.k .low θ) (Explicit.l .low θ) (s-θ)<
        131/100-(s-θ)/2 := by nlinarith only [hn,hzero,hcurv]
    dsimp [ordinaryFirst]
    norm_num [frameCap] at hsin hN hs
    nlinarith [hθ.2]
  · have hCupper := (Curvature.universal_constants hk hkl hqp).1
    have hCmax : curvatureZero R (Explicit.k .low θ) (Explicit.l .low θ)<1183/1250 := by
      linarith [hr.2.2.2.1]
    have hprod := mul_le_mul hCmax.le
      (show θ-s≤1/6 by linarith [hθ.2,hs.1])
      (show 0≤θ-s by linarith) (by norm_num : (0:ℝ)≤1183/1250)
    have hsin : (127/250:ℝ)<Real.sin (frameCap-s) := by
      have hinterval : frameCap-s∈Icc (8/15:ℝ) frameCap := by
        dsimp [frameCap] at *
        exact ⟨by linarith [hθ.2],hN.2⟩
      have hh := trig_bracket (l:=(8/15:ℝ)) (u:=frameCap)
        (by norm_num) (by norm_num [frameCap]; linarith [Real.pi_gt_three]) hinterval
      norm_num [frameCap] at hh
      linarith [hh.1]
    have hlower := mul_le_mul_of_nonneg_right hr.2.2.1.le (transport_trig hN).2.2.1
    dsimp [ordinaryFirst]
    nlinarith

theorem correction_same_monotone {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => LowD.correction (Explicit.c .low θ) s+ordinary θ s)
      (Icc (0:ℝ) frameCap) := by
  have hr := Explicit.low_ranges hθ
  apply LowD.add_monotone
    (show 1≤Explicit.c .low θ by linarith [hr.2.2.2.2.1]) le_rfl le_rfl
    (fun s hs => ordinary_hasDerivAt hθ hs)
  · intro s hs _
    exact (combined_derivative_positive hθ hs (LowD.diagonal_derivative_lower hs)).le
  · intro s hs _
    exact (combined_derivative_positive hθ hs
      (LowD.full_derivative_lower
        (show (519/500:ℝ)≤Explicit.c .low θ by linarith [hr.2.2.2.2.1]) hs)).le

def zeroEnvelope (a z : ℝ) : ℝ :=
  Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z)+
    Explicit.k .low (a+z)*(phi (frameCap-(a+z))-1)+
    Explicit.l .low (a+z)*(Real.cos frameCap-Real.cos (a+z))

theorem original_zero_lower {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 (a+z))
    (hs : s∈Icc 0 frameCap) :
    zeroEnvelope a z≤Explicit.baseline .low a z s+ordinary (a+z) s := by
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hm := correction_same_monotone hθ hzero hs hs.1
  have hG := LowNegative.pure_comparison hθ hz ⟨hθ.1,le_rfl⟩ (1:Fin 3)
  have hid : ordinary (a+z) 0=V R (Explicit.k .low (a+z)) (Explicit.l .low (a+z)) (a+z)+
      Explicit.k .low (a+z)*(phi (frameCap-(a+z))-1)+
      Explicit.l .low (a+z)*(Real.cos frameCap-Real.cos (a+z)) := by
    simp only [ordinary,sub_zero,mixedBlock,V]
    rw [show frameCap-(a+z)-frameCap= -(a+z) by ring]
    ring
  rw [LowD.baseline_correction .low a z hs]
  have hc0 : LowD.correction (Explicit.c .low (a+z)) 0=0 := by
    simp [LowD.correction,LowD.sec,NegativeELargeA.secant]
  rw [hc0,zero_add,hid] at hm
  simp only [Explicit.V,Explicit.p,Explicit.q,Matrix.cons_val_succ,Matrix.cons_val_zero] at hG
  dsimp [zeroEnvelope]
  linarith

theorem HB_negative {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (i : Fin 3) (hi : i=0∨i=2) :
    Explicit.V .low θ z i (θ-s)≤mixedBlock R
      (Explicit.p .low θ z i) (Explicit.q .low θ z i) (frameCap-θ) (frameCap-s) := by
  have hp := LowRanges.pairs hθ hz i
  have hr := LowRanges.HB_ratio hθ hz i hi
  have hP : frameCap-θ∈Icc 0 (frameCap-s) :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hs.2]⟩
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2,hs.2],by linarith [hs.1]⟩
  have hpay : Explicit.q .low θ z i*Real.sin (frameCap-s)≤Explicit.p .low θ z i := by
    have htrig := transport_trig hN
    have hh := mul_le_mul hr htrig.2.2.2.1.le htrig.2.2.1
      (show 0≤(3/2)*Explicit.p .low θ z i by positivity)
    nlinarith [hp.1]
  have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le hP hN hpay
  simpa only [Explicit.V,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh

theorem HB_positive {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i : Fin 3) (hi : i=0∨i=2) :
    Explicit.U .low θ z i (s-θ)≤mixedBlock R
      (Explicit.p .low θ z i) (Explicit.q .low θ z i) (frameCap-θ) (frameCap-s) := by
  have hp := LowRanges.pairs hθ hz i
  have hr := LowRanges.HB_ratio hθ hz i hi
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hN : frameCap-s∈Icc 0 (frameCap-θ) := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hh := NegativeAPositiveTD.SameBlock.positive_surplus hp.1.le
    (show Explicit.q .low θ z i≤(17/10)*Explicit.p .low θ z i by nlinarith [hp.1]) hP hN
  simpa only [Explicit.U,show frameCap-θ-(frameCap-s)=s-θ by ring] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSame
