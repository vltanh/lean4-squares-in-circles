module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LowSlopes

/-!
# The low BT3 saturated G curves

Uncompiled Section 5. The affected GA norm uses ratio at most 2/3
and its 1.6 derivative bound. The unaffected AB same-block derivative
uses the widened .94 baseline ratio and the exact .117l reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowSaturatedG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NegativeAPositiveTD.SecantCoordinate Angular LowAffectedSlope

private theorem r69_low_dom {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]; exact hz

def same (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+mixedBlock R k (lambdaG atG l s) (frameCap-z) (frameCap-s)
def negative (k l c s z : ℝ) : ℝ :=
  baseline true k l c s z+V R k (NegativeAPositiveTD.secant l s) (frameCap-s)
def ABextension (k l c s z : ℝ) : ℝ :=
  extension false k l c s z+mixedBlock R k l (frameCap-z) (frameCap-s)
def ABfirst (k l c s z : ℝ) : ℝ :=
  angleSlope l (c/l) s-
    mixedNDerivative R k l (frameCap-z) (frameCap-s)

theorem cap_cosine {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.cos (frameCap-s)/Real.cos s=Real.cos frameCap+Real.tan s*Real.sin frameCap := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
  field_simp [hc.ne']

theorem GA_same_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    same true k l c s z=baseline true k l c 0 z+k*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
      l*(Real.cos frameCap-1)+
      l*(charged (k/l) z (Real.tan s)+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos := cap_cosine hs
  rw [same,baseline_eq_extension true k l c z hs]
  simp only [extension,affected,lambdaG,NegativeAPositiveTD.lambdaG,↓reduceIte,FlatTStress.secantCharge,mixedBlock]
  rw [show frameCap-z-(frameCap-s)=s-z by ring,
    NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc k z,NegativeAPositiveTD.AffectedPositive.zero_norm hl k]
  dsimp [LowAffectedSlope.charged,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  linear_combination (12*l)*hh

theorem GA_negative_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    negative k l c s z=baseline true k l c 0 z+l*(Real.cos frameCap-1)+
      l*(charged (k/l) frameCap (Real.tan s)+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos := cap_cosine hs
  rw [negative,baseline_eq_extension true k l c z hs]
  simp only [extension,affected,↓reduceIte,FlatTStress.secantCharge,V]
  rw [show -(frameCap-s)=s-frameCap by ring,
    NegativeAPositiveTD.AffectedPositive.rotation_norm hl hc k frameCap,NegativeAPositiveTD.AffectedPositive.zero_norm hl k]
  dsimp [LowAffectedSlope.charged,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  linear_combination (12*l)*hh

theorem original_ratio {z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) :
    Explicit.k .low z/Explicit.l .low z∈Icc (0:ℝ) (2/3:ℝ) := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  exact ⟨div_nonneg hp.1.le hp.2.1.le,(div_le_iff₀ hp.2.1).2 (Explicit.low_ratio hz).2.le⟩

theorem tan_original {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    Real.tan s∈Icc 0 (32/125:ℝ) := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hh := tan_monotone hsf (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hs.2
  exact ⟨tan_nonnegative hsf,hh.trans NegativeAPositiveTD.SecantBounds.tan_GA_cut.le⟩

theorem GA_same_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    same true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z≤
      same true (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hl := (Explicit.family_positive .low (r69_low_dom hz)).2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := charged_monotone (original_ratio hz) hzframe
    (show (0:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) (tan_original hs) (tan_original hs).1
  rw [GA_same_identity hl (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),
    GA_same_identity hl hsf,Real.tan_zero]
  nlinarith [mul_le_mul_of_nonneg_left hh hl.le]

theorem GA_negative_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    negative (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z≤
      negative (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hl := (Explicit.family_positive .low (r69_low_dom hz)).2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hh := charged_monotone (original_ratio hz)
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
    (show (0:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) (tan_original hs) (tan_original hs).1
  rw [GA_negative_identity hl (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),
    GA_negative_identity hl hsf,Real.tan_zero]
  nlinarith [mul_le_mul_of_nonneg_left hh hl.le]

theorem ABextension_eq {k l c s z : ℝ} (hs : s∈Icc 0 frameCap) :
    ABextension k l c s z=same false k l c s z := by
  rw [same,baseline_eq_extension false k l c z hs]
  rfl

theorem ABextension_hasDerivAt {k l c s z : ℝ}
    (hk : 0<k) (hl : 0<l) (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fun s => ABextension k l c s z) (ABfirst k l c s z) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd := (extension_hasDerivAt (k:=k) (m:=c) (z:=z) false hl hc).add
    ((mixedN_hasDerivAt (R:=R) hk hl hP hN).comp s ((hasDerivAt_id s).const_sub frameCap))
  convert hd using 1
  · rfl
  · dsimp [ABfirst,ratio,affected]
    ring

theorem ABfirst_lower {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    (117/1000)*Explicit.l .low z<ABfirst (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  have hratio := Explicit.low_ratio hz
  have hbasic := Explicit.family_basic_domain .low (r69_low_dom hz)
  have habs : |s-z|≤frameCap := by
    rw [abs_le]
    dsimp [frameCap]
    constructor <;> linarith [hs.1,hs.2,hz.1,hz.2]
  have ht := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hp.1 hp.2.1 habs
  obtain ⟨hC,hD⟩ := LowSlopes.narrow_constants hp.1 hbasic.2.2.2.1.le hratio.2.le
  have hC0 : 0≤curvatureZero R (Explicit.k .low z) (Explicit.l .low z) := by
    dsimp [curvatureZero]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
      (pow_nonneg (by rw [pairNorm_zero]; positivity) 3)
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-z)≤1/4 by linarith [hs.1,hz.2]) hC0
  have hnorm : R*normD1 (Explicit.k .low z) (Explicit.l .low z) (s-z)<
      ((11/10:ℝ)+(51/100)*(1/4))*Explicit.l .low z := by
    linarith
  have hN : frameCap-s∈Icc (8/25:ℝ) (7/10:ℝ) := by
    dsimp [frameCap]
    constructor <;> linarith [hs.1,hs.2]
  have hsin := trig_bracket (l:=(8/25:ℝ)) (u:=(7/10:ℝ)) (x:=frameCap-s)
    (by norm_num) (by linarith [Real.pi_gt_three]) hN
  have hsine : (629/2000:ℝ)<Real.sin (frameCap-s) := by
    norm_num at hsin
    linarith [hsin.1]
  have hsine' := mul_lt_mul_of_pos_left hsine hp.2.1
  have hb := LowSlopes.AB_original hz hs
  dsimp [ABfirst,mixedNDerivative] at hb ⊢
  rw [show frameCap-z-(frameCap-s)=s-z by ring]
  linarith

theorem AB_same_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    same false (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z≤
      same false (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hp := Explicit.family_positive .low (r69_low_dom hz)
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hdom {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) : s∈Icc 0 frameCap :=
    ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hm : MonotoneOn (fun s => ABextension (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z)
      (Icc (0:ℝ) (19/50)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (ABextension_hasDerivAt hp.1 hp.2.1 (hdom hs) hzframe).continuousAt.continuousWithinAt)
      (fun s hs => ABextension_hasDerivAt hp.1 hp.2.1 (hdom (Ioo_subset_Icc_self hs)) hzframe)
    intro s hs
    exact (mul_nonneg (by norm_num) hp.2.1.le).trans (ABfirst_lower hz (Ioo_subset_Icc_self hs)).le
  have hh := hm (show (0:ℝ)∈Icc 0 (19/50:ℝ) by norm_num) hs hs.1
  simp only at hh
  rwa [ABextension_eq (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),ABextension_eq (hdom hs)] at hh

theorem same_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<same atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z := by
  have hzero : 0<same atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z := by
    have he : frameCap-z-(frameCap-0)=-z := by ring
    simpa [same,lambdaG,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.secant,baseline_zero,
      mixedBlock,mixedG,NegativeAPositiveTD.mixedG,he] using (low_endpoints hz).2.1
  cases atG
  · exact hzero.trans_le (AB_same_zero_le hz hs)
  · exact hzero.trans_le (GA_same_zero_le hz hs)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowSaturatedG
