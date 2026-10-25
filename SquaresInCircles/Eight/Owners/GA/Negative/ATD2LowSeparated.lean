module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcentration
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositive
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2HighAffected
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2LowABSlope
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes

/-!
# Eight squares: the low separated H and G minima

The positive `allowance` does not depend on `s`. The three unaffected derivatives keep the
reserves `.127 l`, `.03192` and `.032`; the affected GA-G case uses the increasing secant curve
`curve` (`H_positive`, `G_positive`).
-/

section
/-!
## The affected G slope on the low interval

The normalized norm coordinate is increased successively in `x`, `r` and `z` to the endpoints
`x = 32/125`, `r = 33/50` and `z = frameCap` (`first_x_monotone`, `first_r_monotone`,
`first_z_monotone`). The final comparison `endpoint` is the positive-square test with `.761` and
`.5747`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowAffectedSlope
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open SecantCoordinate AffectedNorm

def firstR (r z x : ℝ) : ℝ :=
  (1-r*Real.sin z)*(Real.cos z+x*Real.sin z)/(norm r z x)^3
def charged (r z x : ℝ) : ℝ := (13/12+Real.sin frameCap)*x-R*norm r z x
def chargedFirst (r z x : ℝ) : ℝ := 13/12+Real.sin frameCap-R*first r z x

theorem normR_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun r => norm r z x) ((r+x*Real.cos z-Real.sin z)/norm r z x) r := by
  have hn := norm_pos (x:=x) hv
  have hne : (x+r*Real.cos z)^2+(1-r*Real.sin z)^2≠0 := by
    nlinarith [norm_sq r z x]
  have h1 : HasDerivAt (fun r => x+r*Real.cos z) (Real.cos z) r := by
    simpa using ((hasDerivAt_id r).mul_const (Real.cos z)).const_add x
  have h2 : HasDerivAt (fun r => 1-r*Real.sin z) (-Real.sin z) r := by
    simpa using ((hasDerivAt_id r).mul_const (Real.sin z)).const_sub (1:ℝ)
  have hd : HasDerivAt (fun r => (x+r*Real.cos z)^2+(1-r*Real.sin z)^2)
      (2*(x+r*Real.cos z)*Real.cos z-2*(1-r*Real.sin z)*Real.sin z) r :=
    ((h1.fun_pow 2).fun_add (h2.fun_pow 2)).congr_deriv (by simp; ring)
  have hN : Real.sqrt ((x+r*Real.cos z)^2+(1-r*Real.sin z)^2)=norm r z x := rfl
  refine (hd.sqrt hne).congr_deriv ?_
  rw [hN,div_eq_div_iff (by positivity) hn.ne']
  linear_combination (2*r*norm r z x)*(Real.sin_sq_add_cos_sq z)

theorem firstR_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (fun r => first r z x) (firstR r z x) r := by
  have hn := norm_pos (x:=x) hv
  have he : Real.cos z*(norm r z x)^2-
      (x+r*Real.cos z)*(r+x*Real.cos z-Real.sin z)=
      (1-r*Real.sin z)*(Real.cos z+x*Real.sin z) := by
    rw [norm_sq]
    linear_combination r*(x+r*Real.cos z)*(Real.sin_sq_add_cos_sq z)
  have hd := (((hasDerivAt_id r).mul_const (Real.cos z)).const_add x).div
    (normR_hasDerivAt hv) hn.ne'
  convert hd using 1
  · rfl
  · dsimp [first,firstR]
    field_simp [hn.ne']
    nlinarith only [he]

theorem first_x_monotone {r z : ℝ} (hr : r∈Icc (0:ℝ) (33/50:ℝ))
    (hz : z∈Icc 0 frameCap) : MonotoneOn (first r z) (Icc (0:ℝ) (32/125)) := by
  have hv := second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (first_hasDerivAt (x:=x) hv).continuousAt.continuousWithinAt)
    (fun x _ => first_hasDerivAt hv)
  intro x hx
  exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem first_r_monotone {z x : ℝ} (hx : 0≤x) (hz : z∈Icc 0 frameCap) :
    MonotoneOn (fun r => first r z x) (Icc (0:ℝ) (33/50)) := by
  have hv {r : ℝ} (hr : r∈Icc (0:ℝ) (33/50:ℝ)) :=
    second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun r hr => (firstR_hasDerivAt (x:=x) (hv hr)).continuousAt.continuousWithinAt)
    (fun r hr => firstR_hasDerivAt (hv (Ioo_subset_Icc_self hr)))
  intro r hr
  have htr := transport_trig hz
  exact div_nonneg
    (mul_nonneg (hv (Ioo_subset_Icc_self hr)).le
      (add_nonneg (by linarith [htr.1]) (mul_nonneg hx htr.2.2.1)))
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem first_z_monotone :
    MonotoneOn (fun z => first (33/50) z (32/125)) (Icc (0:ℝ) frameCap) := by
  have hv {z : ℝ} (hz : z∈Icc 0 frameCap) :=
    second_coordinate_pos (r:=(33/50:ℝ)) (by norm_num) hz
  apply monoOn_of_hasDeriv_nonneg
    (fun z hz => (firstZ_hasDerivAt (x:=(32/125:ℝ)) (hv hz)).continuousAt.continuousWithinAt)
    (fun z hz => firstZ_hasDerivAt (x:=(32/125:ℝ)) (hv (Ioo_subset_Icc_self hz)))
  intro z hz
  have ht := transport_trig (Ioo_subset_Icc_self hz)
  have hb : 0≤(33/50:ℝ)+(32/125)*Real.cos z-Real.sin z := by
    linarith [ht.1,ht.2.2.2.1]
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hv (Ioo_subset_Icc_self hz)).le) hb)
    (pow_nonneg (Real.sqrt_nonneg _) 3)

theorem endpoint : R*first (33/50) frameCap (32/125)<159/100 := by
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hc := cos_upper_four (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap] at hc
  have hu0 : 0≤(32/125:ℝ)+(33/50)*Real.cos frameCap := by linarith [ht.1]
  have hu : (32/125:ℝ)+(33/50)*Real.cos frameCap<761/1000 := by linarith
  have hv : (5747/10000:ℝ)<1-(33/50)*Real.sin frameCap := by linarith [ht.2.2.2.1]
  have hn := norm_pos (x:=(32/125:ℝ)) (show 0<1-(33/50)*Real.sin frameCap by linarith)
  have hn2 := norm_sq (33/50) frameCap (32/125)
  have hu2 := pow_le_pow_left₀ hu0 hu.le 2
  have hv2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5747/10000) hv.le 2
  have hQ : 0≤qCap-(159/100:ℝ)^2 := by norm_num [qCap]
  have hscale := mul_le_mul_of_nonneg_left hu2 hQ
  have htest : qCap*(761/1000:ℝ)^2<(159/100:ℝ)^2*((761/1000:ℝ)^2+(5747/10000:ℝ)^2) := by
    norm_num [qCap]
  have hR0 : 0≤R := Real.sqrt_nonneg qCap
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hprod : 0≤R*((32/125:ℝ)+(33/50)*Real.cos frameCap) := mul_nonneg hR0 hu0
  have hsquare : (R*((32/125:ℝ)+(33/50)*Real.cos frameCap))^2<
      ((159/100)*norm (33/50) frameCap (32/125))^2 := by
    rw [mul_pow,mul_pow,hR2,hn2]
    nlinarith only [hscale,hv2,htest]
  have hh : R*((32/125:ℝ)+(33/50)*Real.cos frameCap)<
      (159/100)*norm (33/50) frameCap (32/125) := by
    nlinarith
  dsimp [first]
  rw [←mul_div_assoc]
  exact (div_lt_iff₀ hn).2 hh

theorem normalized_norm_slope {r z x : ℝ} (hr : r∈Icc (0:ℝ) (33/50:ℝ))
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 (32/125:ℝ)) : R*first r z x<159/100 := by
  have h₁ := first_x_monotone hr hz hx (show (32/125:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) hx.2
  have h₂ := first_r_monotone (x:=(32/125:ℝ)) (by norm_num) hz hr
    (show (33/50:ℝ)∈Icc 0 (33/50:ℝ) by norm_num) hr.2
  have h₃ := first_z_monotone hz
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hz.2
  exact (mul_le_mul_of_nonneg_left (h₁.trans (h₂.trans h₃)) (Real.sqrt_nonneg qCap)).trans_lt endpoint

theorem charged_hasDerivAt {r z x : ℝ} (hv : 0<1-r*Real.sin z) :
    HasDerivAt (charged r z) (chargedFirst r z x) x := by
  convert ((hasDerivAt_id x).const_mul (13/12+Real.sin frameCap)).sub
    ((norm_hasDerivAt hv).const_mul R) using 1
  · rfl
  · dsimp [chargedFirst]
    ring

theorem charged_slope {r z x : ℝ} (hr : r∈Icc (0:ℝ) (33/50:ℝ))
    (hz : z∈Icc 0 frameCap) (hx : x∈Icc 0 (32/125:ℝ)) :
    (137/1000:ℝ)<chargedFirst r z x := by
  have hh := normalized_norm_slope hr hz hx
  have hs := sin_lower_seven (by norm_num [frameCap] : (0:ℝ)≤frameCap)
  norm_num [frameCap] at hs
  dsimp [chargedFirst]
  linarith

theorem charged_monotone {r z : ℝ} (hr : r∈Icc (0:ℝ) (33/50:ℝ))
    (hz : z∈Icc 0 frameCap) : MonotoneOn (charged r z) (Icc (0:ℝ) (32/125)) := by
  have hv := second_coordinate_pos ⟨hr.1,by linarith [hr.2]⟩ hz
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (charged_hasDerivAt (x:=x) hv).continuousAt.continuousWithinAt)
    (fun x _ => charged_hasDerivAt hv)
  intro x hx
  exact (by norm_num : (0:ℝ)≤137/1000).trans (charged_slope hr hz (Ioo_subset_Icc_self hx)).le

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowAffectedSlope
end
end
end

section
/-!
## The low saturated G terms attain their minimum at s = 0

The affected GA formulas retain
their exact rotated norm in x = tan s. The unaffected AB same-block
derivative uses the displayed `.1641 l` reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowSaturatedG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open SecantCoordinate SecantBaseline LowAffectedSlope

private lemma r71_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

def same (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+mixedBlock R k (lambdaG atG l s) (frameCap-z) (frameCap-s)
def negative (k l c s z : ℝ) : ℝ :=
  baseline true k l c s z+V R k (NegativeAPositiveTD.secant l s) (frameCap-s)
def ABextension (k l c s z : ℝ) : ℝ :=
  angularBaseline false k l c s z+mixedBlock R k l (frameCap-z) (frameCap-s)
def ABfirst (k l c s z : ℝ) : ℝ :=
  angleSlope l (PositiveTD.tilted c z/l) s-
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
  have hkey : l/Real.cos s*Real.cos (frameCap-s)=
      l*(Real.cos frameCap+Real.tan s*Real.sin frameCap) := by
    rw [←hcos]; ring
  rw [same,baseline_eq_extension true k l c z hs]
  simp only [angularBaseline,affected,lambdaG,↓reduceIte,FlatTStress.secantCharge,mixedBlock]
  rw [show frameCap-z-(frameCap-s)=s-z by ring,
    AffectedPositive.rotation_norm hl hc k z,AffectedPositive.zero_norm hl k]
  simp only [LowAffectedSlope.charged,NegativeAPositiveTD.secant]
  linear_combination hkey

theorem GA_negative_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    negative k l c s z=baseline true k l c 0 z+l*(Real.cos frameCap-1)+
      l*(charged (k/l) frameCap (Real.tan s)+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos := cap_cosine hs
  have hkey : l/Real.cos s*Real.cos (frameCap-s)=
      l*(Real.cos frameCap+Real.tan s*Real.sin frameCap) := by
    rw [←hcos]; ring
  rw [negative,baseline_eq_extension true k l c z hs]
  simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,V]
  rw [show -(frameCap-s)=s-frameCap by ring,
    AffectedPositive.rotation_norm hl hc k frameCap,AffectedPositive.zero_norm hl k]
  simp only [LowAffectedSlope.charged,NegativeAPositiveTD.secant]
  linear_combination hkey

theorem original_ratio {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    Explicit.k .low z/Explicit.l .low z∈Icc (0:ℝ) (33/50:ℝ) := by
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  exact ⟨div_nonneg hp.1.le hp.2.1.le,(div_le_iff₀ hp.2.1).2 (Explicit.low_ratio hz).2.le⟩

theorem tan_original {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    Real.tan s∈Icc 0 (32/125:ℝ) := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hh := tan_monotone hsf (show (1/4:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hs.2
  exact ⟨tan_nonnegative hsf,hh.trans SecantBounds.tan_GA_cut.le⟩

theorem GA_same_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    same true (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z≤
      same true (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hl := (Explicit.family_positive .low (r71_low_dom hz)).2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := charged_monotone (original_ratio hz) hzframe
    (show (0:ℝ)∈Icc 0 (32/125:ℝ) by norm_num) (tan_original hs) (tan_original hs).1
  rw [GA_same_identity hl (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),
    GA_same_identity hl hsf,Real.tan_zero]
  nlinarith [mul_le_mul_of_nonneg_left hh hl.le]

theorem GA_negative_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (1/4:ℝ)) :
    negative (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z≤
      negative (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hl := (Explicit.family_positive .low (r71_low_dom hz)).2.1
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
  have h1 := angularBaseline_hasDerivAt (k:=k) (c:=c) (z:=z) false hl hc
  have h2 : HasDerivAt (fun s => mixedBlock R k l (frameCap-z) (frameCap-s))
      (mixedNDerivative R k l (frameCap-z) (frameCap-s)*(-1)) s :=
    (mixedN_hasDerivAt (R:=R) hk hl hP hN).comp s ((hasDerivAt_id s).const_sub frameCap)
  refine (h1.fun_add h2).congr_deriv ?_
  simp only [ABfirst,basicRatio,affected,Bool.false_eq_true,↓reduceIte]
  ring

theorem ABfirst_lower {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    (1641/10000)*Explicit.l .low z<ABfirst (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  have hratio := Explicit.low_ratio hz
  have hbasic := Explicit.family_basic_domain .low (r71_low_dom hz)
  have habs : |s-z|≤frameCap := by
    rw [abs_le]
    dsimp [frameCap]
    constructor <;> linarith [hs.1,hs.2,hz.1,hz.2]
  have ht := Curvature.norm_slope_signed_tangent hp.1 hp.2.1 habs
  obtain ⟨hC,hD⟩ := Curvature.restricted_constants .narrow hp.1 hbasic.2.2.2.1.le
    (show Explicit.k .low z≤(Curvature.ratioEnd .narrow:ℝ)*Explicit.l .low z by
      rw [show ((Curvature.ratioEnd .narrow:ℚ):ℝ)=33/50 by norm_num [Curvature.ratioEnd]]
      exact hratio.2.le)
  rw [show ((Curvature.C0End .narrow:ℚ):ℝ)=251/500 by norm_num [Curvature.C0End]] at hC
  rw [show ((Curvature.D0End .narrow:ℚ):ℝ)=109/100 by norm_num [Curvature.D0End]] at hD
  have hC0 : 0≤curvatureZero R (Explicit.k .low z) (Explicit.l .low z) := by
    dsimp only [curvatureZero]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
      (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hshift := mul_le_mul_of_nonneg_left
    (show -(s-z)≤1/5 by linarith [hs.1,hz.2]) hC0
  have hnorm : R*normD1 (Explicit.k .low z) (Explicit.l .low z) (s-z)<
      ((109/100:ℝ)+(251/500)*(1/5))*Explicit.l .low z := by
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
  have hb := LowABSlope.original hz hs
  dsimp [ABfirst,mixedNDerivative,Explicit.m] at hb ⊢
  rw [show frameCap-z-(frameCap-s)=s-z by ring]
  linarith

theorem AB_same_zero_le {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (19/50:ℝ)) :
    same false (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z≤
      same false (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  have hzframe : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hdom {s : ℝ} (hs : s∈Icc 0 (19/50:ℝ)) : s∈Icc 0 frameCap :=
    ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hm : MonotoneOn (fun s => ABextension (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z)
      (Icc (0:ℝ) (19/50)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (ABextension_hasDerivAt hp.1 hp.2.1 (hdom hs) hzframe).continuousAt.continuousWithinAt)
      (fun s hs => ABextension_hasDerivAt hp.1 hp.2.1 (hdom (Ioo_subset_Icc_self hs)) hzframe)
    intro s hs
    exact (mul_nonneg (by norm_num) hp.2.1.le).trans (ABfirst_lower hz (Ioo_subset_Icc_self hs)).le
  have hh : ABextension (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z≤
      ABextension (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z :=
    hm (show (0:ℝ)∈Icc 0 (19/50:ℝ) by norm_num) hs hs.1
  rwa [ABextension_eq (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]),ABextension_eq (hdom hs)] at hh

theorem same_positive (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/5:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<same atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z := by
  have hzero : 0<same atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z := by
    have he : frameCap-z-(frameCap-0)=-z := by ring
    simpa [same,lambdaG,NegativeAPositiveTD.secant,baseline_zero,mixedBlock,mixedG,he] using
      (Certificate.low_endpoints hz).2.1
  cases atG
  · exact hzero.trans_le (AB_same_zero_le hz hs)
  · exact hzero.trans_le (GA_same_zero_le hz hs)

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowSaturatedG
end
end
end

section
/-!
## Removing all common signed mass in the high negative-DE family

Both original ordinary totals
are first concentrated without alteration.  The surplus retains its
sign, and the two uniform slope reserves remove the common mass even
when the positive and negative totals occupy different original blocks.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope

namespace OrdinarySlope

theorem positive_short_growth {p q x y : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hx : x∈Icc 0 (8/15:ℝ)) (hy : y∈Icc 0 (8/15:ℝ)) (hxy : x≤y) :
    -(16/25)*q*(y-x)≤U R p q y-U R p q x := by
  have hf (w : ℝ) (hw : w∈Icc 0 (8/15:ℝ)) :=
    NegativeAPositiveTD.PositiveSlope.U_hasDerivAt hp (hp.trans_le hpq)
      (show w∈Icc 0 frameCap by exact ⟨hw.1,by norm_num [frameCap]; linarith [hw.2]⟩)
  exact derivative_reserve
    (fun w hw => (hf w hw).continuousAt.continuousWithinAt)
    (fun w hw => hf w (Ioo_subset_Icc_self hw))
    (fun w hw => (positive_derivative_short hp hpq hqp (Ioo_subset_Icc_self hw)).le)
    hx hy hxy

theorem negative_short_growth {p q x y : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : (2/3)*q≤p)
    (hx : x∈Icc 0 (8/15:ℝ)) (hy : y∈Icc 0 (8/15:ℝ)) (hxy : x≤y) :
    (39/50)*q*(y-x)≤V R p q y-V R p q x := by
  have hf (w : ℝ) (hw : w∈Icc 0 (8/15:ℝ)) :=
    V_hasDerivAt (R:=R) hp (hp.trans_le hpq)
      (show w∈Icc 0 frameCap by exact ⟨hw.1,by norm_num [frameCap]; linarith [hw.2]⟩)
  exact derivative_reserve
    (fun w hw => (hf w hw).continuousAt.continuousWithinAt)
    (fun w hw => hf w (Ioo_subset_Icc_self hw))
    (fun w hw => (negative_derivative_short hp hpq hqp (Ioo_subset_Icc_self hw)).le)
    hx hy hxy

end OrdinarySlope

namespace HighConcentration

def pure (θ z s : ℝ) (i : Fin 3) : ℝ :=
  if s≤θ then Explicit.V .high θ z i (θ-s) else Explicit.U .high θ z i (s-θ)

theorem pure_le_concentrated {θ z s P N : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hs : s∈Icc 0 frameCap) (hP : 0≤P) (hN : 0≤N)
    (hPb : P≤frameCap-θ) (hNb : N≤frameCap-s) (hbalance : N-P=θ-s)
    (i j : Fin 3) :
    (if s≤θ then pure θ z s j else pure θ z s i)≤
      if i=j then mixedBlock R (Explicit.p .high θ z i) (Explicit.q .high θ z i) P N
      else Explicit.U .high θ z i P+Explicit.V .high θ z j N := by
  have hi := Explicit.high_pairs hθ hz i
  have hj := Explicit.high_pairs hθ hz j
  have hqi := hi.1.trans_le hi.2.1
  have hqj := hj.1.trans_le hj.2.1
  have hip : Explicit.q .high θ z i≤2*Explicit.p .high θ z i := by linarith [hi.2.2.1]
  have hjp : Explicit.q .high θ z j≤2*Explicit.p .high θ z j := by linarith [hj.2.2.1]
  have hPcap : P∈Icc 0 frameCap := ⟨hP,by linarith [hθ.1]⟩
  have hNcap : N∈Icc 0 frameCap := ⟨hN,by linarith [hs.1]⟩
  have hPshort : P∈Icc 0 (8/15:ℝ) := by
    dsimp [frameCap] at hPb
    exact ⟨hP,by linarith [hθ.1]⟩
  have hratio := Explicit.high_q_ratio hθ hz i j
  by_cases hst : s≤θ
  · have hPN : P≤N := by linarith
    have hdiff : N-P∈Icc 0 frameCap := ⟨by linarith,by linarith [hNcap.2]⟩
    simp only [pure,hst,↓reduceIte]
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      have hsine : Explicit.q .high θ z i*Real.sin N≤Explicit.p .high θ z i := by
        have hm := mul_le_mul_of_nonneg_left (transport_trig hNcap).2.2.2.1.le hqi.le
        linarith [hi.2.2.1]
      have hh := NegativeAPositiveTD.SameBlock.negative_surplus hi.1.le
        ⟨hP,hPN⟩ hNcap hsine
      simpa only [hbalance,Explicit.V] using hh
    · simp only [hij,↓reduceIte]
      have hg := V_growth hj.1 hj.2.1 hj.2.2.1.le hdiff hNcap (by linarith)
      have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap)
        (Real.sq_sqrt (by norm_num [qCap])).le hi.1 hi.2.1 hip hPcap
      have hpay : 0≤((2/3)*Explicit.q .high θ z j-
          (109/200)*Explicit.q .high θ z i)*P := by
        apply mul_nonneg _ hP
        linarith [hqj.le]
      rw [show N-(N-P)=P by ring,hbalance] at hg
      dsimp [Explicit.U,Explicit.V]
      linarith
  · have hNP : N≤P := by linarith
    have hNshort : N∈Icc 0 (8/15:ℝ) := ⟨hN,hNP.trans hPshort.2⟩
    have hdiff : P-N∈Icc 0 (8/15:ℝ) := ⟨by linarith,by linarith [hPshort.2]⟩
    have hsurplus : P-N=s-θ := by linarith
    simp only [pure,hst,↓reduceIte]
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      have h17 : Explicit.q .high θ z i≤(17/10)*Explicit.p .high θ z i := by
        linarith [hi.1,hi.2.2.1]
      have hh := NegativeAPositiveTD.SameBlock.positive_surplus hi.1.le h17 hPcap ⟨hN,hNP⟩
      simpa only [hsurplus,Explicit.U] using hh
    · simp only [hij,↓reduceIte]
      have hg := OrdinarySlope.negative_short_growth hj.1 hj.2.1 hj.2.2.1.le
        (by norm_num : (0:ℝ)∈Icc 0 (8/15:ℝ)) hNshort hN
      have hu := OrdinarySlope.positive_short_growth hi.1 hi.2.1 hip hdiff hPshort
        (by linarith)
      have hpay : 0≤((39/50)*Explicit.q .high θ z j-
          (16/25)*Explicit.q .high θ z i)*N := by
        apply mul_nonneg _ hN
        linarith [hqj.le]
      simp only [V_zero,sub_zero] at hg
      rw [show P-(P-N)=N by ring,hsurplus] at hu
      dsimp [Explicit.U,Explicit.V]
      linarith

/-- An actual original ordinary allocation is bounded by a single pure
surplus block; the selected block need not be geometrically realized. -/
theorem sum_to_pure {θ z s : ℝ} (P N : Fin 3→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i,pure θ z s i≤∑j,mixedBlock R
      (Explicit.p .high θ z j) (Explicit.q .high θ z j) (P j) (N j) := by
  have hp := Explicit.high_pairs hθ hz
  obtain ⟨i,j,hij⟩ := OrdinaryAngleConcentration.both_signs_concentrate R
    (Explicit.p .high θ z) (Explicit.q .high θ z) P N
    (Real.sqrt_nonneg qCap) (Real.sq_sqrt (by norm_num [qCap])).le
    (fun i => (hp i).1) (fun i => (hp i).2.1)
    (fun i => by linarith [(hp i).1,(hp i).2.2.1]) hP hN
    (by linarith [hθ.1]) (by linarith [hs.1])
  have hh := pure_le_concentrated hθ hz hs
    (Finset.sum_nonneg (fun i _ => hP i)) (Finset.sum_nonneg (fun i _ => hN i))
    hPb hNb hbalance i j
  by_cases hst : s≤θ
  · refine ⟨j,?_⟩
    simp only [hst,↓reduceIte] at hh
    exact hh.trans hij
  · refine ⟨i,?_⟩
    simp only [hst,↓reduceIte] at hh
    exact hh.trans hij

end HighConcentration
end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open SecantBaseline NegativeSlope

private lemma r71_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

inductive Case where
  | abG | abH | gaH
  deriving DecidableEq
def atG : Case→Bool | .gaH=>true | _=>false
def larger (e : Case) (l : ℝ) : ℝ := if e=.abG then l else 1
def upperCase : Case→Upper | .abG=>.G32 | .abH=>.H32 | .gaH=>.H45
def curve (e : Case) (k l c z s : ℝ) : ℝ :=
  angularBaseline (atG e) k l c s z+V R k (larger e l) (frameCap-s)
def first (e : Case) (k l c z s : ℝ) : ℝ :=
  angleSlope l (basicRatio (atG e) k l c z) s-Vd R k (larger e l) (frameCap-s)
def allowance (z : ℝ) : ℝ := (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)

theorem curve_hasDerivAt (e : Case) {k l c z s : ℝ}
    (hk : 0<k) (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (curve e k l c z) (first e k l c z s) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hq : 0<larger e l := by cases e <;> simp [larger]; positivity
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have h1 := angularBaseline_hasDerivAt (k:=k) (c:=c) (z:=z) (atG e) hl hc
  have h2 : HasDerivAt (fun s => V R k (larger e l) (frameCap-s))
      (Vd R k (larger e l) (frameCap-s)*(-1)) s :=
    (V_hasDerivAt (R:=R) hk hq hN).comp s ((hasDerivAt_id s).const_sub frameCap)
  refine (h1.fun_add h2).congr_deriv ?_
  simp only [first]
  ring

theorem upper_original (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    Vd R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s)<
      (upperValue (upperCase e):ℝ)*larger e (Explicit.l .low z) := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  have hkl := (Explicit.family_basic_domain .low (r71_low_dom hz)).2.2.2.1
  have hratio := Explicit.low_ratio hz
  cases e
  · apply upper_bound .G32 hp.1 hkl.le
      (by linarith [hratio.1])
      (by simpa [upperRatio] using hratio.2.le)
    dsimp [atG,Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · rw [show larger .abH (Explicit.l .low z)=1 by simp [larger]]
    apply upper_bound .H32 hp.1 (by linarith) (by linarith)
      (by simpa [upperRatio] using hkhi)
    dsimp [atG,Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · rw [show larger .gaH (Explicit.l .low z)=1 by simp [larger]]
    apply upper_bound .H45 hp.1 (by linarith) (by linarith)
      (by simpa [upperRatio] using hkhi)
    dsimp [atG,Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem first_positive (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    0<first e (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z s := by
  have hV := upper_original e hz hs
  have hl := (Explicit.low_ranges hz).2.2.1
  cases e
  · have hB := LowABSlope.original hz hs
    dsimp [first,atG,larger,upperCase,upperValue,basicRatio,affected,Explicit.m] at hV hB ⊢
    have hmargin : (127/1000)*Explicit.l .low z<
        angleSlope (Explicit.l .low z) (PositiveTD.tilted (Explicit.c .low z) z/Explicit.l .low z) s-
          Vd R (Explicit.k .low z) (Explicit.l .low z) (frameCap-s) := by linarith
    nlinarith
  · have hB := LowABSlope.original hz hs
    dsimp [first,atG,larger,upperCase,upperValue,basicRatio,affected,Explicit.m] at hV hB ⊢
    have hmargin : (399/12500:ℝ)<
        angleSlope (Explicit.l .low z) (PositiveTD.tilted (Explicit.c .low z) z/Explicit.l .low z) s-
          Vd R (Explicit.k .low z) 1 (frameCap-s) := by linarith
    linarith
  · have hB := LowGASlope.original hz hs
    dsimp [first,atG,larger,upperCase,upperValue,basicRatio,affected] at hV hB ⊢
    have hmargin : (4/125:ℝ)<
        angleSlope (Explicit.l .low z) (Explicit.k .low z/Explicit.l .low z) s-
          Vd R (Explicit.k .low z) 1 (frameCap-s) := by linarith
    linarith

theorem fixed_zero_le (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) frameCap≤
      baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s) := by
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  have hzero : (0:ℝ)∈Icc 0 (Explicit.angleCut (atG e)) := by
    cases e <;> norm_num [atG,Explicit.angleCut]
  have hm : MonotoneOn (curve e (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z)
      (Icc (0:ℝ) (Explicit.angleCut (atG e))) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (curve_hasDerivAt e hp.1 hp.2.1 (Explicit.angle_domain _ hs).2).continuousAt.continuousWithinAt)
      (fun s hs => curve_hasDerivAt e hp.1 hp.2.1 (Explicit.angle_domain _ (Ioo_subset_Icc_self hs)).2)
    intro s hs
    exact (first_positive e hz (Ioo_subset_Icc_self hs)).le
  have hh := hm hzero hs hs.1
  dsimp [curve] at hh
  rw [←baseline_eq_extension (atG e) _ _ _ _ (Explicit.angle_domain _ hzero).2,
    ←baseline_eq_extension (atG e) _ _ _ _ (Explicit.angle_domain _ hs).2,sub_zero] at hh
  exact hh

theorem H_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z-
      allowance z+V R (Explicit.k .low z) 1 (frameCap-s) := by
  have hzero := (Certificate.low_endpoints hz).2.2.1
  cases atG
  · have hh := fixed_zero_le .abH hz hs
    simp only [atG,larger,reduceCtorEq,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith
  · have hh := fixed_zero_le .gaH hz hs
    simp only [atG,larger,reduceCtorEq,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith

theorem G_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z-
      allowance z+V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s) := by
  have hzero := (Certificate.low_endpoints hz).2.2.2.1
  cases atG
  · have hh := fixed_zero_le .abG hz hs
    simp only [atG,larger,↓reduceIte,baseline_zero] at hh
    dsimp [allowance,lambdaG]
    linarith
  · have hh := LowSaturatedG.GA_negative_zero_le hz hs
    simp only [LowSaturatedG.negative,NegativeAPositiveTD.secant,Real.cos_zero,div_one,
      sub_zero,baseline_zero] at hh
    dsimp [allowance,lambdaG,NegativeAPositiveTD.secant]
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.LowSeparated
end
end
end
