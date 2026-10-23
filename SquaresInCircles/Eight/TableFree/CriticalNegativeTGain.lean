module

public import SquaresInCircles.Eight.TableFree.CriticalNegativeTPolynomials
public import SquaresInCircles.Eight.TableFree.CriticalEExclusion
public import SquaresInCircles.Eight.TableFree.FlatTStress

/-!
# Exact sharp-strip negative-T secant endpoints

Uncompiled source. The two rationalized certificates are joined to the
literal full-circle secant charges. The factors are exact identities,
including the difference of the shifted ordinary B norms. The A endpoint
uses an integrated coefficient comparison, so no ordering of k and c is
assumed. All coefficients come from the original minimizing chain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTGain
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open CriticalECoefficients CriticalEExclusion CriticalNegativeTPolynomials
open FlatTStress SoleNormGain SingleAngleConcavity

theorem sqrt_difference {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hden : 0<Real.sqrt a+Real.sqrt b) :
    Real.sqrt a-Real.sqrt b=(a-b)/(Real.sqrt a+Real.sqrt b) := by
  apply (eq_div_iff hden.ne').2
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]

theorem secant_norm_difference {a c s : ℝ} (hc : 0<c) (hcos : 0<Real.cos s) :
    Real.sqrt (a^2+c^2/Real.cos s^2)-Real.sqrt (a^2+c^2)=
      c^2*Real.sin s^2/(Real.cos s^2*
        (Real.sqrt (a^2+c^2/Real.cos s^2)+Real.sqrt (a^2+c^2))) := by
  have hn : 0<Real.sqrt (a^2+c^2) := Real.sqrt_pos.mpr (by positivity)
  have hd : 0<Real.sqrt (a^2+c^2/Real.cos s^2)+Real.sqrt (a^2+c^2) :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hn
  rw [sqrt_difference (by positivity) (by positivity) hd]
  field_simp [hcos.ne',hd.ne']
  nlinarith [Real.sin_sq_add_cos_sq s]

theorem negative_norm_difference {l c t : ℝ} (hl : 0<l) (hc : 0<c)
    (ht : t∈Icc 0 frameCap) :
    Real.sqrt (l^2+c^2)-Real.sqrt (l^2+c^2-2*l*c*Real.sin t)=
      2*l*c*Real.sin t/
        (Real.sqrt (l^2+c^2)+Real.sqrt (l^2+c^2-2*l*c*Real.sin t)) := by
  have hneg : 0<l^2+c^2-2*l*c*Real.sin t := by
    simpa only [Real.sin_neg,mul_neg,sub_eq_add_neg] using
      pair_radicand_pos hl hc (by simpa [abs_of_nonneg ht.1] using ht.2 : |-t|≤frameCap)
  have hzero : 0<Real.sqrt (l^2+c^2) := Real.sqrt_pos.mpr (by positivity)
  rw [sqrt_difference (by positivity) hneg.le
    (add_pos_of_pos_of_nonneg hzero (Real.sqrt_nonneg _))]
  congr 1
  ring

theorem TD_factor {R l c t : ℝ} (hl : 0<l) (hc : 0<c)
    (ht : t∈Icc 0 frameCap) :
    secantCharge R c 1 t-V R l c t=c*Real.sin t*jD R l c t := by
  have hcos := transport_cos_pos (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have hD := secant_norm_difference (a := 1) hc hcos
  have hB := negative_norm_difference hl hc ht
  have hbase : c*(1/Real.cos t-1+(13/12)*(Real.sin t/Real.cos t))-
      c*(Real.cos t-1)=c*Real.sin t*((Real.sin t+13/12)/Real.cos t) := by
    field_simp [hcos.ne']
    nlinarith [Real.sin_sq_add_cos_sq t]
  calc
    secantCharge R c 1 t-V R l c t=
        (c*(1/Real.cos t-1+(13/12)*(Real.sin t/Real.cos t))-c*(Real.cos t-1))-
          R*((Real.sqrt (1+c^2/Real.cos t^2)-Real.sqrt (1+c^2))+
            (Real.sqrt (l^2+c^2)-Real.sqrt (l^2+c^2-2*l*c*Real.sin t))) := by
      simp only [secantCharge,V,pairNorm_zero,pairNorm,Real.sin_neg,
        Real.tan_eq_sin_div_cos,div_pow,one_pow]
      ring
    _=c*Real.sin t*jD R l c t := by
      rw [hbase,show Real.sqrt (1+c^2/Real.cos t^2)-Real.sqrt (1+c^2)=
        c^2*Real.sin t^2/(Real.cos t^2*
          (Real.sqrt (1+c^2/Real.cos t^2)+Real.sqrt (1+c^2))) by simpa using hD,hB]
      dsimp [jD]
      ring

theorem BT_factor {R l c t : ℝ} (hl : 0<l) (hc : 0<c)
    (ht : t∈Icc shortAngle frameCap) :
    secantCharge R c l shortAngle+V R l c (t-shortAngle)-V R l c t=
      c*Real.sin shortAngle*jB R l c t := by
  let b : ℝ := shortAngle
  let a : ℝ := Real.sin b/(1+Real.cos b)
  have hb : b∈Icc 0 frameCap := by norm_num [b,shortAngle,frameCap]
  have hcB := transport_cos_pos (by rw [abs_of_nonneg hb.1]; exact hb.2)
  have hc1 : 0<1+Real.cos b := by linarith
  have hhalf : Real.sin b*a=1-Real.cos b := by
    dsimp [a]
    field_simp [hc1.ne']
    nlinarith [Real.sin_sq_add_cos_sq b]
  have hcosSub : Real.cos (t-b)-Real.cos t=
      Real.sin b*(Real.sin t-Real.cos t*a) := by
    rw [Real.cos_sub]
    nlinarith [congrArg (fun x : ℝ => Real.cos t*x) hhalf]
  have hsinSub : Real.sin t-Real.sin (t-b)=
      Real.sin b*(Real.cos t+Real.sin t*a) := by
    rw [Real.sin_sub]
    nlinarith [congrArg (fun x : ℝ => Real.sin t*x) hhalf]
  have hsec : 1/Real.cos b-1=Real.sin b*a/Real.cos b := by
    rw [hhalf]
    field_simp [hcB.ne']
    ring
  have ht0 : t∈Icc 0 frameCap := ⟨hb.1.trans ht.1,ht.2⟩
  have hd : t-b∈Icc 0 frameCap := ⟨sub_nonneg.mpr ht.1,by linarith [ht.2,hb.1]⟩
  have hr (u : ℝ) (hu : u∈Icc 0 frameCap) : 0<l^2+c^2-2*l*c*Real.sin u := by
    simpa only [Real.sin_neg,mul_neg,sub_eq_add_neg] using
      pair_radicand_pos hl hc (by simpa [abs_of_nonneg hu.1] using hu.2 : |-u|≤frameCap)
  have hshift : Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))-
      Real.sqrt (l^2+c^2-2*l*c*Real.sin t)=
      2*l*c*Real.sin b*(Real.cos t+Real.sin t*a)/
        (Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))+
          Real.sqrt (l^2+c^2-2*l*c*Real.sin t)) := by
    rw [sqrt_difference (hr _ hd).le (hr _ ht0).le (by positivity)]
    congr 1
    nlinarith [congrArg (fun x : ℝ => 2*l*c*x) hsinSub]
  have hnew := secant_norm_difference (a := l) hc hcB
  have hbase : c*(1/Real.cos b-1+(13/12)*(Real.sin b/Real.cos b))+
      c*(Real.cos (t-b)-1)-c*(Real.cos t-1)=
      c*Real.sin b*(a*(1/Real.cos b-Real.cos t)+(13/12)/Real.cos b+Real.sin t) := by
    rw [hsec]
    have hh := congrArg (fun x : ℝ => c*x) hcosSub
    dsimp at hh
    nlinarith
  calc
    secantCharge R c l b+V R l c (t-b)-V R l c t=
        (c*(1/Real.cos b-1+(13/12)*(Real.sin b/Real.cos b))+
          c*(Real.cos (t-b)-1)-c*(Real.cos t-1))-
          R*((Real.sqrt (l^2+c^2/Real.cos b^2)-Real.sqrt (l^2+c^2))+
            (Real.sqrt (l^2+c^2-2*l*c*Real.sin (t-b))-
              Real.sqrt (l^2+c^2-2*l*c*Real.sin t))) := by
      simp only [secantCharge,V,pairNorm_zero,pairNorm,Real.sin_neg,
        Real.tan_eq_sin_div_cos,div_pow]
      ring
    _=c*Real.sin b*jB R l c t := by
      rw [hbase,hnew,hshift]
      dsimp [jB,a,b]
      ring

/-- An error of at most .011d suffices at the shifted BT endpoint. -/
theorem A_lower {R t k l c eta d : ℝ} (hR : R∈Icc 0 2)
    (h : Bounds t k l c eta) (hd : d∈Icc 0 (1/5:ℝ)) :
    V R l c d-(11/1000)*d≤Vnu R l k l d := by
  have ho := h.order
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,by dsimp [frameCap]; linarith [hd.2]⟩
  have hpen : 0≤(c-l)*(1-Real.cos d) :=
    mul_nonneg (sub_nonneg.mpr ho.2.2.1) (by linarith [Real.cos_le_one d])
  by_cases hck : c≤k
  · have hm := HalfRatioNormGain.larger_monotone hR.1 h.ell_pos ho.2.2.1 hck
      ho.2.2.2.2.2.1 hd'
    dsimp [V,Vnu,normGain] at *
    linarith
  · have hkc : k≤c := le_of_lt (lt_of_not_ge hck)
    have hm := coefficient_short hR ho.1 hkc ho.2.2.2.1
      (show l≤(18/25)*k by linarith [h.ell_k]) hd
    have hdif := mul_le_mul_of_nonneg_left h.difference.le
      (show 0≤(11/20)*d by positivity)
    dsimp [V,Vnu,normGain] at *
    nlinarith

theorem TD_endpoint {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    V (Real.sqrt q) (L q t) (Cc q t) t<secantCharge (Real.sqrt q) (Cc q t) 1 t := by
  have h := coefficient_bounds hq ht
  have hj := (minimizing_strip hq ht).1
  change 0<jD (Real.sqrt q) (L q t) (Cc q t) t at hj
  have hs : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [ht.1]) (by linarith [ht.2,Real.pi_gt_three])
  have hp := mul_pos (mul_pos (show 0<Cc q t by linarith [h.c_lower]) hs) hj
  rw [← TD_factor h.ell_pos (by linarith [h.c_lower]) h.angle] at hp
  linarith

theorem BT_endpoints {q t : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    V (Real.sqrt q) (L q t) (Cc q t) t+11/10000<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) shortAngle+
        V (Real.sqrt q) (L q t) (Cc q t) (t-shortAngle) ∧
    V (Real.sqrt q) (L q t) (Cc q t) t+3/10000<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) shortAngle+
        Vnu (Real.sqrt q) (L q t) (K q t) (L q t) (t-shortAngle) := by
  have h := coefficient_bounds hq ht
  have hj := (minimizing_strip hq ht).2
  change (7/500:ℝ)<jB (Real.sqrt q) (L q t) (Cc q t) t at hj
  have hs : (89/1000:ℝ)<Real.sin shortAngle := by
    have hh := sin_lower_seven (show (0:ℝ)≤shortAngle by norm_num [shortAngle])
    norm_num [shortAngle] at hh ⊢
    linarith
  have hcs : (37/40)*(89/1000)<Cc q t*Real.sin shortAngle :=
    mul_lt_mul h.c_lower hs (by norm_num) (by linarith [h.c_lower])
  have hp : (11/10000:ℝ)<Cc q t*Real.sin shortAngle*jB (Real.sqrt q) (L q t) (Cc q t) t := by
    have hm := mul_lt_mul hcs hj (by norm_num) (by nlinarith)
    nlinarith
  rw [← BT_factor h.ell_pos (by linarith [h.c_lower])
    (show t∈Icc shortAngle frameCap by constructor <;> dsimp [shortAngle,frameCap] <;>
      linarith [ht.1,ht.2])] at hp
  have hq0 : 0≤q := by norm_num [qLow] at hq; linarith [hq.1]
  have hR : Real.sqrt q≤2 := by
    have hq2 := Real.sq_sqrt hq0
    norm_num [qTrial] at hq
    nlinarith [Real.sqrt_nonneg q,hq.2]
  have hd : t-shortAngle∈Icc 0 (1/5:ℝ) := by
    constructor <;> dsimp [shortAngle] <;> linarith [ht.1,ht.2]
  have hA := A_lower ⟨Real.sqrt_nonneg q,hR⟩ h hd
  have hshort : t-shortAngle≤7/100 := by dsimp [shortAngle]; linarith [ht.2]
  constructor <;> nlinarith

end SquaresInCircles.Eight.TableFree.CriticalNegativeTGain
