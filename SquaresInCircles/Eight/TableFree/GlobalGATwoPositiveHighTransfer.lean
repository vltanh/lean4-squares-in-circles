module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveAEnvelope
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveWeights

/-!
# All six high A/T endpoint scalar inequalities

Uncompiled translation of Sections 5--7 of the complete two-positive
scalar proof.  The sorted D support is bounded by its full-circle
support, all six polynomial numerators are transferred through their
positive masses, and the B coefficient uses the stated common cap.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveTD
open PositiveTD.Certificate

abbrev kAt (t : ℝ) : ℝ := aeval t highK
abbrev lAt (t : ℝ) : ℝ := aeval t highL
abbrev cAt (t : ℝ) : ℝ := aeval t highC

def aAt : Endpoint→ℝ→ℝ | .atT,_ => 0 | .atA,t => t
def zAt : Endpoint→ℝ→ℝ | .atT,t => t | .atA,_ => 0
def mAt (e : Endpoint) (t : ℝ) : ℝ := tilted (cAt t) (zAt e t)

def endpointBase (e : Endpoint) (t : ℝ) : ℝ :=
  baseline (kAt t) (lAt t) (cAt t) (zAt e t)+lAt t*ASupport.charge (aAt e t)

def endpointNonradical (e : Endpoint) (t : ℝ) : ℝ :=
  2*kAt t+3*lAt t+(3/2)*mAt e t+cAt t/2+3+
    cAt t*edgeWidth (zAt e t)-cAt t*sigma*Real.sin (zAt e t)+
      lAt t*ASupport.charge (aAt e t)

theorem high_frame_domain {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩

theorem high_m_bounds (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<aeval t (highMMinus e) ∧ aeval t (highMMinus e)≤mAt e t ∧
      mAt e t≤aeval t (highMPlus e) ∧ mAt e t≤aeval t (highMu e) := by
  have hr := high_ranges ht
  have hc : 0<cAt t := by linarith [hr.2.2.2.2.1]
  cases e
  · have hm := tilted_polynomial_bounds (c:=highC) (high_frame_domain ht) hc
    have hcos := cos_upper_four (high_frame_domain ht).1
    have hsin := sin_upper_five (high_frame_domain ht).1
    have htilt : Real.cos t+eta*Real.sin t≤aeval t (C4+C etaQ*S5) := by
      norm_num [C4,S5,eta,etaQ]
      linarith
    have hmu := mul_le_mul_of_nonneg_left htilt hc.le
    refine ⟨hm.1,hm.2.1,hm.2.2,?_⟩
    simpa [highMu,mAt,zAt,tilted] using hmu
  · simpa [highMMinus,highMPlus,highMu,mAt,zAt,tilted] using
      (show 0<cAt t ∧ cAt t≤cAt t ∧ cAt t≤cAt t ∧ cAt t≤cAt t from
        ⟨hc,le_rfl,le_rfl,le_rfl⟩)

theorem high_Q_bound (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    max (lAt t) (mAt e t)≤aeval t highQ := by
  have hL : lAt t≤aeval t highQ := by
    norm_num only [highQ,map_add,map_mul,map_sub,aeval_C,aeval_X,h]
    dsimp [frameCap] at ht
    linarith [ht.2]
  apply max_le hL
  cases e
  · have hg := highQGap_positive ht
    have hm := (high_m_bounds .atT ht).2.2.2
    simp only [highQGap,map_sub] at hg
    simpa only [highMu] using hm.trans (show
      aeval t (highC*(C4+C etaQ*S5))≤aeval t highQ by linarith)
  · simpa [mAt,zAt,tilted] using (highQ_C_positive ht).le

theorem high_nonradical_lower (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    aeval t (highA e)≤endpointNonradical e t := by
  have hr := high_ranges ht
  have hl : 0≤lAt t := by linarith [hr.2.2.1]
  have hc : 0≤cAt t := by linarith [hr.2.2.2.2.1]
  cases e
  · have hm := (high_m_bounds .atT ht).2.1
    have htrig := taylor_bounds (high_frame_domain ht)
    have hs := sigma_sine_upper (high_frame_domain ht) hc
    have hw₀ := mul_le_mul_of_nonneg_left
      (add_le_add htrig.2.2.2.2.1 htrig.2.1) hc
    have hw : cAt t/2*(1+aeval t C10+aeval t S11)≤cAt t*edgeWidth t := by
      rw [edgeWidth_positive_formula (high_frame_domain ht)]
      nlinarith only [hw₀]
    norm_num only [highA,map_add,map_sub,map_mul,map_one,aeval_C]
    simp only [endpointNonradical,aAt,zAt,ASupport.charge_zero,mul_zero,add_zero]
    nlinarith only [hm,hs,hw]
  · have hA := mul_le_mul_of_nonneg_left (ASupport.high_polynomial_charge ht) hl
    have hw : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    norm_num only [highA,map_add,map_mul,aeval_C]
    simp only [endpointNonradical,mAt,aAt,zAt,tilted,Real.cos_zero,Real.sin_zero,
      mul_zero,mul_one,add_zero,sub_zero,hw]
    nlinarith only [hA]

theorem high_norm_bounds (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    (pairNorm (kAt t) 1 0)^2≤aeval t highPH ∧
    (pairNorm (kAt t) (lAt t) 0)^2≤aeval t highPG ∧
    (pairNorm (cAt t) 1 0)^2≤aeval t highPD ∧
    (pairNorm (lAt t) (mAt e t) 0)^2≤aeval t (highPB e) ∧
    (pairNorm (kAt t) 1 (-t))^2≤aeval t highPHminus ∧
    (pairNorm (kAt t) (lAt t) (-t))^2≤aeval t highPGminus ∧
    (pairNorm (lAt t) (mAt e t) (-t))^2≤aeval t (highPBminus e) := by
  have hr := high_ranges ht
  have hk : 0<kAt t := by linarith [hr.1]
  have hl : 0<lAt t := by linarith [hr.2.2.1]
  have hm := high_m_bounds e ht
  have hm0 : 0<mAt e t := hm.1.trans_le hm.2.1
  have hm2 : (mAt e t)^2≤(aeval t (highMPlus e))^2 :=
    pow_le_pow_left₀ hm0.le hm.2.2.1 2
  have hs := taylor_bounds (high_frame_domain ht)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [zero_norm_sq]
    simp [highPH,add_comm]
  · rw [zero_norm_sq]
    simp [highPG]
  · rw [zero_norm_sq]
    simp [highPD,add_comm]
  · rw [zero_norm_sq]
    simp only [highPB,map_add,map_pow]
    linarith
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) (high_frame_domain ht) hs.2.1
    norm_num only [highPHminus,highPH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hk hl (high_frame_domain ht) hs.2.1
    norm_num only [highPGminus,highPG,map_add,map_sub,map_mul,map_pow,aeval_C]
    nlinarith only [hh]
  · have hh := negative_norm_sq_le hl hm0 (high_frame_domain ht) hs.2.1
    have hp := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hm.2.1 hs.1) hl.le
    norm_num only [highPBminus,highPB,map_add,map_sub,map_mul,map_pow,aeval_C]
    nlinarith only [hh,hp,hm2]

theorem baseline_full_lower (k l c z a : ℝ) :
    2*k+3*l+(3/2)*tilted c z+c/2+3+c*edgeWidth z-c*sigma*Real.sin z+l*ASupport.charge a-
      R*(pairNorm k 1 0+pairNorm k l 0+pairNorm l (tilted c z) 0+pairNorm c 1 0)≤
        baseline k l c z+l*ASupport.charge a := by
  have hD := clippedSupport_le_fullSupport 1 c
  simp only [baseline,fullSupport_pair] at hD ⊢
  nlinarith only [hD]

theorem high_H_lower (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+Real.cos t-1-
      R*(pairNorm (kAt t) (lAt t) 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) 1 (-t)+pairNorm (cAt t) 1 0)≤
      endpointBase e t+V R (kAt t) 1 t := by
  have hh := baseline_full_lower (kAt t) (lAt t) (cAt t) (zAt e t) (aAt e t)
  dsimp [endpointNonradical,endpointBase,mAt,V]
  nlinarith only [hh]

theorem high_G_lower (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+lAt t*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (lAt t) (mAt e t) 0+
        pairNorm (kAt t) (lAt t) (-t)+pairNorm (cAt t) 1 0)≤
      endpointBase e t+V R (kAt t) (lAt t) t := by
  have hh := baseline_full_lower (kAt t) (lAt t) (cAt t) (zAt e t) (aAt e t)
  dsimp [endpointNonradical,endpointBase,mAt,V]
  nlinarith only [hh]

theorem sorted_pair_norm (l m s : ℝ) :
    pairNorm (min l m) (max l m) s=pairNorm l m s := by
  rcases le_total l m with h | h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,pairNorm_symm]

theorem high_B_lower (e : Endpoint) (t : ℝ) :
    endpointNonradical e t+max (lAt t) (mAt e t)*(Real.cos t-1)-
      R*(pairNorm (kAt t) 1 0+pairNorm (kAt t) (lAt t) 0+
        pairNorm (lAt t) (mAt e t) (-t)+pairNorm (cAt t) 1 0)≤
      endpointBase e t+V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  have hh := baseline_full_lower (kAt t) (lAt t) (cAt t) (zAt e t) (aAt e t)
  simp only [V,sorted_pair_norm]
  dsimp [endpointNonradical,endpointBase,mAt]
  nlinarith only [hh]

theorem high_H_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+V R (kAt t) 1 t := by
  have hn := high_norm_bounds e ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hA : aeval t (highA e+C10-1)≤endpointNonradical e t+Real.cos t-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [high_nonradical_lower e ht,htrig.2.2.2.2.1]
  have hrG : 0<aeval t highRG := by simpa only [mass,Matrix.cons_val_succ,Matrix.cons_val_zero]
    using masses_positive e 1 ht
  have hrB : 0<aeval t (highRB e) := by simpa only [mass,Matrix.cons_val_succ,Matrix.cons_val_zero]
    using masses_positive e 3 ht
  have hrH : 0<aeval t highRHminus := by simpa only [mass,Matrix.cons_val_succ,Matrix.cons_val_zero]
    using masses_positive e 4 ht
  have hrD : 0<aeval t highRD := by simpa only [mass,Matrix.cons_val_succ,Matrix.cons_val_zero]
    using masses_positive e 2 ht
  have hp := num4_transfer hrG hrB hrH hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.1 hA (highNH_positive e ht)
  exact hp.trans_le (high_H_lower e t)

theorem high_G_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+V R (kAt t) (lAt t) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1)
    (show 0≤lAt t by linarith [hr.2.2.1])
  have hA : aeval t (highA e+highL*(C10-1))≤
      endpointNonradical e t+lAt t*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrB : 0<aeval t (highRB e) := by simpa [mass] using masses_positive e 3 ht
  have hrG : 0<aeval t highRGminus := by simpa [mass] using masses_positive e 5 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrB hrG hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.1 hA (highNG_positive e ht)
  exact hp.trans_le (high_G_lower e t)

theorem high_B_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t := by
  have hn := high_norm_bounds e ht
  have hr := high_ranges ht
  have htrig := taylor_bounds (high_frame_domain ht)
  have hQ := high_Q_bound e ht
  have hQ0 : 0≤aeval t highQ := by
    have hlq := (le_max_left (lAt t) (mAt e t)).trans hQ
    linarith [hr.2.2.1]
  have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right htrig.2.2.2.2.1 1) hQ0
  have h₂ := mul_le_mul_of_nonpos_right hQ (sub_nonpos.mpr (Real.cos_le_one t))
  have hA : aeval t (highA e+highQ*(C10-1))≤endpointNonradical e t+
      max (lAt t) (mAt e t)*(Real.cos t-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e ht]
  have hrH : 0<aeval t highRH := by simpa [mass] using masses_positive e 0 ht
  have hrG : 0<aeval t highRG := by simpa [mass] using masses_positive e 1 ht
  have hrB : 0<aeval t (highRBminus e) := by simpa [mass] using masses_positive e 6 ht
  have hrD : 0<aeval t highRD := by simpa [mass] using masses_positive e 2 ht
  have hp := num4_transfer hrH hrG hrB hrD
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.1 hA (highNB_positive e ht)
  exact hp.trans_le (high_B_lower e t)

/-- Both all-A and all-T endpoints satisfy all three high alternatives. -/
theorem high_six_scalars_positive (e : Endpoint) {t : ℝ} (ht : t∈Icc (1/6:ℝ) frameCap) :
    0<endpointBase e t+V R (kAt t) 1 t ∧
    0<endpointBase e t+V R (kAt t) (lAt t) t ∧
    0<endpointBase e t+
      V R (min (lAt t) (mAt e t)) (max (lAt t) (mAt e t)) t :=
  ⟨high_H_positive e ht,high_G_positive e ht,high_B_positive e ht⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive.Certificate
