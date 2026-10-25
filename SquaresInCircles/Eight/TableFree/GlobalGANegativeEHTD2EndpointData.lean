module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Ranges
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHGain

/-!
# Actual gain and circle-norm inputs for the genuine-EH endpoints

Uncompiled transfer data for the thirty-two endpoint numerators. The
shifted ordinary angle is retained independently of the coefficient
angle. Lower and upper tilted coefficients are applied in the exact
sign required by each squared norm. The EH multiplier and its constant
support loss remain in the actual gain throughout.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 taylor_bounds)

abbrev split_sum := NegativeDEPositiveTD.Certificate.split_sum
abbrev split_angles := @NegativeDEPositiveTD.Certificate.split_angles

theorem split_positive (r : Regime) (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left r f) (Explicit.right r f)) :
    0<Explicit.k r f θ ∧ 0<Explicit.l r f θ ∧
      0<Explicit.c r f θ ∧ 0<Explicit.splitM r f e θ := by
  apply Explicit.family_positive r f hθ
  exact (split_angles e (Explicit.family_frame_domain r f hθ)).2.1

theorem g_polynomial_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    aeval s gPoly≤NegativeEH.g s := by
  have ht := taylor_bounds hs
  have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (show (0:ℝ)≤82/125 by norm_num)
  simp only [gPoly,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast]
  dsimp only [NegativeEH.g,NegativeEH.K,NegativeEH.beta,K,beta]
  push_cast
  linarith only [hsin,hcos]

theorem G_polynomial_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    aeval s GPoly≤NegativeEH.G s := by
  have hh := mul_le_mul_of_nonneg_left (g_polynomial_lower hs)
    (show (0:ℝ)≤201/200 by norm_num)
  simp only [GPoly,map_sub,map_mul,aeval_C,eq_ratCast]
  dsimp only [NegativeEH.G,NegativeEH.p,p]
  push_cast
  linarith

theorem g_constant_lower (s : ℚ) (hs : (s:ℝ)∈Icc 0 frameCap) :
    (gStar s:ℝ)≤NegativeEH.g (s:ℝ) := by
  have hh := g_polynomial_lower hs
  rw [NegativeDEPositiveTD.Certificate.eval_rat] at hh
  simpa [gStar,gPoly] using hh

theorem G_constant_lower (s : ℚ) (hs : (s:ℝ)∈Icc 0 frameCap) :
    (GStar s:ℝ)≤NegativeEH.G (s:ℝ) := by
  have hh := G_polynomial_lower hs
  rw [NegativeDEPositiveTD.Certificate.eval_rat] at hh
  simpa [GStar,GPoly,gStar,gPoly] using hh

theorem zero_norm_upper {p q qHi : ℝ} (hp : 0<p) (hq : 0<q) (hhi : q≤qHi) :
    (pairNorm p q 0)^2≤p^2+qHi^2 := by
  have hh := PositiveTD.Certificate.zero_norm_sq p q
  rw [hh]
  have hsq := pow_le_pow_left₀ hq.le hhi 2
  linarith

theorem negative_norm_upper {p q qLo qHi t : ℝ}
    (hp : 0<p) (hq : 0<q) (hlo0 : 0≤qLo) (hlo : qLo≤q) (hhi : q≤qHi)
    (ht : t∈Icc 0 frameCap) :
    (pairNorm p q (-t))^2≤p^2+qHi^2-2*p*qLo*aeval t S11 := by
  have hnorm := pairNorm_sq hp hq (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)
  have htay := taylor_bounds ht
  have hprod := mul_le_mul hlo htay.2.1 htay.1 hq.le
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0≤2*p by positivity)
  have hsq := pow_le_pow_left₀ hq.le hhi 2
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hnorm
  nlinarith only [hnorm,hscaled,hsq]

theorem positive_norm_upper {p q qHi t : ℝ}
    (hp : 0<p) (hq : 0<q) (hhi : q≤qHi) (ht : t∈Icc 0 frameCap) :
    (pairNorm p q t)^2≤p^2+qHi^2+2*p*qHi*aeval t S9 := by
  have hnorm := pairNorm_sq hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have htay := taylor_bounds ht
  have hprod := mul_le_mul hhi htay.2.2.1 (transport_trig ht).2.2.1 (hq.le.trans hhi)
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0≤2*p by positivity)
  have hsq := pow_le_pow_left₀ hq.le hhi 2
  simp only [pairEnergy,pairProduct] at hnorm
  nlinarith only [hnorm,hscaled,hsq]

theorem far_tilted_bounds (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) :
    0<aeval θ (farMLo f e) ∧ aeval θ (farMLo f e)≤Explicit.splitM .far f e θ ∧
      Explicit.splitM .far f e θ≤aeval θ (farMHi f e) := by
  have hc := (split_positive .far f e hθ).2.2.1
  cases e
  · have hh := PositiveTD.Certificate.tilted_polynomial_bounds
      (c:=farC f) (Explicit.family_frame_domain .far f hθ) (by simpa using hc)
    simpa [farMLo,farMHi,Explicit.splitM,Explicit.splitT,Explicit.m,
      NegativeDEPositiveTD.Explicit.splitT,
      Explicit.eta,NegativeDEPositiveTD.Explicit.eta,PositiveTD.tilted,PositiveTD.eta,
      PositiveTD.Certificate.mMinus,PositiveTD.Certificate.mPlus] using hh
  · simpa [farMLo,farMHi,Explicit.splitM,Explicit.splitT,Explicit.m,
      NegativeDEPositiveTD.Explicit.splitT] using
      (show 0<Explicit.c .far f θ ∧ Explicit.c .far f θ≤Explicit.c .far f θ ∧
        Explicit.c .far f θ≤Explicit.c .far f θ from ⟨hc,le_rfl,le_rfl⟩)

theorem far_tilted_upper_simple (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) :
    Explicit.splitM .far f e θ≤aeval θ (farMu f e) := by
  have hc := (split_positive .far f e hθ).2.2.1
  have hf := Explicit.family_frame_domain .far f hθ
  cases e
  · have hs := sin_upper_five hf.1
    have hcos := cos_upper_four hf.1
    have hh := mul_le_mul_of_nonneg_left
      (show Real.cos θ+(293/1000)*Real.sin θ≤
        1-θ^2/2+θ^4/24+(293/1000)*(θ-θ^3/6+θ^5/120) by
          linarith) hc.le
    have hM : Explicit.splitM .far f .atT θ=
        Explicit.c .far f θ*(Real.cos θ+(293/1000)*Real.sin θ) := by
      simp [Explicit.splitM,Explicit.m,NegativeDEPositiveTD.Explicit.splitT,
        Explicit.eta,NegativeDEPositiveTD.Explicit.eta]
    have hU : aeval θ (farMu f .atT)=
        Explicit.c .far f θ*(1-θ^2/2+θ^4/24+(293/1000)*(θ-θ^3/6+θ^5/120)) := by
      simp only [farMu,C4,S5,map_mul,map_add,map_sub,map_one,map_pow,aeval_C,aeval_X,
        eq_ratCast,farC_eval,PositiveTD.Certificate.etaQ]
      push_cast
      ring
    rw [hM,hU]
    exact hh
  · simp [farMu,Explicit.splitM,Explicit.splitT,Explicit.m,NegativeDEPositiveTD.Explicit.splitT]

theorem far_qStar_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    max (Explicit.l .far .high θ) (Explicit.splitM .far .high e θ)≤aeval θ farQStar := by
  have hl : Explicit.l .far .high θ≤aeval θ farQStar := by
    simp only [farQStar,map_add,map_mul,map_sub,aeval_C,aeval_X,farL_eval]
    norm_num [PositiveTD.Certificate.h]
    linarith [hθ.2]
  apply max_le hl
  cases e
  · have hm := far_tilted_upper_simple .high .atT hθ
    have hq := far_qstar_T_positive hθ
    simp only [map_sub] at hq
    exact hm.trans (by linarith)
  · have hq := far_qstar_A_positive hθ
    simp only [map_sub,farC_eval] at hq
    simpa [Explicit.splitM,Explicit.splitT,Explicit.m,NegativeDEPositiveTD.Explicit.splitT]
      using (sub_pos.mp hq).le

theorem low_A_charge_quarter {a : ℝ} (ha : a∈Icc (0:ℝ) (1/4)) :
    aeval a J0≤TwoPositive.ASupport.charge a := by
  have hf : a∈Icc 0 frameCap := ⟨ha.1,by norm_num [frameCap]; linarith [ha.2]⟩
  have ht := taylor_bounds hf
  have hcut : a≤TwoPositive.ASupport.alpha := by linarith [ha.2,TwoPositive.ASupport.alpha_bounds.1]
  have hab := TwoPositive.ASupport.axial_le_abar
  have he : ((TwoPositive.Certificate.abar:ℚ):ℝ)=1414575672/1000000000 := by
    norm_num [TwoPositive.Certificate.abar]
  rw [he] at hab
  have h₂ := mul_le_mul_of_nonneg_right hab (transport_trig hf).2.2.1
  simp only [TwoPositive.ASupport.charge,hcut,↓reduceIte,TwoPositive.ASupport.axialCharge,
    J0,NegativeDEPositiveTD.Certificate.J0,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast]
  push_cast
  linarith only [ht.2.2.2.2.1,ht.2.2.1,h₂]

def farBaseActual (f : Family) (e : Split) (θ : ℝ) : ℝ :=
  2*Explicit.k .far f θ+3*Explicit.l .far f θ+(3/2)*Explicit.splitM .far f e θ+
    Explicit.c .far f θ/2+3+Explicit.c .far f θ*edgeWidth (Explicit.splitT e θ)-
    Explicit.c .far f θ*Explicit.sigma*Real.sin (Explicit.splitT e θ)+
    Explicit.l .far f θ*TwoPositive.ASupport.charge (Explicit.splitA e θ)

theorem far_nonradical_lower (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) :
    aeval θ (farB f e)≤farBaseActual f e θ := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive .far f e hθ
  have hf := Explicit.family_frame_domain .far f hθ
  have ht := taylor_bounds hf
  cases e
  · have htilt := (far_tilted_bounds f .atT hθ).2.1
    have hs := PositiveTD.Certificate.sigma_sine_upper hf hc.le
    have hW0 := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
    have hW : Explicit.c .far f θ/2*(1+aeval θ C10+aeval θ S11)≤
        Explicit.c .far f θ*edgeWidth θ := by
      rw [edgeWidth_positive_formula hf]
      nlinarith only [hW0]
    have hj : TwoPositive.ASupport.charge 0=0 := by
      rw [TwoPositive.ASupport.charge_low (by norm_num)]
      norm_num [TwoPositive.ASupport.axialCharge]
    have hsig : Explicit.sigma=PositiveTD.sigma := by
      simp [NegativeDEPositiveTD.Explicit.sigma,PositiveTD.sigma,NegativeDEPositiveTD.Explicit.eta]
    have hsb : ((PositiveTD.Certificate.sigmabar:ℚ):ℝ)=1415477291/1000000000 := by
      norm_num [PositiveTD.Certificate.sigmabar]
    rw [hsb] at hs
    simp only [farB,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,farK_eval,farL_eval,
      farC_eval]
    simp only [farBaseActual,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,hj,mul_zero,add_zero,hsig]
    push_cast
    linarith only [htilt,hs,hW]
  · have hJ : aeval θ (if f=.low then J0 else J1)≤TwoPositive.ASupport.charge θ := by
      cases f
      · exact low_A_charge_quarter hθ
      · have h1 := hθ.1
        simp only [Explicit.left,Explicit.u] at h1
        exact NegativeDEPositiveTD.AEnvelope.high_polynomial_charge
          ⟨by linarith,hf.2⟩
    have hJscaled := mul_le_mul_of_nonneg_left hJ hl.le
    have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    simp only [farB,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,farK_eval,farL_eval,
      farC_eval]
    simp only [farBaseActual,Explicit.splitA,Explicit.splitT,Explicit.splitM,Explicit.m,
      NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,hW]
    push_cast
    linarith only [hJscaled]

theorem far_baseline_identity (f : Family) (e : Split) (θ : ℝ) :
    Explicit.baseline .far f (Explicit.splitA e θ) (Explicit.splitT e θ)=farBaseActual f e θ-
      R*(pairNorm (Explicit.k .far f θ) 1 0+
        pairNorm (Explicit.k .far f θ) (Explicit.l .far f θ) 0+
        pairNorm (Explicit.l .far f θ) (Explicit.splitM .far f e θ) 0+
        pairNorm 1 (Explicit.c .far f θ) 0) := by
  simp only [Explicit.baseline,split_sum,Explicit.sortedD,Bool.false_eq_true,if_false,fullSupport_pair]
  rw [pairNorm_symm (Explicit.c .far f θ) 1 0]
  dsimp [farBaseActual,Explicit.splitM]
  ring

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Certificate
