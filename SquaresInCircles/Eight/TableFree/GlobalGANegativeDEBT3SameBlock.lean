module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3PositivePure
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHSameBlock
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3LowSameBlock

/-!
# Every ordinary same-block alternative in the negative-DE / BT3 stress

Uncompiled Sections 4.1, 4.2 and 5 of the hand proof. The positive
surplus comparison uses the whole ratio bound 341/200 and the actual
cap 7/10. Low H/G negative surplus retains its correlated low-family
correction. The high family and the low B pair use the exact signed
same-block identity. Neither signed mass is discarded prematurely.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.SameBlock
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma cap_cosine_loss {t : ℝ} (ht : t∈Icc 0 frameCap) :
    1-Real.cos t≤(183/500)*Real.sin t := by
  have hd (x : ℝ) : HasDerivAt
      (fun x => (183/500)*Real.sin x+Real.cos x-1)
      ((183/500)*Real.cos x-Real.sin x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (183/500)).add
      (Real.hasDerivAt_cos x)).sub_const 1 using 1 <;> ring
  have hdd (x : ℝ) : HasDerivAt
      (fun x => (183/500)*Real.cos x-Real.sin x)
      (-(183/500)*Real.sin x-Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (183/500)).sub
      (Real.hasDerivAt_sin x) using 1 <;> ring
  have hc : ConcaveOn ℝ (Icc 0 frameCap)
      (fun x => (183/500)*Real.sin x+Real.cos x-1) := by
    apply concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x)
    intro x hx
    have hh := transport_trig hx
    linarith [hh.1,hh.2.2.1]
  have he : 0≤(183/500)*Real.sin frameCap+Real.cos frameCap-1 := by
    have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
    have hh := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
    norm_num [frameCap] at hs hh ⊢
    linarith
  have hh := hc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,zero_add,sub_self,
    min_eq_left he] at hh
  linarith

/-- Whole-cap positive-surplus comparison, including either zero mass. -/
theorem positive {p q P N : ℝ} (hp : 0≤p) (hqp : q≤(341/200)*p)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hn : N∈Icc 0 frameCap := ⟨hN,hNP.trans hP⟩
  have hsin := (transport_trig hn).2.2.1
  have hloss := cap_cosine_loss hn
  have hloss0 : 0≤1-Real.cos N := sub_nonneg.mpr (Real.cos_le_one N)
  have hcap := NegativeEH.SameBlock.cap_phi
  have hfirst := mul_le_mul_of_nonneg_right hcap.1.le hloss0
  have hsecond := mul_le_mul_of_nonneg_right hcap.2.le hsin
  have hid : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)+
      (341/200)*(Real.cos N-1)=
      (PositiveAngularEnvelope.phi frameCap-341/200)*(1-Real.cos N)+
        (Real.cos frameCap-Real.sin frameCap)*Real.sin N := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  have hbracket : 0≤PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)+
      (341/200)*(Real.cos N-1) := by
    rw [hid]
    nlinarith only [hfirst,hsecond,hloss,hsin,hloss0]
  have hscaled := mul_nonneg hp hbracket
  have hdiff := mul_le_mul_of_nonneg_left
    (NegativeEH.SameBlock.phi_difference hN hNP hP) hp
  have hcoef := mul_le_mul_of_nonpos_right hqp
    (sub_nonpos.mpr (Real.cos_le_one N))
  have he : mixedBlock R p q P N-U R p q (P-N)=
      p*(PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N))+q*(Real.cos N-1) := by
    dsimp [mixedBlock,U]
    ring
  rw [←sub_nonneg,he]
  nlinarith only [hscaled,hdiff,hcoef]

lemma family_ratio (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 3) :
    Explicit.q f θ i≤(341/200)*Explicit.p f θ i := by
  cases f
  · have hb := Explicit.low_bounds hθ
    have hm : 1≤Explicit.m .low θ := by linarith [hb.2.1]
    fin_cases i
    · change (1:ℝ)≤(341/200)*Explicit.k .low θ
      linarith [hb.1.1]
    · change (1:ℝ)≤(341/200)*Explicit.k .low θ
      linarith [hb.1.1]
    · change max 1 (Explicit.m .low θ) ≤ (341/200)*min 1 (Explicit.m .low θ)
      rw [min_eq_left hm,max_eq_right hm]
      linarith [hb.2.2]
  · have hh := Explicit.high_pairs hθ i
    linarith [hh.1,hh.2.2]

lemma sine_monotone : MonotoneOn Real.sin (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (Real.hasDerivAt_sin x).continuousAt.continuousWithinAt)
    (fun x _ => Real.hasDerivAt_sin x)
  intro x hx
  linarith [(transport_trig (Ioo_subset_Icc_self hx)).1]

lemma shifted_cosine_difference {θ s : ℝ}
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 θ) :
    Real.cos frameCap-Real.cos θ≤Real.cos (frameCap-s)-Real.cos (θ-s) := by
  have hcos : Real.cos frameCap≤Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
      (by norm_num [frameCap]; linarith [Real.pi_gt_three]) hθ.2
  have hsin := sine_monotone hθ
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hθ.2
  have hss := (transport_trig (show s∈Icc 0 frameCap from ⟨hs.1,hs.2.trans hθ.2⟩)).2.2.1
  have h₁ := mul_nonneg_of_nonpos_of_nonpos
    (sub_nonpos.mpr hcos) (sub_nonpos.mpr (Real.cos_le_one s))
  have h₂ := mul_nonneg (sub_nonneg.mpr hsin) hss
  rw [Real.cos_sub,Real.cos_sub]
  nlinarith only [h₁,h₂]

theorem low_H_negative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 θ) :
    V R (Explicit.k .low θ) 1 (θ-s)≤
      mixedBlock R (Explicit.k .low θ) 1 (frameCap-θ) (frameCap-s) := by
  have ht := Explicit.frame_domain .low hθ
  have hc := PositiveBT3.LowEnvelope.correction_positive hθ
  have hh := shifted_cosine_difference ht hs
  have he : mixedBlock R (Explicit.k .low θ) 1 (frameCap-θ) (frameCap-s)-
      V R (Explicit.k .low θ) 1 (θ-s)=
      Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
        Real.cos (frameCap-s)-Real.cos (θ-s) := by
    dsimp [mixedBlock,V]
    rw [show frameCap-θ-(frameCap-s)= -(θ-s) by ring]
    ring
  dsimp [PositiveBT3.LowEnvelope.correction] at hc
  change 0<Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+Real.cos frameCap-Real.cos θ at hc
  rw [←sub_nonneg,he]
  linarith

theorem low_negative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 θ) (i : Fin 3) :
    Explicit.V .low θ i (θ-s)≤ mixedBlock R (Explicit.p .low θ i)
      (Explicit.q .low θ i) (frameCap-θ) (frameCap-s) := by
  have ht := Explicit.frame_domain .low hθ
  have hm := (Explicit.low_bounds hθ).2
  have hm1 : 1≤Explicit.m .low θ := by linarith [hm.1]
  fin_cases i
  · exact low_H_negative hθ hs
  · simpa [Explicit.V,Explicit.p,Explicit.q,Explicit.l] using low_H_negative hθ hs
  · have hN : frameCap-s∈Icc 0 frameCap :=
      ⟨by linarith [hs.2,ht.2],by linarith [hs.1]⟩
    have hsin := mul_le_mul_of_nonneg_left (transport_trig hN).2.2.2.1.le
      (show 0≤Explicit.m .low θ by linarith [hm.1])
    have hh := NegativeAPositiveTD.SameBlock.negative_surplus
      (p:=(1:ℝ)) (q:=Explicit.m .low θ) (by norm_num)
      (show frameCap-θ∈Icc 0 (frameCap-s) from
        ⟨by linarith [ht.2],by linarith [hs.2]⟩) hN
      (show Explicit.m .low θ*Real.sin (frameCap-s)≤1 by nlinarith [hm.2])
    change V R (min 1 (Explicit.m .low θ)) (max 1 (Explicit.m .low θ)) (θ-s) ≤
      mixedBlock R (min 1 (Explicit.m .low θ)) (max 1 (Explicit.m .low θ)) (frameCap-θ) (frameCap-s)
    rw [min_eq_left hm1,max_eq_right hm1,show θ-s=frameCap-s-(frameCap-θ) by ring]
    exact hh

theorem high_negative {θ P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i : Fin 3) :
    Explicit.V .high θ i (N-P)≤
      mixedBlock R (Explicit.p .high θ i) (Explicit.q .high θ i) P N := by
  have hp := Explicit.high_pairs hθ i
  have hn : N∈Icc 0 frameCap := ⟨hP.trans hPN,hN⟩
  have hsin := mul_le_mul_of_nonneg_left (transport_trig hn).2.2.2.1.le
    (hp.1.trans_le hp.2.1).le
  exact NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le ⟨hP,hPN⟩ hn
    (by nlinarith [hp.2.2])

/-- All ordinary same-block endpoints, with no restriction on the surplus sign. -/
theorem ordinary_saturated_lower (f : Family) {θ z s : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f))
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    Blocks.pure f θ z s i.castSucc i.castSucc≤
      Blocks.saturated f θ z s i.castSucc i.castSucc := by
  have ht := Explicit.frame_domain f hθ
  have hP : 0≤frameCap-θ := sub_nonneg.mpr ht.2
  have hN : 0≤frameCap-s := sub_nonneg.mpr hs.2
  have hsat : Blocks.saturated f θ z s i.castSucc i.castSucc=
      Blocks.block f θ z s (frameCap-θ) (frameCap-s) i.castSucc := by
    simp only [Blocks.saturated,ChargedHybridConcentration.saturated,
      Blocks.block,↓reduceIte]
  rw [hsat,Blocks.block_ordinary]
  by_cases he : s≤θ
  · have hpure : Blocks.pure f θ z s i.castSucc i.castSucc=
        Blocks.negative f θ (θ-s) i.castSucc := by
      simp only [Blocks.pure,ChargedHybridConcentration.pure,if_pos he,Blocks.negative]
    rw [hpure,Blocks.negative_ordinary]
    cases f
    · exact low_negative hθ ⟨hs.1,he⟩ i
    · have hh := high_negative hθ hP (by linarith : frameCap-θ≤frameCap-s)
        (by linarith [hs.1] : frameCap-s≤frameCap) i
      simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  · have hpure : Blocks.pure f θ z s i.castSucc i.castSucc=
        Blocks.positive f θ z s (s-θ) i.castSucc := by
      simp only [Blocks.pure,ChargedHybridConcentration.pure,if_neg he,Blocks.positive]
    rw [hpure,Blocks.positive_ordinary]
    have hp := Explicit.family_pairs f hθ i
    have hh := positive hp.1.le (family_ratio f hθ i) hN
      (by linarith : frameCap-s≤frameCap-θ) (by linarith [ht.1] : frameCap-θ≤frameCap)
    simpa only [show frameCap-θ-(frameCap-s)=s-θ by ring,Explicit.U] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.SameBlock
