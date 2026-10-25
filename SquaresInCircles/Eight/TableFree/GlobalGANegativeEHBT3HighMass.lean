module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3HighSplit

/-!
# Removing all common signed mass in both high-total EH1/BT3 families

Uncompiled Sections 5 and 7. The four actual ordinary blocks remain
separate throughout concentration. Small-high uses the original common
coefficient scale; far-high uses the .6 bound on total negative mass.
The far EH charge is paid by the same-block reserve and the separated
negative-slope reserve, not dropped after concentrating the masses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.HighMass
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeSlope

lemma reduce_negative (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hpair : ∀i,0<Blocks.p f θ z i ∧ Blocks.p f θ z i≤Blocks.q f θ z i ∧
      Blocks.q f θ z i≤2*Blocks.p f θ z i)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 θ)
    (hsame : ∀i,Blocks.negative f θ z (θ-s) i≤
      Blocks.block f θ z (frameCap-θ) (frameCap-s) i)
    (hsep : ∀i j,Blocks.negative f θ z (θ-s) j≤
      Blocks.positive f θ z (frameCap-θ) i+Blocks.negative f θ z (frameCap-s) j)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j,Blocks.negative f θ z (θ-s) j≤∑i,Blocks.block f θ z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate f P N hpair hθ ⟨hs.1,hs.2.trans hθ.2⟩
    hP hN hPb hNb hbalance
  have hsat : Blocks.negative f θ z (θ-s) j≤Blocks.saturated f θ z s i j := by
    by_cases he : i=j
    · subst j
      simpa only [Blocks.saturated,ChargedOrdinaryConcentration.saturated,↓reduceIte,
        Blocks.block] using hsame i
    · simpa only [Blocks.saturated,ChargedOrdinaryConcentration.saturated,ite_eq_right he,
        Blocks.positive,Blocks.negative] using hsep i j
  have hpure : Blocks.pure f θ z s i j=Blocks.negative f θ z (θ-s) j := by
    simp only [Blocks.pure,ChargedOrdinaryConcentration.pure,ite_eq_left hs.2,Blocks.negative]
  rw [hpure,min_eq_left hsat] at hij
  exact ⟨j,hij⟩

lemma small_high_same {θ z P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i : Fin 4) :
    Blocks.negative .smallHigh θ z (N-P) i≤Blocks.block .smallHigh θ z P N i := by
  have hp := Blocks.small_high_pairs hθ hz i
  have hNc : N∈Icc 0 frameCap := ⟨hP.trans hPN,hN⟩
  have hq : 0≤Blocks.q .smallHigh θ z i := (hp.1.trans_le hp.2.1).le
  have hsin := mul_le_mul_of_nonneg_left (transport_trig hNc).2.2.2.1.le hq
  have hsine : Blocks.q .smallHigh θ z i*Real.sin N≤Blocks.p .smallHigh θ z i := by
    nlinarith [hp.2.2]
  have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le ⟨hP,hPN⟩ hNc hsine
  simpa only [Blocks.block,Blocks.negative,ChargedOrdinaryConcentration.block,
    epsilon,far,Bool.false_eq_true,if_false,zero_mul,sub_zero] using hh

lemma small_high_separated {θ z P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i j : Fin 4) :
    Blocks.negative .smallHigh θ z (N-P) j≤
      Blocks.positive .smallHigh θ z P i+Blocks.negative .smallHigh θ z N j := by
  have hi := Blocks.small_high_pairs hθ hz i
  have hj := Blocks.small_high_pairs hθ hz j
  have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    hi.1 hi.2.1 (by linarith [hi.1,hi.2.2]) ⟨hP,hPN.trans hN⟩
  have hv := V_growth hj.1 hj.2.1 hj.2.2
    (show N-P∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show N∈Icc 0 frameCap from ⟨hP.trans hPN,hN⟩) (by linarith)
  have hscalei := Blocks.small_high_scale hθ hz i
  have hscalej := Blocks.small_high_scale hθ hz j
  have hq : 0<Blocks.q .smallHigh θ z j := hj.1.trans_le hj.2.1
  have hmargin : 0≤(2/3)*Blocks.q .smallHigh θ z j-
      (109/200)*Blocks.q .smallHigh θ z i := by linarith
  have hpay := mul_nonneg hmargin hP
  simp only [Blocks.positive,Blocks.negative,ChargedOrdinaryConcentration.positive,
    epsilon,far,Bool.false_eq_true,if_false,zero_mul,sub_zero]
  nlinarith only [hu,hv,hpay]

lemma small_high_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc (0:ℝ) (1/10))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j,Blocks.negative .smallHigh θ z (θ-s) j≤∑i,Blocks.block .smallHigh θ z (P i) (N i) i := by
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have he : s≤θ := by linarith [hs.2,hθ.1]
  have hPc : 0≤frameCap-θ := by linarith [ht.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNc : frameCap-s≤frameCap := by linarith [hs.1]
  apply reduce_negative .smallHigh P N
    (fun i => ⟨(Blocks.small_high_pairs hθ hz i).1,(Blocks.small_high_pairs hθ hz i).2.1,
      by linarith [(Blocks.small_high_pairs hθ hz i).1,(Blocks.small_high_pairs hθ hz i).2.2]⟩)
    ht ⟨hs.1,he⟩
  · intro i
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      small_high_same hθ hz hPc hPN hNc i
  · intro i j
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      small_high_separated hθ hz hPc hPN hNc i j
  all_goals assumption

lemma far_high_positive_lower {θ z P : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(11/20)*P≤Blocks.positive .farHigh θ z P i := by
  have hp := Blocks.far_high_pairs hθ hz i
  have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<Blocks.p .farHigh θ z i by linarith [hp.1]) hp.2.1
    (show Blocks.q .farHigh θ z i≤2*Blocks.p .farHigh θ z i by linarith [hp.1,hp.2.2.1]) hP
  have hq := mul_le_mul_of_nonneg_right hp.2.2.2 hP.1
  simp only [Blocks.positive,ChargedOrdinaryConcentration.positive,epsilon,far,if_true]
  nlinarith only [hh,hq]

lemma far_high_same {θ z P N : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i : Fin 4) :
    Blocks.negative .farHigh θ z (N-P) i≤Blocks.block .farHigh θ z P N i := by
  have hp := Blocks.far_high_pairs hθ hz i
  have hh := OrdinaryNegativeShortSlope.same_reserve (R:=R) hp.1 hp.2.2.1 hP hPN hN
  simp only [Blocks.block,Blocks.negative,ChargedOrdinaryConcentration.block,epsilon,far,if_true]
  linarith

lemma far_high_separated {θ z P N : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i j : Fin 4) :
    Blocks.negative .farHigh θ z (N-P) j≤
      Blocks.positive .farHigh θ z P i+Blocks.negative .farHigh θ z N j := by
  have hp := Blocks.far_high_pairs hθ hz j
  have hu := far_high_positive_lower hθ hz
    (show P∈Icc 0 frameCap from ⟨hP,by norm_num [frameCap]; linarith⟩) i
  have hv := OrdinaryNegativeShortSlope.V_growth
    (show 0<Blocks.p .farHigh θ z j by linarith [hp.1]) hp.2.1
    (show (3/5)*Blocks.q .farHigh θ z j≤Blocks.p .farHigh θ z j by linarith [hp.2.2.1])
    (show N-P∈OrdinaryNegativeShortSlope.domain from ⟨by linarith,by linarith⟩)
    (show N∈OrdinaryNegativeShortSlope.domain from ⟨hP.trans hPN,hN⟩) (by linarith)
  have hpay := mul_nonneg (sub_nonneg.mpr hp.1) hP
  dsimp [Blocks.negative]
  nlinarith only [hu,hv,hpay,hP]

lemma far_high_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc (1/10:ℝ) (1/4))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j,Blocks.negative .farHigh θ z (θ-s) j≤∑i,Blocks.block .farHigh θ z (P i) (N i) i := by
  have ht : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩
  have he : s≤θ := by linarith [hs.2,hθ.1]
  have hPc : 0≤frameCap-θ := by linarith [ht.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNc : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  apply reduce_negative .farHigh P N
    (fun i => ⟨by linarith [(Blocks.far_high_pairs hθ hz i).1],
      (Blocks.far_high_pairs hθ hz i).2.1,
      by linarith [(Blocks.far_high_pairs hθ hz i).1,(Blocks.far_high_pairs hθ hz i).2.2.1]⟩)
    ht ⟨by linarith [hs.1],he⟩
  · intro i
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      far_high_same hθ hz hPc hPN hNc i
  · intro i j
    simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using
      far_high_separated hθ hz hPc hPN hNc i j
  all_goals assumption

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.HighMass
