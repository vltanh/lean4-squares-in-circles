module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2HighSplit
public import SquaresInCircles.Eight.TableFree.OrdinaryMixedShortReserve

/-!
# Complete far-EH high-total scalar exclusion

Uncompiled Section 5 of the remaining-error companion. The actual
negative mass is at most .6, since the original EH magnitude is at
least .1. The short-angle growth theorem pays every separated common
mass. The same-block reserve pays the .005 charge without discarding
opposite signed arguments. DE2 is kept as the fourth, distinguished
block throughout. The final negative surplus is concave in the actual
EH magnitude and uses both already proved intrinsic endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarHigh
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryAngleConcentration

lemma pair_data {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤Blocks.p .far .high θ z i ∧
      Blocks.p .far .high θ z i≤Blocks.q .far .high θ z i ∧
      Blocks.q .far .high θ z i≤(5/3)*Blocks.p .far .high θ z i :=
  Blocks.far_pair .high hθ hz i

lemma q_upper {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 4) : Blocks.q .far .high θ z i≤1 := by
  have hh := Explicit.far_high_q_le_one hθ hz (Blocks.ordinaryIndex i)
  fin_cases i <;> exact hh

lemma positive_lower {θ z P : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(11/20)*P≤Blocks.positive .far .high θ z P i := by
  have hp := pair_data hθ hz i
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    have hh := mul_le_mul_of_nonneg_right
      (show Blocks.dCost+Explicit.errorCharge .far≤(11/20:ℝ) by
        dsimp [Blocks.dCost,Explicit.errorCharge,NegativeEH.epsilon]
        linarith [diagonal_bounds.2]) hP.1
    linarith
  · have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (show 0<Blocks.p .far .high θ z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .high θ z i≤2*Blocks.p .far .high θ z i by linarith [hp.1,hp.2.2]) hP
    have hq := mul_le_mul_of_nonneg_right (q_upper hθ hz i) hP.1
    simp only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,if_neg hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    nlinarith

lemma separated_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i j : Fin 4) :
    Blocks.negative .far .high θ z (N-P) j≤
      Blocks.positive .far .high θ z P i+Blocks.negative .far .high θ z N j := by
  have hj := pair_data hθ hz j
  have hu := positive_lower hθ hz
    (show P∈Icc 0 frameCap from ⟨hP,by norm_num [frameCap]; linarith⟩) i
  have hv := OrdinaryNegativeShortSlope.V_growth
    (show 0<Blocks.p .far .high θ z j by linarith [hj.1]) hj.2.1
    (show (3/5)*Blocks.q .far .high θ z j≤Blocks.p .far .high θ z j by linarith [hj.2.2])
    (show N-P∈OrdinaryNegativeShortSlope.domain from ⟨by linarith,by linarith⟩)
    (show N∈OrdinaryNegativeShortSlope.domain from ⟨hP.trans hPN,hN⟩)
    (by linarith : N-P≤N)
  have hpay := mul_nonneg (show 0≤Blocks.p .far .high θ z j-3/5 by linarith [hj.1]) hP
  dsimp [Blocks.negative]
  nlinarith

lemma same_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) (i : Fin 4) :
    Blocks.negative .far .high θ z (N-P) i≤Blocks.block .far .high θ z P N i := by
  by_cases hi : i=3
  · subst i
    rw [Blocks.block_D]
    exact separated_lower hθ hz hP hPN hN 3 3
  · have hp := pair_data hθ hz i
    have hh := OrdinaryNegativeShortSlope.same_reserve (R:=R) hp.1 hp.2.2 hP hPN hN
    simp only [Blocks.block,Blocks.negative,ChargedHybridConcentration.block,
      PositiveTD.Hybrid.block,if_neg hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    linarith

lemma sum_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hs : s∈Icc (1/10:ℝ) (1/4))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j : Fin 3,Explicit.V .far .high θ z j (θ-s)≤
      ∑i,Blocks.block .far .high θ z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .far .high P N hθ hz hs hP hN hPb hNb hbalance
  have horder : s≤θ := by linarith [hθ.1,hs.2]
  have hPcap : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNcap : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  have hsat : Blocks.negative .far .high θ z (θ-s) j≤Blocks.saturated .far .high θ z s i j := by
    by_cases hsame : i=j
    · subst j
      have hh := same_lower hθ hz hPcap hPN hNcap i
      simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,↓reduceIte,
        Blocks.block,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
    · have hh := separated_lower hθ hz hPcap hPN hNcap i j
      simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,if_neg hsame,
        Blocks.positive,Blocks.negative,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  have hpure : Blocks.pure .far .high θ z s i j=Blocks.negative .far .high θ z (θ-s) j := by
    simp [Blocks.pure,ChargedHybridConcentration.pure,horder,Blocks.negative]
  rw [hpure,min_eq_left hsat,Blocks.negative_to_ordinary] at hij
  exact ⟨Blocks.ordinaryIndex j,hij⟩

lemma negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 3) :
    0<Explicit.baseline .far .high a z+NegativeEH.G s+
      Explicit.V .far .high (a+z) z i (a+z-s) := by
  have hp := Explicit.family_pairs .far .high hθ ⟨hz,by linarith⟩ i
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap] : (1/4:ℝ)≤frameCap)) (convex_Icc (1/10:ℝ) (1/4))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 hp.2.2)
    (a:=-1) (b:=a+z) (l:=1/10) (u:=1/4)
    (fun s hs => ⟨by linarith [hs.2,hθ.1],by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩)
  have hc := OrdinaryMixedShortReserve.constant_add (hg.add hv) (Explicit.baseline .far .high a z)
  have hc' : ConcaveOn ℝ (Icc (1/10:ℝ) (1/4)) (fun t => Explicit.baseline .far .high a z+
      NegativeEH.G t+Explicit.V .far .high (a+z) z i (a+z-t)) :=
    hc.congr (fun t _ => by
      simp only [Pi.add_apply,Explicit.V]
      rw [show -1*t+(a+z)=a+z-t by ring]
      ring)
  have h0 := HighSplit.far_cut_positive false hθ ha hz i
  have h1 := HighSplit.far_cut_positive true hθ ha hz i
  simp only [Bool.false_eq_true,↓reduceIte] at h0 h1
  have hh := concave_gt_of_endpoints (c:=0) hc' hs h0 h1
  exact hh

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .far .high a z s+
      ∑i,Blocks.block .far .high (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := sum_to_negative P N hθ ⟨hz,by linarith⟩ hs hP hN hPb hNb hbalance
  have hh := negative_positive hθ ha hz hs i
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarHigh
