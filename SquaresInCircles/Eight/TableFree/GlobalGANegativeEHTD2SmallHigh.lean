module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2HighSplit

/-!
# Complete small-EH high-total scalar exclusion

Uncompiled Section 4 of the small-error companion. The two signed
budgets imply negative surplus. Every common positive/negative mass is
removed using the original pair ratios, including the distinguished D
singleton. The remaining negative block is concave in the actual EH
magnitude, with its two proved intrinsic endpoints at zero and .1.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallHigh
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open OrdinaryAngleConcentration

theorem pair_data {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    0<Blocks.p .small .high θ z i ∧ Blocks.p .small .high θ z i≤Blocks.q .small .high θ z i ∧
      (2/3)*Blocks.q .small .high θ z i<Blocks.p .small .high θ z i := by
  have hp := NegativeDEPositiveTD.Explicit.high_pairs hθ hz
  fin_cases i
  · exact ⟨(hp 0).1,(hp 0).2.1,(hp 0).2.2.1⟩
  · exact ⟨(hp 1).1,(hp 1).2.1,(hp 1).2.2.1⟩
  · exact ⟨(hp 2).1,(hp 2).2.1,(hp 2).2.2.1⟩
  · exact ⟨(hp 0).1,(hp 0).2.1,(hp 0).2.2.1⟩

theorem q_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i j : Fin 4) :
    Blocks.q .small .high θ z i<(29/25)*Blocks.q .small .high θ z j := by
  have hh := NegativeDEPositiveTD.Explicit.high_q_ratio hθ hz (Blocks.ordinaryIndex i) (Blocks.ordinaryIndex j)
  fin_cases i <;> fin_cases j <;> exact hh

theorem positive_lower {θ z P : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(109/200)*Blocks.q .small .high θ z i*P≤Blocks.positive .small .high θ z P i := by
  have hp := pair_data hθ hz i
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    change -(109/200)*1*P≤ -(Blocks.dCost+0)*P
    have hh := mul_le_mul_of_nonneg_right
      (show Blocks.dCost≤109/200 by dsimp [Blocks.dCost]; linarith [diagonal_bounds.2]) hP.1
    nlinarith
  · have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1
      (show Blocks.q .small .high θ z i≤2*Blocks.p .small .high θ z i by linarith [hp.2.2]) hP
    simpa only [Blocks.positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
      if_neg hi,Explicit.errorCharge,zero_mul,sub_zero] using hh

theorem separated_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i j : Fin 4) :
    Blocks.negative .small .high θ z (N-P) j≤
      Blocks.positive .small .high θ z P i+Blocks.negative .small .high θ z N j := by
  have hi := pair_data hθ hz i
  have hj := pair_data hθ hz j
  have hqj := hj.1.trans_le hj.2.1
  have hu := positive_lower hθ hz ⟨hP,hPN.trans hN⟩ i
  have hv := V_growth hj.1 hj.2.1 hj.2.2.le
    (show N-P∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show N∈Icc 0 frameCap from ⟨hP.trans hPN,hN⟩) (by linarith)
  have hratio := q_ratio hθ hz i j
  have hpay := mul_nonneg (show 0≤(2/3)*Blocks.q .small .high θ z j-
      (109/200)*Blocks.q .small .high θ z i by nlinarith) hP
  dsimp [Blocks.negative]
  nlinarith

theorem same_lower {θ z P N : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i : Fin 4) :
    Blocks.negative .small .high θ z (N-P) i≤Blocks.block .small .high θ z P N i := by
  by_cases hi : i=3
  · subst i
    rw [Blocks.block_D]
    exact separated_lower hθ hz hP hPN hN 3 3
  · have hp := pair_data hθ hz i
    have hNc : N∈Icc 0 frameCap := ⟨hP.trans hPN,hN⟩
    have hsine : Blocks.q .small .high θ z i*Real.sin N≤Blocks.p .small .high θ z i := by
      have hh := mul_le_mul_of_nonneg_left (transport_trig hNc).2.2.2.1.le
        ((hp.1.trans_le hp.2.1).le)
      nlinarith [hp.2.2]
    have hh := NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le ⟨hP,hPN⟩ hNc hsine
    simpa only [Blocks.block,Blocks.negative,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      if_neg hi,Explicit.errorCharge,zero_mul,sub_zero] using hh

theorem sum_to_negative {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc (0:ℝ) (1/10))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃j : Fin 3,Explicit.V .small .high θ z j (θ-s)≤
      ∑i,Blocks.block .small .high θ z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .small .high P N hθ hz hs hP hN hPb hNb hbalance
  have horder : s≤θ := by linarith [hθ.1,hs.2]
  have hPcap : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hPN : frameCap-θ≤frameCap-s := by linarith
  have hNcap : frameCap-s≤frameCap := by linarith [hs.1]
  have hsat : Blocks.negative .small .high θ z (θ-s) j≤Blocks.saturated .small .high θ z s i j := by
    by_cases hsame : i=j
    · subst j
      have hh := same_lower hθ hz hPcap hPN hNcap i
      rw [show frameCap-s-(frameCap-θ)=θ-s by ring] at hh
      rw [Blocks.saturated,ChargedHybridConcentration.saturated,if_pos rfl]
      exact hh
    · have hh := separated_lower hθ hz hPcap hPN hNcap i j
      simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,if_neg hsame,
        Blocks.positive,Blocks.negative,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  have hpure : Blocks.pure .small .high θ z s i j=Blocks.negative .small .high θ z (θ-s) j := by
    simp [Blocks.pure,ChargedHybridConcentration.pure,horder,Blocks.negative]
  rw [hpure,min_eq_left hsat,Blocks.negative_to_ordinary] at hij
  exact ⟨Blocks.ordinaryIndex j,hij⟩

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 3) :
    0<Explicit.baseline .small .high a z+NegativeEH.g s+
      Explicit.V .small .high (a+z) z i (a+z-s) := by
  have hp := NegativeDEPositiveTD.Explicit.high_pairs hθ ⟨hz,by linarith⟩ i
  have hg := NegativeEH.g_concave.subset
    (Icc_subset_Icc le_rfl (by norm_num [frameCap] : (1/10:ℝ)≤frameCap)) (convex_Icc 0 (1/10))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 (by linarith [hp.2.2.1]))
    (a:=-1) (b:=a+z) (l:=0) (u:=1/10)
    (fun s hs => ⟨by linarith [hs.2,hθ.1],by simp only [frameCap]; linarith [hs.1,hθ.2]⟩)
  have hc := TwoPositive.Split.add_constant (hg.add hv) (Explicit.baseline .small .high a z)
  have hg0 : NegativeEH.g 0=0 := by simp [NegativeEH.g]
  have h0 : 0<NegativeEH.g 0+V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
      (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (-1*0+(a+z))+
      Explicit.baseline .small .high a z := by
    have h : 0<Explicit.baseline .small .high a z+V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
        (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (a+z) :=
      HighSplit.small_zero_positive hθ ha hz i
    rw [hg0,show -1*(0:ℝ)+(a+z)=a+z by ring]
    linarith
  have h1 : 0<NegativeEH.g (1/10)+V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
      (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (-1*(1/10)+(a+z))+
      Explicit.baseline .small .high a z := by
    have h : 0<Explicit.baseline .small .high a z+NegativeEH.g (1/10)+
        V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
        (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (a+z-1/10) :=
      HighSplit.small_v_positive hθ ha hz i
    rw [show -1*(1/10:ℝ)+(a+z)=a+z-1/10 by ring]
    linarith
  have hh := concave_gt_of_endpoints (c:=0) hc hs h0 h1
  simp only [Pi.add_apply,show -1*s+(a+z)=a+z-s by ring] at hh
  change 0<Explicit.baseline .small .high a z+NegativeEH.g s+
    V R (NegativeDEPositiveTD.Explicit.p .high (a+z) z i)
      (NegativeDEPositiveTD.Explicit.q .high (a+z) z i) (a+z-s)
  linarith

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .small .high a z s+
      ∑i,Blocks.block .small .high (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := sum_to_negative P N hθ ⟨hz,by linarith⟩ hs hP hN hPb hNb hbalance
  have hh := negative_positive hθ ha hz hs i
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallHigh
