module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3HighSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3SameBlock
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighConcentration

/-!
# Eight squares: high-total concentration for the DE3 / BT3 stress

Both signed mass caps are kept. Ordinary separated blocks use the whole or the shortened slope
reserve according to the sign of their surplus. The distinguished TD0 block uses the
secant-dependent `gamma` and the remaining-angle comparison, also when both signs are allocated to
that block. Every concentration alternative thus reduces to a pure signed surplus (`sum_to_pure`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighConcentration
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope

lemma ordinary_separated {θ s P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 frameCap) (hP : 0≤P) (hN : 0≤N)
    (hPb : P≤frameCap-θ) (hNb : N≤frameCap-s)
    (hbalance : N-P=θ-s) (i j : Fin 3) :
    (if s≤θ then Explicit.V .high θ j (θ-s) else Explicit.U .high θ i (s-θ))≤
      Explicit.U .high θ i P+Explicit.V .high θ j N := by
  have hi := Explicit.high_pairs hθ i
  have hj := Explicit.high_pairs hθ j
  have hip : Explicit.q .high θ i≤2*Explicit.p .high θ i := by linarith [hi.1,hi.2.2]
  have hqj := hj.1.trans_le hj.2.1
  have hPcap : P∈Icc 0 frameCap := ⟨hP,by linarith [hθ.1]⟩
  have hNcap : N∈Icc 0 frameCap := ⟨hN,by linarith [hs.1]⟩
  have hPshort : P∈Icc 0 (8/15:ℝ) := by
    dsimp [frameCap] at hPb
    exact ⟨hP,by linarith [hθ.1]⟩
  have hratio := Explicit.high_spread hθ i j
  by_cases hst : s≤θ
  · have hPN : P≤N := by linarith
    have hdiff : N-P∈Icc 0 frameCap := ⟨by linarith,by linarith [hNcap.2]⟩
    have hv := V_growth hj.1 hj.2.1 hj.2.2.le hdiff hNcap (by linarith)
    have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      hi.1 hi.2.1 hip hPcap
    have hpay := mul_nonneg
      (show 0≤(2/3)*Explicit.q .high θ j-(109/200)*Explicit.q .high θ i by
        nlinarith [hqj.le]) hP
    rw [hbalance] at hv
    simp only [ite_eq_left hst]
    dsimp [Explicit.U,Explicit.V]
    nlinarith
  · have hNP : N≤P := by linarith
    have hNshort : N∈Icc 0 (8/15:ℝ) := ⟨hN,hNP.trans hPshort.2⟩
    have hdiff : P-N∈Icc 0 (8/15:ℝ) := ⟨by linarith,by linarith [hPshort.2]⟩
    have hsurplus : P-N=s-θ := by linarith
    have hv := NegativeDEPositiveTD.OrdinarySlope.negative_short_growth hj.1 hj.2.1 hj.2.2.le
      (by norm_num : (0:ℝ)∈Icc 0 (8/15:ℝ)) hNshort hN
    have hu := NegativeDEPositiveTD.OrdinarySlope.positive_short_growth hi.1 hi.2.1 hip
      hdiff hPshort (by linarith)
    have hpay := mul_nonneg
      (show 0≤(39/50)*Explicit.q .high θ j-(16/25)*Explicit.q .high θ i by
        nlinarith [hqj.le]) hN
    simp only [V_zero,sub_zero] at hv
    rw [hsurplus] at hu
    simp only [ite_eq_right hst]
    dsimp [Explicit.U,Explicit.V]
    nlinarith

lemma D_separated {θ z s P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (hP : 0≤P) (hN : 0≤N)
    (_hPb : P≤frameCap-θ) (hNb : N≤frameCap-s)
    (hbalance : N-P=θ-s) (j : Fin 3) :
    (if s≤θ then Explicit.V .high θ j (θ-s)
      else -Explicit.gamma .high θ z s*(s-θ))≤
        -Explicit.gamma .high θ z s*P+Explicit.V .high θ j N := by
  by_cases hst : s≤θ
  · have hdiff : N-P∈Icc 0 (frameCap-s) := ⟨by linarith,by linarith⟩
    have hg := HighSlopes.gamma_growth hθ hz hs hdiff ⟨hN,hNb⟩ (by linarith) j
    rw [show N-(N-P)=P by ring,hbalance] at hg
    simp only [hst,↓reduceIte]
    linarith
  · have hg := HighSlopes.gamma_growth hθ hz hs
      (show (0:ℝ)∈Icc 0 (frameCap-s) from ⟨le_rfl,by linarith [hs.2]⟩)
      ⟨hN,hNb⟩ hN j
    have h0 : Explicit.V .high θ j 0=0 := by simp [Explicit.V,V_zero]
    rw [h0,sub_zero,sub_zero] at hg
    have hsurplus : s-θ=P-N := by linarith
    simp only [hst,↓reduceIte,hsurplus]
    linarith

lemma separated_lower {θ z s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (i j : Fin 4) :
    Blocks.pure .high θ z s i j≤
      Blocks.positive .high θ z s (frameCap-θ) i+
        Blocks.negative .high θ (frameCap-s) j := by
  have ht := Explicit.frame_domain .high hθ
  have hP : 0≤frameCap-θ := sub_nonneg.mpr ht.2
  have hN : 0≤frameCap-s := sub_nonneg.mpr hs.2
  have hbalance : frameCap-s-(frameCap-θ)=θ-s := by ring
  have hpure : Blocks.pure .high θ z s i j=if s≤θ then Blocks.negative .high θ (θ-s) j
      else Blocks.positive .high θ z s (s-θ) i := rfl
  rw [hpure]
  by_cases hi : i=3
  · subst i
    have hh := D_separated hθ hz hs hP hN le_rfl le_rfl hbalance (Blocks.ordinaryIndex j)
    rw [Blocks.positive_D,Blocks.positive_D,Blocks.negative_to_ordinary,
      Blocks.negative_to_ordinary]
    exact hh
  · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
    obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
      ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
    subst i
    have hh := ordinary_separated hθ hs hP hN le_rfl le_rfl hbalance r (Blocks.ordinaryIndex j)
    rw [Blocks.positive_ordinary,Blocks.positive_ordinary,Blocks.negative_to_ordinary,
      Blocks.negative_to_ordinary]
    exact hh

theorem saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (i j : Fin 4) :
    Blocks.pure .high θ z s i j≤Blocks.saturated .high θ z s i j := by
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .high θ z s 3 3=
          Blocks.block .high θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,Blocks.block,
          ↓reduceIte]
      rw [he,Blocks.block_D]
      exact separated_lower hθ hz hs 3 3
    · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
      obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
        ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
      subst i
      exact SameBlock.ordinary_saturated_lower .high hθ hs r
  · have he : Blocks.saturated .high θ z s i j=
        Blocks.positive .high θ z s (frameCap-θ) i+Blocks.negative .high θ (frameCap-s) j := by
      simp only [Blocks.saturated,ChargedHybridConcentration.saturated,hij,↓reduceIte]
      rfl
    rw [he]
    exact separated_lower hθ hz hs i j

/-- Every high-total allocation has a pure lower bound. The indices are scalar allocations, not
geometric witnesses. -/
theorem sum_to_pure {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,Blocks.pure .high θ z s i j≤∑k,Blocks.block .high θ z s (P k) (N k) k := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .high P N hθ hs hP hN hPb hNb hbalance
  rw [min_eq_left (saturated_lower hθ hz hs i j)] at hij
  exact ⟨i,j,hij⟩

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighConcentration
