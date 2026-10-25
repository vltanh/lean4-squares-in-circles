module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Blocks
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSlopes

/-!
# Eight squares: all four ordinary far-low EH1/BT3 pairs

The unrotated B coefficient and rotated D
coefficient are not interchanged in the block sum. The familiar far-EH
range lemma is used only to prove their actual coefficient intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.FarLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope

lemma coefficient_ranges {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (hz : z∈Icc 0 θ) :
    Explicit.k .farLow θ=121/200 ∧ Explicit.l .farLow θ∈Icc (91/100:ℝ) 1 ∧
    Explicit.m .farLow θ∈Icc (367/400:ℝ) (111/100) ∧
    Explicit.l .farLow θ<Explicit.m .farLow θ ∧
    Explicit.m .farLow θ≤Explicit.c .farLow θ z ∧
    Explicit.c .farLow θ z≤111/100 ∧
    Explicit.c .farLow θ z<(117/100)*Explicit.l .farLow θ := by
  have hr := NegativeEHPositiveTD.Explicit.far_low_ranges hθ
  have hc := NegativeEHPositiveTD.Explicit.far_low_tilted hθ hz
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hc.1,hc.2.1,hc.2.2.2⟩

lemma pair_data {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    (3/5:ℝ)≤Blocks.p .farLow θ z i ∧ Blocks.p .farLow θ z i≤Blocks.q .farLow θ z i ∧
    Blocks.q .farLow θ z i≤(5/3)*Blocks.p .farLow θ z i ∧ Blocks.q .farLow θ z i≤111/100 := by
  have hr := coefficient_ranges hθ hz
  have hp := NegativeEHPositiveTD.Explicit.far_pairs .low hθ
    (show (0:ℝ)∈Icc 0 θ from ⟨le_rfl,hθ.1⟩)
  have hk : Explicit.k .farLow θ=121/200 := hr.1
  fin_cases i
  · change (3/5:ℝ)≤Explicit.k .farLow θ ∧ Explicit.k .farLow θ≤1 ∧
      (1:ℝ)≤(5/3)*Explicit.k .farLow θ ∧ (1:ℝ)≤111/100
    rw [hk]; norm_num
  · refine ⟨(hp 1).1,(hp 1).2.1,(hp 1).2.2,?_⟩
    change Explicit.l .farLow θ≤111/100
    linarith [hr.2.1.2]
  · change (3/5:ℝ)≤ min (Explicit.l .farLow θ) (Explicit.m .farLow θ) ∧
      min (Explicit.l .farLow θ) (Explicit.m .farLow θ)≤
        max (Explicit.l .farLow θ) (Explicit.m .farLow θ) ∧
      max (Explicit.l .farLow θ) (Explicit.m .farLow θ)≤
        (5/3)*min (Explicit.l .farLow θ) (Explicit.m .farLow θ) ∧
      max (Explicit.l .farLow θ) (Explicit.m .farLow θ)≤111/100
    rw [min_eq_left hr.2.2.2.1.le,max_eq_right hr.2.2.2.1.le]
    exact ⟨by linarith [hr.2.1.1],hr.2.2.2.1.le,
      by linarith [hr.2.1.1,hr.2.2.1.2],hr.2.2.1.2⟩
  · change (3/5:ℝ)≤ min 1 (Explicit.c .farLow θ z) ∧
      min 1 (Explicit.c .farLow θ z)≤ max 1 (Explicit.c .farLow θ z) ∧
      max 1 (Explicit.c .farLow θ z)≤(5/3)*min 1 (Explicit.c .farLow θ z) ∧
      max 1 (Explicit.c .farLow θ z)≤111/100
    rcases le_total (1:ℝ) (Explicit.c .farLow θ z) with hc|hc
    · rw [min_eq_left hc,max_eq_right hc]
      exact ⟨by norm_num,hc,by linarith [hr.2.2.2.2.2.1],hr.2.2.2.2.2.1⟩
    · rw [min_eq_right hc,max_eq_left hc]
      exact ⟨by linarith [hr.2.2.1.1,hr.2.2.2.2.1],hc,
        by linarith [hr.2.2.1.1,hr.2.2.2.2.1],by norm_num⟩

lemma positive_lower {θ z P : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (hP : P∈Icc 0 frameCap) (i : Fin 4) :
    -(12199/20000)*P≤Blocks.positive .farLow θ z P i := by
  have hp := pair_data hθ hz i
  have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    (show 0<Blocks.p .farLow θ z i by linarith [hp.1]) hp.2.1
    (show Blocks.q .farLow θ z i≤2*Blocks.p .farLow θ z i by linarith [hp.1,hp.2.2.1]) hP
  have hq := mul_le_mul_of_nonneg_right hp.2.2.2 hP.1
  simp only [Blocks.positive,ChargedOrdinaryConcentration.positive,epsilon,far,ite_true]
  nlinarith only [hu,hq]

lemma negative_HB {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (ht : t∈Icc 0 frameCap) :
    Blocks.ordinaryV .farLow θ 0 t≤Blocks.ordinaryV .farLow θ 2 t := by
  have hh := NegativeEHPositiveTD.FarLowSlopes.H_le_B hθ
    (show (0:ℝ)∈Icc 0 θ from ⟨le_rfl,hθ.1⟩) ht
  simpa [Blocks.ordinaryV,Blocks.ordinaryP,Blocks.ordinaryQ,
    NegativeEHPositiveTD.Explicit.V,NegativeEHPositiveTD.Explicit.p,NegativeEHPositiveTD.Explicit.q,
    NegativeEHPositiveTD.Explicit.k,NegativeEHPositiveTD.Explicit.l,
    NegativeEHPositiveTD.Explicit.m,NegativeEHPositiveTD.Explicit.c,
    Explicit.k,Explicit.l,Explicit.m] using hh

lemma negative_HD {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Blocks.ordinaryV .farLow θ 0 t≤Blocks.negative .farLow θ z t 3 := by
  have hr := coefficient_ranges hθ hz
  have hh := Blocks.D_redundant (k:=Explicit.k .farLow θ) (c:=Explicit.c .farLow θ z)
    (by norm_num [Explicit.k])
    (by rw [hr.1]; linarith [hr.2.2.1.1,hr.2.2.2.2.1])
    (by linarith [hr.2.2.2.2.2.1]) ht
  exact hh

lemma negative_representative {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    ∃j : Fin 2,Blocks.ordinaryV .farLow θ j.castSucc t≤Blocks.negative .farLow θ z t i := by
  fin_cases i
  · exact ⟨0,le_rfl⟩
  · exact ⟨1,le_rfl⟩
  · exact ⟨0,negative_HB hθ ht⟩
  · exact ⟨0,negative_HD hθ hz ht⟩

lemma positive_HG {θ z t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Blocks.positive .farLow θ z t 0≤Blocks.positive .farLow θ z t 1 := by
  have hh := NegativeEHPositiveTD.FarLowSlopes.H_le_G hθ hz ht
  simpa [Blocks.positive,ChargedOrdinaryConcentration.positive,Blocks.p,Blocks.q,
    PositiveBT3.pWeights,PositiveBT3.qWeights,
    NegativeEHPositiveTD.Explicit.U,NegativeEHPositiveTD.Explicit.p,NegativeEHPositiveTD.Explicit.q,
    Explicit.k,Explicit.l,NegativeEHPositiveTD.Explicit.k,NegativeEHPositiveTD.Explicit.l] using
    sub_le_sub_right hh (epsilon .farLow*t)

lemma small_total_c_ge_one {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/10)) (hz : z∈Icc 0 θ) :
    1≤Explicit.c .farLow θ z := by
  have hr := coefficient_ranges (show θ∈Icc (0:ℝ) (1/4) from ⟨hθ.1,by linarith [hθ.2]⟩) hz
  have hm : 1≤Explicit.m .farLow θ := by dsimp [Explicit.m]; linarith [hθ.2]
  exact hm.trans hr.2.2.2.2.1

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.FarLow
