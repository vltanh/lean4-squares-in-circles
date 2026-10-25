module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighDerivative
public import SquaresInCircles.Eight.TableFree.OrdinaryAngleConcentration

/-!
# Removing all common signed mass in the high negative-DE family

Uncompiled transcription of Section 8.  Both original ordinary totals
are first concentrated without alteration.  The surplus retains its
sign, and the two uniform slope reserves remove the common mass even
when the positive and negative totals occupy different original blocks.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
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
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD
