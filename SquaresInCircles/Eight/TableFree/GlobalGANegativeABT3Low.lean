module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LowSeparated
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3High

/-!
# All low saturated alternatives and the complete reference scalar theorem

Uncompiled Sections 5--8. The same-block H/B comparisons retain their
exact surplus. The positive allowance .68125(h-z) includes the widened
D cost. The final finite-sum theorem uses both original signed budgets.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Low
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryPositiveEnvelope

theorem positive_allowance (atG : Bool) {s z : ℝ} (hz : z∈Icc 0 (1/4:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i : Fin 4) :
    -LowSeparated.allowance z≤Concentration.positive .low
      (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z) := by
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by dsimp [frameCap]; linarith [hz.2],by linarith [hz.1]⟩
  by_cases hi : i=3
  · subst i
    simp only [Concentration.positive,PositiveTD.Hybrid.positive,↓reduceIte,LowSeparated.allowance]
    nlinarith [hP.1]
  · have hc := Explicit.ordered_pair_domain .low atG hz hs i
    have hq := Explicit.low_q_upper atG hz hs i
    have hu := U_lower (Real.sqrt_nonneg _) radius_sq.le hc.1 hc.2.1 hc.2.2 hP
    have hh := mul_le_mul_of_nonneg_right hq.le hP.1
    simp only [Concentration.positive,PositiveTD.Hybrid.positive,↓reduceIte,if_neg hi,
      LowSeparated.allowance]
    nlinarith only [hu,hh]

theorem separated_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.p .low atG z s j) (Explicit.q .low atG z s j) (frameCap-s) := by
  have hu := positive_allowance atG hz hs i
  have hH := LowSeparated.H_positive atG hz hs
  have hG := LowSeparated.G_positive atG hz hs
  have hsf := (Explicit.angle_domain atG hs).2
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  fin_cases j
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s)
    linarith
  · have hB := LowNegative.B_dominates_H atG hz hs hN
    linarith
  · change 0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.positive .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i (frameCap-z)+
        V R (Explicit.k .low z) 1 (frameCap-s)
    linarith

theorem HB_pure_le_same (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i : Fin 4) (hi : i=0∨i=2) :
    Concentration.pure .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i i s z≤
      mixedBlock R (Explicit.p .low atG z s i) (Explicit.q .low atG z s i) (frameCap-z) (frameCap-s) := by
  have hc := Explicit.ordered_pair_domain .low atG hz hs i
  have hr := Explicit.low_HB_ratio atG hz hs i hi
  have hsf := (Explicit.angle_domain atG hs).2
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by dsimp [frameCap]; linarith [hz.2],by linarith [hz.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hsf.2],by linarith [hsf.1]⟩
  have hiD : i≠3 := by rcases hi with rfl|rfl <;> decide
  by_cases hsz : s≤z
  · have ht := transport_trig hN
    have hp := mul_le_mul hr ht.2.2.2.1.le ht.2.2.1
      (show 0≤(3/2)*Explicit.p .low atG z s i by positivity)
    have hpay : Explicit.q .low atG z s i*Real.sin (frameCap-s)≤Explicit.p .low atG z s i := by
      nlinarith only [hp,hc.1]
    have hh := NegativeAPositiveTD.SameBlock.negative_surplus hc.1.le
      (show frameCap-z∈Icc 0 (frameCap-s) from ⟨hP.1,by linarith⟩) hN hpay
    simpa only [Concentration.pure,if_pos hsz,show frameCap-s-(frameCap-z)=z-s by ring] using hh
  · have hh := NegativeAPositiveTD.SameBlock.positive_surplus hc.1.le
      (show Explicit.q .low atG z s i≤(17/10)*Explicit.p .low atG z s i by nlinarith only [hr,hc.1]) hP
      (show frameCap-s∈Icc 0 (frameCap-z) from ⟨hN.1,by linarith⟩)
    simpa only [Concentration.pure,if_neg hsz,Concentration.positive,PositiveTD.Hybrid.positive,
      ↓reduceIte,if_neg hiD,show frameCap-z-(frameCap-s)=s-z by ring] using hh

theorem saturated_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      Concentration.saturated .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z := by
  by_cases hij : i=j
  · subst j
    by_cases hiD : i=3
    · subst i
      simpa only [Concentration.saturated,Concentration.block,Concentration.positive,
        PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,↓reduceIte,add_assoc] using
        separated_positive atG hz hs 3 3
    by_cases hiG : i=1
    · subst i
      simpa [Concentration.saturated,Concentration.block,PositiveTD.Hybrid.block,
        Explicit.p,Explicit.q,pWeights,qWeights,LowSaturatedG.same] using LowSaturatedG.same_positive atG hz hs
    have hi : i=0∨i=2 := by fin_cases i <;> simp_all
    have hc := HB_pure_le_same atG hz hs i hi
    have hp := LowPure.original atG hz hs i i
    simp only [Concentration.saturated,Concentration.block,PositiveTD.Hybrid.block,↓reduceIte,if_neg hiD]
    linarith
  · simpa only [Concentration.saturated,if_neg hij,add_assoc] using separated_positive atG hz hs i j

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
      min (Concentration.pure .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z)
        (Concentration.saturated .low (Explicit.p .low atG z s) (Explicit.q .low atG z s) i j s z) := by
  rw [add_min]
  exact lt_min (LowPure.original atG hz hs i j) (saturated_positive atG hz hs i j)

end Low

theorem reference_scalar_positive (f : Certificate.Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (P N : Fin 4→ℝ)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPbudget : (∑i,P i)≤frameCap-z) (hNbudget : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=z-s) :
    0<baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z+
      ∑i,Concentration.block f (Explicit.p f atG z s) (Explicit.q f atG z s) i (P i) (N i) := by
  have hp := Explicit.ordered_pair_domain f atG hz hs
  obtain ⟨i,j,hh⟩ := Concentration.concentrate f (Explicit.p f atG z s) (Explicit.q f atG z s) P N
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2) hP hN
    (Explicit.angle_domain atG hs).2 (Explicit.frame_domain f hz) hPbudget hNbudget hbalance
  have hpos : 0<baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z+
      min (Concentration.pure f (Explicit.p f atG z s) (Explicit.q f atG z s) i j s z)
        (Concentration.saturated f (Explicit.p f atG z s) (Explicit.q f atG z s) i j s z) := by
    cases f
    · exact Low.intrinsic_positive atG hz hs i j
    · exact High.intrinsic_positive atG hz hs i j
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
