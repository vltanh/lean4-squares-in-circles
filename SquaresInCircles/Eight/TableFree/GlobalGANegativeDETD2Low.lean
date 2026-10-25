module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowSplit
public import SquaresInCircles.Eight.TableFree.OrdinarySignedBudgetConcentration

/-!
# Complete low-total negative-DE / positive-TD2 scalar exclusion

Uncompiled join of Sections 5--7 of the angle companion with the five
strict intrinsic endpoint inequalities. Pure positive, pure negative,
same-block saturation, and distinct-block saturation are all included.
The ordinary concentration uses both original signed budgets and never
changes the original A/TD split or the actual E magnitude.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Low
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinarySignedBudgetConcentration

theorem pure_negative_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 (a+z)) (i : Fin 3) :
    0<Explicit.baseline .low a z s+Explicit.V .low (a+z) z i (a+z-s) := by
  have he := LowSplit.original_endpoints hθ ha hz
  have hmin : 0< min
      (Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z))
      (Explicit.baseline .low a z (a+z)) := lt_min he.1 he.2.2.1
  have hh := hmin.trans_le (LowNegative.original_endpoint_lower hθ hs)
  have hc := LowNegative.pure_comparison hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
    (show a+z-s∈Icc 0 (a+z) from ⟨by linarith [hs.2],by linarith [hs.1]⟩) i
  linarith

theorem pure_positive_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    0<Explicit.baseline .low a z s+Explicit.U .low (a+z) z i (s-(a+z)) := by
  have he := (LowSplit.original_endpoints hθ ha hz).2.2.1
  exact he.trans_le (LowPositive.equal_le_positive_surplus hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs i)

theorem same_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    0<Explicit.baseline .low a z s+mixedBlock R
      (Explicit.p .low (a+z) z i) (Explicit.q .low (a+z) z i)
        (frameCap-(a+z)) (frameCap-s) := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  by_cases hi : i=1
  · subst i
    have he := (LowSplit.original_endpoints hθ ha hz).2.1
    have hl := LowSame.original_zero_lower hθ hzd hs
    have hh := he.trans_le hl
    simpa only [LowSame.ordinary,Explicit.p,Explicit.q,Matrix.cons_val] using hh
  · have hi' : i=0∨i=2 := by fin_cases i <;> simp_all
    by_cases horder : s≤a+z
    · have hp := pure_negative_positive hθ ha hz ⟨hs.1,horder⟩ i
      have hc := LowSame.HB_negative hθ hzd ⟨hs.1,horder⟩ i hi'
      linarith
    · have horder' : a+z ≤ s := (lt_of_not_ge horder).le
      have hp := pure_positive_positive hθ ha hz ⟨horder',hs.2⟩ i
      have hc := LowSame.HB_positive hθ hzd ⟨horder',hs.2⟩ i hi'
      linarith

theorem separated_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i j : Fin 3) :
    0<Explicit.baseline .low a z s+Explicit.U .low (a+z) z i (frameCap-(a+z))+
      Explicit.V .low (a+z) z j (frameCap-s) := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hH := LowSeparated.original_negative_zero_le true hθ hs
  have hG := LowSeparated.original_negative_zero_le false hθ hs
  have he := (LowSplit.original_endpoints hθ ha hz).2.2.2
  fin_cases j
  · have hp := he i true
    simp only [LowSeparated.larger,ite_true,Explicit.V,Explicit.p,Explicit.q,Fin.reduceFinMk,
      Matrix.cons_val] at hp hH ⊢
    generalize frameCap = F at hp hH ⊢
    linarith
  · have hp := he i false
    simp only [LowSeparated.larger,Bool.false_eq_true,ite_false,Explicit.V,Explicit.p,Explicit.q,
      Fin.reduceFinMk,Matrix.cons_val] at hp hG ⊢
    generalize frameCap = F at hp hG ⊢
    linarith
  · have hp := he i true
    have hB := LowNegative.B_dominates_H hθ hzd
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    simp only [LowSeparated.larger,ite_true] at hp hH
    simp only [Fin.reduceFinMk]
    generalize frameCap = F at hp hH hB ⊢
    linarith

theorem intrinsic_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (i j : Fin 3) :
    0<Explicit.baseline .low a z s+
      min (pure R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z))
        (saturated R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z)) := by
  have hp : 0<Explicit.baseline .low a z s+
      pure R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z) := by
    by_cases horder : s≤a+z
    · simpa only [OrdinarySignedBudgetConcentration.pure,horder,↓reduceIte,Explicit.V] using
        pure_negative_positive hθ ha hz ⟨hs.1,horder⟩ j
    · simpa only [OrdinarySignedBudgetConcentration.pure,horder,↓reduceIte,Explicit.U] using
        pure_positive_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ i
  have hsaturated : 0<Explicit.baseline .low a z s+
      saturated R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) i j s (a+z) := by
    by_cases hij : i=j
    · subst j
      simpa only [saturated,↓reduceIte] using same_positive hθ ha hz hs i
    · simpa only [saturated,hij,↓reduceIte,Explicit.U,Explicit.V,add_assoc] using
        separated_positive hθ ha hz hs i j
  rw [add_min]
  exact lt_min hp hsaturated

/-- Positivity for the actual original ordinary allocation, with its
unchanged signed balance and both actual total budgets. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 3→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline .low a z s+∑i,mixedBlock R
      (Explicit.p .low (a+z) z i) (Explicit.q .low (a+z) z i) (P i) (N i) := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hp := LowRanges.pairs hθ hzd
  have htf : a+z∈Icc 0 frameCap := ⟨hθ.1,by norm_num [frameCap]; linarith [hθ.2]⟩
  obtain ⟨i,j,hij⟩ := concentrate R (Explicit.p .low (a+z) z) (Explicit.q .low (a+z) z) P N
    (Real.sqrt_nonneg qCap) radius_sq.le (fun i => (hp i).1)
    (fun i => (hp i).2.1) (fun i => (hp i).2.2.1) hP hN hs htf hPb hNb hbalance
  have hh := intrinsic_positive hθ ha hz hs i j
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Low
