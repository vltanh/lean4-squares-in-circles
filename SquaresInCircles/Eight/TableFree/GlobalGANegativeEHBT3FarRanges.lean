module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Ranges

/-!
# All four far-EH / BT3 pairs

Uncompiled Sections 6--7. B uses the unrotated m; the independently
varying D pair uses c=m(cos z+eta sin z). Both orders of the D pair
are retained. Its negative alternative is compared to H without
requiring the stronger small-high lower bound k >= 2/3.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Explicit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem farLow_pairs {t z : ℝ} (ht : t∈Icc 0 u) (hz : z∈Icc 0 t) (i : Fin 4) :
    (3/5:ℝ)≤p .farLow t z i ∧ p .farLow t z i≤q .farLow t z i ∧
      q .farLow t z i≤(5/3)*p .farLow t z i := by
  have hr := NegativeEHPositiveTD.Explicit.far_low_ranges ht
  have hc := NegativeEHPositiveTD.Explicit.far_low_tilted ht hz
  have hz0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,ht.1⟩
  have hp := NegativeEHPositiveTD.Explicit.far_pairs .low ht hz0
  fin_cases i
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,farLow_k] using hp 0
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,farLow_k,farLow_l] using hp 1
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,farLow_l,farLow_m,
      NegativeEHPositiveTD.Explicit.p,NegativeEHPositiveTD.Explicit.q,NegativeEHPositiveTD.Explicit.m]
      using hp 2
  · have hc0 : (367/400:ℝ)≤c .farLow t z := hr.2.2.1.1.trans hc.1
    have hc1 : c .farLow t z≤111/100 := hc.2.1
    change (3/5:ℝ)≤min 1 (c .farLow t z) ∧ min 1 (c .farLow t z)≤max 1 (c .farLow t z) ∧
      max 1 (c .farLow t z)≤(5/3)*min 1 (c .farLow t z)
    rcases le_total 1 (c .farLow t z) with he|he
    · rw [min_eq_left he,max_eq_right he]
      exact ⟨by norm_num,he,by linarith⟩
    · rw [min_eq_right he,max_eq_left he]
      exact ⟨by linarith,he,by linarith⟩

theorem farLow_q_upper {t z : ℝ} (ht : t∈Icc 0 u) (hz : z∈Icc 0 t) (i : Fin 4) :
    q .farLow t z i≤111/100 := by
  have hr := NegativeEHPositiveTD.Explicit.far_low_ranges ht
  have hc := NegativeEHPositiveTD.Explicit.far_low_tilted ht hz
  fin_cases i <;> simp only [q,PositiveBT3.qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero]
  · norm_num
  · exact hr.2.1.2.trans (by norm_num)
  · exact max_le (hr.2.1.2.trans (by norm_num)) hr.2.2.1.2
  · exact max_le (by norm_num) hc.2.1

theorem farHigh_pairs {t z : ℝ} (ht : t∈Icc u frameCap) (hz : z∈Icc 0 t) (i : Fin 4) :
    (3/5:ℝ)≤p .farHigh t z i ∧ p .farHigh t z i≤q .farHigh t z i ∧
      q .farHigh t z i≤(5/3)*p .farHigh t z i := by
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges ht
  have hc := NegativeEHPositiveTD.Explicit.far_high_tilted ht hz
  have hz0 : (0:ℝ)∈Icc 0 t := ⟨le_rfl,by linarith [ht.1]⟩
  have hp := NegativeEHPositiveTD.Explicit.far_pairs .high ht hz0
  fin_cases i
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,farHigh_k] using hp 0
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,farHigh_k,farHigh_l] using hp 1
  · simpa [p,q,PositiveBT3.pWeights,PositiveBT3.qWeights,farHigh_l,farHigh_m,
      NegativeEHPositiveTD.Explicit.p,NegativeEHPositiveTD.Explicit.q,NegativeEHPositiveTD.Explicit.m]
      using hp 2
  · have hc0 : k .farHigh t<c .farHigh t z := hc.2.2.1.trans_le (min_le_right _ _)
    have hc1 : c .farHigh t z<1 := (le_max_right _ _).trans_lt hc.2.2.2.1
    change (3/5:ℝ)≤min 1 (c .farHigh t z) ∧ min 1 (c .farHigh t z)≤max 1 (c .farHigh t z) ∧
      max 1 (c .farHigh t z)≤(5/3)*min 1 (c .farHigh t z)
    rw [min_eq_right hc1.le,max_eq_left hc1.le]
    exact ⟨by linarith [hr.1.1],hc1.le,by linarith [hr.1.1]⟩

theorem farHigh_q_upper {t z : ℝ} (ht : t∈Icc u frameCap) (hz : z∈Icc 0 t) (i : Fin 4) :
    q .farHigh t z i≤1 := by
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges ht
  have hc := NegativeEHPositiveTD.Explicit.far_high_tilted ht hz
  fin_cases i <;> simp only [q,PositiveBT3.qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero]
  · exact le_rfl
  · exact hr.2.1.2.trans (by norm_num)
  · exact max_le (hr.2.1.2.trans (by norm_num)) (hr.2.2.1.2.trans (by norm_num))
  · exact max_le le_rfl ((le_max_right _ _).trans hc.2.2.2.1.le)

/-- Whole-interval D comparison, including either order of (1,c). -/
theorem D_redundant {k c d : ℝ} (hk : k∈Icc (1/2:ℝ) 1)
    (hkc : k≤c) (hc : c≤6/5) (hd : d∈Icc 0 frameCap) :
    V R k 1 d≤V R (min 1 c) (max 1 c) d := by
  by_cases hc1 : c≤1
  · rw [min_eq_right hc1,max_eq_left hc1]
    exact OrdinaryNegativeEnvelope.V_monotone_smaller (Real.sqrt_nonneg qCap)
      (by norm_num : (0:ℝ)<1) hd hk ⟨hk.1.trans hkc,hc1⟩ hkc
  · have hc1' : 1≤c := (lt_of_not_ge hc1).le
    rw [min_eq_left hc1',max_eq_right hc1']
    have hfirst : V R k 1 d≤V R 1 1 d :=
      OrdinaryNegativeEnvelope.V_monotone_smaller (Real.sqrt_nonneg qCap)
        (by norm_num : (0:ℝ)<1) hd hk (by norm_num) hk.2
    exact hfirst.trans (PositiveATD0.balanced_second_coefficient
      (by norm_num) le_rfl hc1' (by linarith) hd)

theorem actual_D_redundant (f : Family) {t z d : ℝ}
    (ht : t∈Icc (left f) (right f)) (hz : z∈Icc 0 t) (hd : d∈Icc 0 frameCap) :
    V R (k f t) 1 d≤V R (p f t z 3) (q f t z 3) d := by
  have hc := source_coefficients f ht hz
  exact D_redundant ⟨hc.1.1,by linarith [hc.1.2]⟩ hc.2.2.2.1 hc.2.2.2.2.le hd

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Explicit
