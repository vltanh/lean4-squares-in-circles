module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SmallLowPure

/-!
# Complete small-EH low-total scalar exclusion

Uncompiled completion of Section 3 of the small-EH companion. The
actual DE2 singleton is included as the fourth block. Its same-block
term is already separated, and its negative term is exactly the H
minorant. Every pure and saturated alternative is strictly positive.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem separated_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i j : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.positive .small .low (a+z) z (frameCap-(a+z)) i+
        Blocks.negative .small .low (a+z) z (frameCap-s) j := by
  have hH := separated_monotone true hθ (by norm_num) hs hs.1
  have hG := separated_monotone false hθ (by norm_num) hs hs.1
  have h0H := zero_separated_positive hθ ha hz i true
  have h0G := zero_separated_positive hθ ha hz i false
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hg0 : NegativeEH.g 0=0 := by simp [NegativeEH.g]
  simp only [hg0,sub_zero,zero_add,NegativeDEPositiveTD.LowSeparated.larger,Bool.false_eq_true,
    reduceIte] at hH hG h0H h0G
  fin_cases j
  · change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      V R (Explicit.k .small .low (a+z)) 1 (frameCap-s)
    linarith
  · change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      V R (Explicit.k .small .low (a+z)) (NegativeDEPositiveTD.Explicit.l .low (a+z)) (frameCap-s)
    linarith
  · have hB : V R (Explicit.k .small .low (a+z)) 1 (frameCap-s)≤
        NegativeDEPositiveTD.Explicit.V .low (a+z) z 2 (frameCap-s) :=
      NegativeDEPositiveTD.LowNegative.B_dominates_H hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hsf.2],by linarith [hsf.1]⟩)
    change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      NegativeDEPositiveTD.Explicit.V .low (a+z) z 2 (frameCap-s)
    linarith
  · change 0<Explicit.baseline .small .low a z+NegativeEH.g s+_+
      V R (Explicit.k .small .low (a+z)) 1 (frameCap-s)
    linarith

theorem same_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.block .small .low (a+z) z (frameCap-(a+z)) (frameCap-s) i := by
  by_cases hiD : i=3
  · subst i
    rw [Blocks.block_D]
    simpa only [add_assoc] using separated_positive hθ ha hz hs 3 3
  by_cases hiG : i=1
  · subst i
    have hm := G_same_monotone hθ (by norm_num) hs hs.1
    have h0 : 0<Explicit.baseline .small .low a z+mixedBlock R
        (NegativeDEPositiveTD.Explicit.k .low (a+z)) (NegativeDEPositiveTD.Explicit.l .low (a+z))
        (frameCap-(a+z)) frameCap := zero_G_same_positive hθ ha hz
    have hg0 : NegativeEH.g 0=0 := by simp [NegativeEH.g]
    simp only [hg0,sub_zero,zero_add,NegativeDEPositiveTD.LowSame.ordinary] at hm
    have hb : Blocks.block .small .low (a+z) z (frameCap-(a+z)) (frameCap-s) 1=
        mixedBlock R (NegativeDEPositiveTD.Explicit.k .low (a+z))
          (NegativeDEPositiveTD.Explicit.l .low (a+z)) (frameCap-(a+z)) (frameCap-s)-
          0*(frameCap-(a+z)) :=
      Blocks.block_ordinary .small .low (a+z) z (frameCap-(a+z)) (frameCap-s) 1
    rw [hb]
    linarith
  obtain ⟨j,hj,hcase⟩ : ∃j : Fin 3,j.castSucc=i ∧ (j=0∨j=2) := by
    fin_cases i
    · exact ⟨0,rfl,Or.inl rfl⟩
    · exact absurd rfl hiG
    · exact ⟨2,rfl,Or.inr rfl⟩
    · exact absurd rfl hiD
  subst i
  rw [Blocks.block_ordinary]
  simp only [Explicit.errorCharge,zero_mul,sub_zero]
  by_cases horder : s≤a+z
  · have hp := pure_negative_positive hθ ha hz hs horder j.castSucc
    have hh : Explicit.V .small .low (a+z) z j (a+z-s)≤ mixedBlock R
        (Explicit.p .small .low (a+z) z j) (Explicit.q .small .low (a+z) z j)
        (frameCap-(a+z)) (frameCap-s) := NegativeDEPositiveTD.LowSame.HB_negative hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) ⟨hs.1,horder⟩ j hcase
    rw [Blocks.negative_ordinary] at hp
    linarith
  · have horder' : a+z ≤ s := (lt_of_not_ge horder).le
    have hp := pure_positive_positive hθ ha hz ⟨horder',hs.2⟩ j.castSucc
    have hh : Explicit.U .small .low (a+z) z j (s-(a+z))≤ mixedBlock R
        (Explicit.p .small .low (a+z) z j) (Explicit.q .small .low (a+z) z j)
        (frameCap-(a+z)) (frameCap-s) := NegativeDEPositiveTD.LowSame.HB_positive hθ
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
      (show s∈Icc (a+z) frameCap from ⟨horder',by norm_num [frameCap]; linarith [hs.2]⟩) j hcase
    rw [Blocks.positive_ordinary] at hp
    simp only [Explicit.errorCharge,zero_mul,sub_zero] at hp
    linarith

theorem intrinsic_positive {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i j : Fin 4) :
    0<Explicit.baseline .small .low a z+NegativeEH.g s+
      min (Blocks.pure .small .low (a+z) z s i j)
        (Blocks.saturated .small .low (a+z) z s i j) := by
  have hp : 0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.pure .small .low (a+z) z s i j := by
    by_cases horder : s≤a+z
    · simpa only [Blocks.pure,ChargedHybridConcentration.pure,if_pos horder,Blocks.negative] using
        pure_negative_positive hθ ha hz hs horder j
    · simpa only [Blocks.pure,ChargedHybridConcentration.pure,if_neg horder,Blocks.positive] using
        pure_positive_positive hθ ha hz ⟨(lt_of_not_ge horder).le,hs.2⟩ i
  have ht : 0<Explicit.baseline .small .low a z+NegativeEH.g s+
      Blocks.saturated .small .low (a+z) z s i j := by
    by_cases hij : i=j
    · subst j
      rw [Blocks.saturated,ChargedHybridConcentration.saturated,if_pos rfl]
      exact same_positive hθ ha hz hs i
    · simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,if_neg hij,
        Blocks.positive,Blocks.negative,add_assoc] using separated_positive hθ ha hz hs i j
  rw [add_min]
  exact lt_min hp ht

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .small .low a z s+
      ∑i,Blocks.block .small .low (a+z) z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .small .low P N hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs hP hN hPb hNb hbalance
  have hh := intrinsic_positive hθ ha hz hs i j
  dsimp [Explicit.stressBase,Explicit.gain]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.SmallLow
