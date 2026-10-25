module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2SourceData

/-!
# The actual H square under the genuine EH multiplier

Uncompiled original-point comparison. There is one original HG argument
at H, not an independently chosen positive and negative pair. Its two
closed signs are handled before using the nominal mixed-block bound.
The negative cosine coefficient is the actual k, not the larger EH
multiplier. This is the reason the full H norm increment is retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

lemma singleton_P (k u t : ℝ) : (⟨k,u,t,0⟩:Block).P=positivePart t := by
  simp [Block.P]
lemma singleton_N (k u t : ℝ) : (⟨k,u,t,0⟩:Block).N=negativePart t := by
  simp [Block.N]

lemma singleton_increment_positive {k u t : ℝ} (ht : t∈Icc 0 frameCap) :
    (⟨k,u,t,0⟩:Block).increment R=U R k u t := by
  simp [Block.increment,psi_positive ht,U]

lemma singleton_increment_negative {k u t : ℝ} (ht : -t∈Icc 0 frameCap) :
    (⟨k,u,t,0⟩:Block).increment R=
      k*(Real.cos (-t)-1)-R*(pairNorm k u t-pairNorm k u 0) := by
  have hp := psi_negative ht
  simp only [neg_neg] at hp
  simp [Block.increment,hp]

lemma singleton_minorant (r : Regime) {k t : ℝ}
    (hk : k∈Icc (1/2:ℝ) (17/20))
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5))
    (hP : positivePart t≤frameCap) (hN : negativePart t≤frameCap) :
    mixedBlock R k 1 (positivePart t) (negativePart t)-Explicit.errorCharge r*positivePart t≤
      (⟨k,Explicit.ehWeight r,t,0⟩:Block).increment R := by
  cases r
  · have hp : 0≤(⟨k,(1:ℝ),t,0⟩:Block).p := by
      dsimp [Block.p]
      exact le_min (by linarith [hk.1]) (by norm_num)
    have hh := (⟨k,(1:ℝ),t,0⟩:Block).minorant R hp
      (by rw [singleton_P]; exact hP) (by rw [singleton_N]; exact hN)
    simpa [Block.p,Block.q,min_eq_left (by linarith [hk.2] : k≤1),
      max_eq_right (by linarith [hk.2] : k≤1),singleton_P,singleton_N,
      Explicit.errorCharge,Explicit.ehWeight] using hh
  · have hkf := hfar rfl
    by_cases ht : 0≤t
    · have hPt : positivePart t=t := max_eq_left ht
      have hNt : negativePart t=0 := max_eq_right (by linarith)
      have htf : t∈Icc 0 frameCap := ⟨ht,by simpa only [hPt] using hP⟩
      rw [hPt,hNt,mixedBlock_zero_right,singleton_increment_positive htf]
      exact NegativeEH.HComparison.positive hkf htf
    · have hPt : positivePart t=0 := max_eq_right (le_of_not_ge ht)
      have hNt : negativePart t= -t := max_eq_left (by linarith)
      have htf : -t∈Icc 0 frameCap := ⟨by linarith,by simpa only [hNt] using hN⟩
      rw [hPt,hNt,mixedBlock_zero_left,mul_zero,sub_zero,singleton_increment_negative htf]
      simpa only [neg_neg,Explicit.ehWeight] using NegativeEH.HComparison.negative hkf htf

/-- No support-maximizing square is substituted for the original H point. -/
theorem actual_H_minorant (r : Regime) {Q k t : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained Q) (hQ : Q≤qCap)
    (hk : k∈Icc (1/2:ℝ) (17/20))
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5))
    (hP : positivePart t≤frameCap) (hN : negativePart t≤frameCap) :
    mixedBlock R k 1 (positivePart t) (negativePart t)-Explicit.errorCharge r*positivePart t≤
      PositiveTD.actualPairIncrement (⟨k,Explicit.ehWeight r,t,0⟩:Block) P := by
  have ha := PositiveTD.actual_block_increment_lower
    (B:=(⟨k,Explicit.ehWeight r,t,0⟩:Block)) hy hc hQ
    (by simpa only [singleton_P] using hP) (by simpa only [singleton_N] using hN)
  exact (singleton_minorant r hk hfar hP hN).trans ha

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Source
