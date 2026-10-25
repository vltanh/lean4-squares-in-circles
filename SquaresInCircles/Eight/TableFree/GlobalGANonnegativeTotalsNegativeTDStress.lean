module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSourceData

/-!
# The original negative-TD2 force inequality pays every scalar term

Uncompiled transcription of Section 7. The four original anchor
points pay the four analytic blocks, the unchanged T/D pair pays the
sharp secant gain, and the unchanged A/E points pay their selected
signed totals. No transported marker or artificial boundary state
is used in this force comparison.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NonnegativeTotals.Source (aTotal eTotal)

theorem block_lower {Q ε s : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hε : ε∈Icc 0 frameCap)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta T=-s) (i : Fin 4) :
    Concentration.block ε i (blocks C hg ga ab de eh ε i).P (blocks C hg ga ab de eh ε i).N≤
      actualBlocks C hg ga ab de eh ε i := by
  have hr := ranges hε
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (p ε j) (q ε j)
        (blocks C hg ga ab de eh ε j).P (blocks C hg ga ab de eh ε j).N≤
          PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε j) P := by
    have hco := block_coefficients (C:=C) (hg:=hg) ga ab de eh hε j
    have hpn : 0≤(blocks C hg ga ab de eh ε j).p := by
      rw [hco.1]
      exact (coefficients hε j).1.le
    have hb := block_budgets hg ga ab de eh ε hvar ha he hs hd j
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpn hb.1 hb.2
    rwa [hco.1,hco.2] at hh
  fin_cases i
  · simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hsmall := NegativePrimary.erase_abs_bound de (original_error_bound hvar hn D)
    have hk : k ε∈Icc (1/2:ℝ) (17/20:ℝ) := ⟨by linarith [hr.1],by linarith [hr.2.1]⟩
    have hcoef : c∈Icc (k ε) 2 := ⟨by dsimp [c]; linarith [hr.2.1],by norm_num [c]⟩
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hsort D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hQ hk hcoef hsmall
    simpa [Concentration.block,PositiveTD.Hybrid.block,actualBlocks,blocks,Block.P,Block.N,p,q,aD] using hh

theorem stress_lower {Q ε s : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hε : ε∈Icc 0 frameCap)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta T=-s) (hhg : hg=0∨hg=2) :
    base ε+l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+
      TwoPositive.ASupport.charge (eTotal C de eh)+speed*s+
      (∑i,Concentration.block ε i (blocks C hg ga ab de eh ε i).P (blocks C hg ga ab de eh ε i).N)≤
        actualStress C hg ga ab de eh ε := by
  have hb := budgets hg ga ab de eh ε hvar ha he hs hd
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall := original_error_bound hvar hn
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => block_lower ga ab de eh hε
    hsort hc hQ hHy hGy hBy hDy hvar ha he hs hd i (hg:=hg))
  have hres := NonnegativeTotals.Source.primary_reserves ga ab de eh hsort hc hQ hsmall
    (show 0≤l ε by linarith [(ranges hε).2.2.1]) hb.2.1 hb.2.2.1
  have hgain := actual_sharp_gain (hsort T) hcoreT (hc T) (hsort D) hDy (hc D)
    hQ hs (by norm_num [c] : 0≤c)
  rw [decomposition C ga ab de eh hhg hd hs]
  dsimp [speed]
  linarith

theorem weights_nonnegative {ε : ℝ} {C : SignedCycle} (hε : ε∈Icc 0 frameCap)
    (hsmall : |delta C.theta T|≤frameCap) (i : Vertex) : 0≤weights C ε i := by
  have hr := ranges hε
  have hcos := NegativePrimary.cos_pos hsmall
  have hk : 0≤k ε := by linarith [hr.1]
  have hl : 0≤l ε := by linarith [hr.2.2.1]
  fin_cases i <;> simp [weights,c] <;> positivity

theorem stress_nonpositive {ε : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool)
    (hε : ε∈Icc 0 frameCap) (hsmall : |delta C.theta T|≤frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : actualStress C hg ga ab de eh ε≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,NonnegativeTotals.Source.owners,H] using hHG
    · simpa [owners,NonnegativeTotals.Source.owners,G] using hGA
    · simpa [owners,NonnegativeTotals.Source.owners,A] using hAB
    · simpa [owners,NonnegativeTotals.Source.owners,B] using hBT
    · simpa [owners,NonnegativeTotals.Source.owners,T] using hTD
    · simpa [owners,NonnegativeTotals.Source.owners,D] using hDE
    · simpa [owners,NonnegativeTotals.Source.owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonnegative hε hsmall) hf)

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Source
