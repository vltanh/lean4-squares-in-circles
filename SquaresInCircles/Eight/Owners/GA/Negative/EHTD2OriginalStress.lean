module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Blocks
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceHSupport

/-!
# Eight squares: the negative-EH scalar inequality forced by the cycle

The H coefficient, the selected A gains, the T support and the DE2 singleton of the cycle are all
kept. The far EH charge is taken once from each positive block mass. The full-circle D baseline is
used only as a lower bound of the sorted support (`baseline_lower`). No scalar positivity is
assumed (`scalar_nonpositive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks PairedE

lemma charge_nonnegative (r : Regime) : 0≤Explicit.errorCharge r := by
  cases r <;> norm_num [Explicit.errorCharge,NegativeEH.epsilon]

lemma clipped_le_full (c : ℝ) : clippedSupport 1 c≤fullSupport 1 c := by
  by_cases h : 1≤c
  · rw [clippedSupport,ite_eq_left h]
    have hh := raw_full_support (a:=GlobalGA.Secondary.diagonal) (b:=GlobalGA.Secondary.diagonal) (f:=1) (g:=c)
      (show (GlobalGA.Secondary.diagonal+1/2)^2+(GlobalGA.Secondary.diagonal+1/2)^2≤qCap by nlinarith [diagonal_circle])
    simpa [diagonalSupport,add_mul] using hh
  · simp [clippedSupport,h]

lemma baseline_lower (r : Regime) (f : Family) (a z : ℝ) :
    Explicit.baseline r f a z≤
      PositiveTD.baseline (Explicit.k r f (a+z)) (Explicit.l r f (a+z))
        (Explicit.c r f (a+z)) z+Explicit.l r f (a+z)*TwoPositive.ASupport.charge a := by
  have hc := clipped_le_full (Explicit.c r f (a+z))
  have hm : Explicit.m r f (a+z) z=PositiveTD.tilted (Explicit.c r f (a+z)) z := rfl
  simp only [Explicit.baseline,PositiveTD.baseline,hm]
  change _≤_
  dsimp only [Explicit.sigma,NegativeDEPositiveTD.Explicit.sigma,PositiveTD.sigma,
    NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta]
  split_ifs <;> linarith

lemma eh_gain_lower {C : SignedCycle} (r : Regime) (f : Family)
    (ga ab : Bool) (hflat : (C.point E).a=7/12)
    (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f))
    (hs : magnitude C∈Icc (Explicit.eLeft r) (Explicit.eRight r)) :
    Explicit.gain r (magnitude C)≤
      ehGain C (Explicit.k r f (total C ga ab)) (Explicit.ehWeight r) := by
  have hsf := Explicit.e_frame_domain r hs
  have he : delta C.theta E= -magnitude C := by simp [magnitude]
  cases r
  · have hh := NegativeEH.small_actual_gain hb hsf
    rw [edgeWidth_positive_formula hsf] at hh
    rw [ehGain,he,hflat,edgeWidth_negative_formula hsf]
    simp only [Real.sin_neg,Real.cos_neg,Explicit.ehWeight,Explicit.gain]
    linarith
  · have hh := NegativeEH.far_actual_gain hb (Explicit.far_k_domain f hθ) hs
    rw [edgeWidth_positive_formula hsf] at hh
    rw [ehGain,he,hflat,edgeWidth_negative_formula hsf]
    simp only [Real.sin_neg,Real.cos_neg,Explicit.ehWeight,Explicit.gain]
    linarith

lemma family_block_coefficients {C : SignedCycle} (hg ga ab : Bool)
    (r : Regime) (f : Family)
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f))
    (hz : delta C.theta T∈Icc 0 (total C ga ab)) (i : Fin 4) :
    (blocks C hg ga ab (Explicit.k r f (total C ga ab))
      (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).p=
        Blocks.p r f (total C ga ab) (delta C.theta T) i ∧
    (blocks C hg ga ab (Explicit.k r f (total C ga ab))
      (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).q=
        Blocks.q r f (total C ga ab) (delta C.theta T) i := by
  have hc := Explicit.source_coefficients r f hθ hz
  simpa only [Blocks.p,Blocks.q,Explicit.m,Explicit.eta,
    NegativeDEPositiveTD.Explicit.eta,PositiveTD.tilted,PositiveTD.eta]
    using block_coefficients (C:=C) hg ga ab (c:=Explicit.c r f (total C ga ab))
      (by linarith [hc.1.2]) hc.2.1 i

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle}
    (hg ga ab : Bool) (r : Regime) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0)
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f)) (i : Fin 4) :
    Blocks.block r f (total C ga ab) (delta C.theta T)
      (blocks C hg ga ab (Explicit.k r f (total C ga ab))
        (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).P
      (blocks C hg ga ab (Explicit.k r f (total C ga ab))
        (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).N i≤
    actualBlocks C hg ga ab (Explicit.k r f (total C ga ab))
      (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) (Explicit.ehWeight r) i := by
  let k := Explicit.k r f (total C ga ab)
  let l := Explicit.l r f (total C ga ab)
  let c := Explicit.c r f (total C ga ab)
  have hb := budgets hg ga ab k l c hvar ha hz hs
  have hc := Explicit.source_coefficients r f hθ hb.td_domain
  have hp := Blocks.original_pair r f hθ hb.td_domain
  have hcoef := family_block_coefficients hg ga ab r f hθ hb.td_domain
  have hbudget := block_budgets hg ga ab k l c hvar ha hz hs
  have hcharge (j : Fin 4) := mul_nonneg (charge_nonnegative r)
    (blocks C hg ga ab k l c j).P_nonneg
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      mixedBlock R (Blocks.p r f (total C ga ab) (delta C.theta T) j)
        (Blocks.q r f (total C ga ab) (delta C.theta T) j)
        (blocks C hg ga ab k l c j).P (blocks C hg ga ab k l c j).N-
          Explicit.errorCharge r*(blocks C hg ga ab k l c j).P≤
        PositiveTD.actualPairIncrement (blocks C hg ga ab k l c j) P := by
    have hpos : 0≤(blocks C hg ga ab k l c j).p := by
      rw [(hcoef j).1]
      exact (hp j).1.le
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpos
      (hbudget j).1 (hbudget j).2
    rw [(hcoef j).1,(hcoef j).2] at hh
    exact (sub_le_self _ (hcharge j)).trans hh
  fin_cases i
  · have hfar : r=.far→k∈Icc (3/5:ℝ) (4/5) := by
      intro he
      subst r
      exact Explicit.far_k_domain f hθ
    have hP : positivePart (NegativePrimary.erase (!hg) (delta C.theta H))≤frameCap := by
      simpa [blocks,Block.P] using (hbudget 0).1
    have hN : negativePart (NegativePrimary.erase (!hg) (delta C.theta H))≤frameCap := by
      simpa [blocks,Block.N] using (hbudget 0).2
    have hh := actual_H_minorant r hHy (hcontained H) hQ hc.1 hfar hP hN
    simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      Blocks.p,Blocks.q,blocks,actualBlocks,hBlock,Block.P,Block.N,k,l,c] using hh
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,c] using hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,k,l,c] using hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hsorted D)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hcontained D) hQ hc.1 ⟨hc.2.2.1,hc.2.2.2⟩
      (original_error_bound hvar hn D)
    have he := (sub_le_self _ (hcharge 3)).trans hh
    simpa [Blocks.block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
      actualBlocks,blocks,Blocks.p,Blocks.q,Block.P,Block.N,Blocks.dCost,k,l,c] using he

theorem stress_nonpositive {C : SignedCycle} (hg ga ab : Bool) {k l c u : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hu : 0≤u)
    (hz : delta C.theta T∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l c u≤0 := by
  have hm := PositiveTD.tilted_pos hc hz
  have hw (i : Vertex) : 0≤weights C k l c u i := by
    fin_cases i
    · exact hk
    · exact hl
    · exact hl
    · exact hm.le
    · exact hc.le
    · show (0:ℝ)≤1
      norm_num
    · exact hu
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hfeasible i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

theorem scalar_nonpositive {Q : ℝ} {C : SignedCycle} (hg ga ab : Bool)
    (r : Regime) (f : Family)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta T) (hs : delta C.theta E≤0)
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hθ : total C ga ab∈Icc (Explicit.left r f) (Explicit.right r f))
    (he : magnitude C∈Icc (Explicit.eLeft r) (Explicit.eRight r))
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    Explicit.stressBase r f (aTotal C ga ab) (delta C.theta T) (magnitude C)+
      ∑i,Blocks.block r f (total C ga ab) (delta C.theta T)
        (blocks C hg ga ab (Explicit.k r f (total C ga ab))
          (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).P
        (blocks C hg ga ab (Explicit.k r f (total C ga ab))
          (Explicit.l r f (total C ga ab)) (Explicit.c r f (total C ga ab)) i).N i≤0 := by
  let k := Explicit.k r f (total C ga ab)
  let l := Explicit.l r f (total C ga ab)
  let c := Explicit.c r f (total C ga ab)
  have hbud := budgets hg ga ab k l c hvar ha hz hs
  have hp := Explicit.family_positive r f hθ hbud.td_domain
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from
      ⟨ha,hbud.a_domain.2.trans hbud.total_domain.2⟩)
  change TwoPositive.ASupport.charge (aTotal C ga ab)≤
    primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hA
  have hAg := mul_le_mul_of_nonneg_left hA hp.2.1.le
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,hbud.td_domain.2.trans hbud.total_domain.2⟩
  have hT := PositiveTD.tReserve_nonneg (hsorted T) (hcontained T) hQ hp.2.2.1.le hzframe
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower hg ga ab r f hsorted hcontained hQ hHy hGy hBy hDy
      hvar ha hz hs hθ i)
  have hE := eh_gain_lower r f ga ab hflat hb hθ he
  have hbase := baseline_lower r f (aTotal C ga ab) (delta C.theta T)
  have hidentity := decomposition C hg ga ab k l c (Explicit.ehWeight r)
  have hu : 0≤Explicit.ehWeight r := by cases r <;> norm_num [Explicit.ehWeight,NegativeEH.p]
  have hupper := stress_nonpositive hg ga ab hp.1.le hp.2.1.le hp.2.2.1 hu hzframe hfeasible
  have htot : aTotal C ga ab+delta C.theta T=total C ga ab := rfl
  rw [htot] at hbase
  simp only [k,l,c] at hidentity
  dsimp only [Explicit.stressBase]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Source
