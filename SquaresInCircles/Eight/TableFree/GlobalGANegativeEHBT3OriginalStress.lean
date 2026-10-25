module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3SourceData

/-!
# Original EH1 / BT3 full-circle necessary inequality

Uncompiled support step. The actual H support is compared with its
nominal pair only after retaining the EH multiplier and its zero-angle
support loss. The positive-mass charge is subtracted once per block.
D retains both original signed arguments, including arbitrary TD0.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev Regime := NegativeEHPositiveTD.Regime
abbrev ehWeight := NegativeEHPositiveTD.Explicit.ehWeight
abbrev errorCharge := NegativeEHPositiveTD.Explicit.errorCharge
abbrev ehLower := NegativeEHPositiveTD.Explicit.gain

def fullBlock (r : Regime) (k l m z : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m z) i)
    (PositiveBT3.qWeights k l m (PositiveBT3.tilted m z) i) P N-errorCharge r*P

lemma charge_nonnegative (r : Regime) : 0≤errorCharge r := by
  cases r <;> norm_num [errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,NegativeEH.epsilon]

lemma weight_nonnegative (r : Regime) : 0≤ehWeight r := by
  cases r <;> norm_num [ehWeight,NegativeEHPositiveTD.Explicit.ehWeight,NegativeEH.p]

lemma eh_gain_lower {C : SignedCycle} (r : Regime) {k : ℝ}
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (hs : magnitude C∈Icc (NegativeEHPositiveTD.Explicit.eLeft r)
      (NegativeEHPositiveTD.Explicit.eRight r))
    (hk : r=.far→k∈Icc (3/5:ℝ) (4/5)) :
    ehLower r (magnitude C)≤ehGain C k (ehWeight r) := by
  have hsf := NegativeEHPositiveTD.Explicit.e_frame_domain r hs
  have he : delta C.theta E= -magnitude C := by simp [magnitude]
  cases r
  · have hh := NegativeEH.small_actual_gain hb hsf
    rw [edgeWidth_positive_formula hsf] at hh
    rw [ehGain,NegativeEHPositiveTD.Source.ehGain,he,hflat,edgeWidth_negative_formula hsf]
    simp only [Real.sin_neg,Real.cos_neg,ehWeight,NegativeEHPositiveTD.Explicit.ehWeight,
      ehLower,NegativeEHPositiveTD.Explicit.gain]
    linarith
  · have hh := NegativeEH.far_actual_gain hb (hk rfl) hs
    rw [edgeWidth_positive_formula hsf] at hh
    rw [ehGain,NegativeEHPositiveTD.Source.ehGain,he,hflat,edgeWidth_negative_formula hsf]
    simp only [Real.sin_neg,Real.cos_neg,ehWeight,NegativeEHPositiveTD.Explicit.ehWeight,
      ehLower,NegativeEHPositiveTD.Explicit.gain]
    linarith

lemma pair_positive {k l m z : ℝ} (hk : 0<k) (hl : 0<l) (hm : 0< m)
    (hz : z∈Icc 0 frameCap) (i : Fin 4) :
    0<PositiveBT3.pWeights k l m (PositiveBT3.tilted m z) i := by
  have hc : 0<PositiveBT3.tilted m z := PositiveTD.tilted_pos hm hz
  fin_cases i <;> simp [PositiveBT3.pWeights,lt_min_iff,hk,hl,hm,hc]

theorem actual_blocks_lower {Q : ℝ} {C : SignedCycle} (r : Regime)
    (hg : Fin 4) (ga ab : Bool) {k l m : ℝ}
    (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : k≤l) (hm : 0< m)
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5)) (i : Fin 4) :
    fullBlock r k l m (delta C.theta B) i
      (blocks C hg ga ab k l m i).P (blocks C hg ga ab k l m i).N≤
        actualBlocks C hg ga ab k l m (ehWeight r) i := by
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  have hzframe : delta C.theta B∈Icc 0 frameCap :=
    ⟨hz,hbud.bt_domain.2.trans hbud.total_domain.2⟩
  have hp := pair_positive (show 0<k by linarith [hk.1])
    (show 0<l by linarith [hk.1]) hm hzframe
  have hk1 : k≤1 := by linarith [hk.2]
  have hcoef := block_coefficients (C:=C) (hg:=hg) (m:=m) ga ab hk1 hl
  have hbudget := block_budgets hg ga ab k l m hvar ha hz hs
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained Q) :
      fullBlock r k l m (delta C.theta B) j
        (blocks C hg ga ab k l m j).P (blocks C hg ga ab k l m j).N≤
          PositiveTD.actualPairIncrement (blocks C hg ga ab k l m j) P := by
    have hpos : 0≤(blocks C hg ga ab k l m j).p := by rw [(hcoef j).1]; exact (hp j).le
    have hh := PositiveTD.actual_block_minorant hy hP hQ hpos (hbudget j).1 (hbudget j).2
    rw [(hcoef j).1,(hcoef j).2] at hh
    have hcharge := mul_nonneg (charge_nonnegative r) (blocks C hg ga ab k l m j).P_nonneg
    dsimp [fullBlock]
    linarith
  fin_cases i
  · have hP : positivePart (if hg=0 then 0 else delta C.theta H)≤frameCap := by
      simpa [blocks,PositiveBT3.Source.blocks,NegativePrimary.erase,Block.P] using (hbudget 0).1
    have hN : negativePart (if hg=0 then 0 else delta C.theta H)≤frameCap := by
      simpa [blocks,PositiveBT3.Source.blocks,NegativePrimary.erase,Block.N] using (hbudget 0).2
    have hh := NegativeEHPositiveTD.Source.actual_H_minorant r hHy (hcontained H) hQ hk hfar hP hN
    simpa [fullBlock,PositiveBT3.pWeights,PositiveBT3.qWeights,blocks,PositiveBT3.Source.blocks,
      NegativePrimary.erase,Block.P,Block.N,actualBlocks,hBlock,ehWeight,errorCharge] using hh
  · simpa [actualBlocks] using hordinary 1 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hcontained G)
  · simpa [actualBlocks] using hordinary 2 (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hcontained B)
  · simpa [actualBlocks] using hordinary 3 (P:=(C.point Candidate.D).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hcontained Candidate.D)

theorem stress_nonpositive {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) {k l m u : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0< m) (hu : 0≤u)
    (hz : delta C.theta B∈Icc 0 frameCap)
    (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) : stress C hg ga ab k l m u≤0 := by
  have hc : 0<PositiveBT3.tilted m (delta C.theta B) := PositiveTD.tilted_pos hm hz
  have hw (i : Vertex) : 0≤weights C k l m u i := by
    fin_cases i <;> simp [weights,hk,hl,hm.le,hu,hc.le]
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hfeasible i
  exact mul_nonpos_of_nonneg_of_nonpos (hw i) (sub_nonpos.mpr hi)

/-- Full-circle scalar necessity is derived, rather than assumed. -/
theorem full_scalar_nonpositive {Q : ℝ} {C : SignedCycle} (r : Regime)
    {hg : Fin 4} (ga ab : Bool) {k l m : ℝ}
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : k≤l) (hm : 0< m)
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5))
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (he : magnitude C∈Icc (NegativeEHPositiveTD.Explicit.eLeft r)
      (NegativeEHPositiveTD.Explicit.eRight r))
    (hhg : hg=0∨hg=2) (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+
      l*TwoPositive.ASupport.charge (aTotal C ga ab)+ehLower r (magnitude C)+
      (∑i,fullBlock r k l m (delta C.theta B) i
        (blocks C hg ga ab k l m i).P (blocks C hg ga ab k l m i).N)≤0 := by
  have hbud := budgets hg ga ab k l m hvar ha hz hs
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from ⟨ha,hbud.a_domain.2.trans hbud.total_domain.2⟩)
  have hAg := mul_le_mul_of_nonneg_left hA (show 0≤l by linarith [hk.1])
  have hzframe : delta C.theta B∈Icc 0 frameCap :=
    ⟨hz,hbud.bt_domain.2.trans hbud.total_domain.2⟩
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hQ hm.le hzframe
  have hE := eh_gain_lower r hflat hb he hfar
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    actual_blocks_lower r hg ga ab hcontained hQ hHy hGy hBy hDy hvar ha hz hs hk hl hm hfar i)
  have hid := decomposition C ga ab hhg k l m (ehWeight r)
  have hupper := stress_nonpositive hg ga ab (show 0≤k by linarith [hk.1])
    (show 0≤l by linarith [hk.1]) hm (weight_nonnegative r) hzframe hfeasible
  change l*TwoPositive.ASupport.charge (aTotal C ga ab)≤
    l*PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hAg
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
