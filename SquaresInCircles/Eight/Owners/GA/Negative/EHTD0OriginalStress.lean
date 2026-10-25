module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3Scalar
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD0SourceData

/-!
# Eight squares: high A and negative EH1 with BT2 and TD0 errors of either sign

The EH1 scalar is the four-block EH1/BT3 analytic theorem at zero T tilt; it does not claim that
BT3 is feasible. The BT2 and TD0 errors stay in the B and D circle blocks (`fullBlock`), and all
selected A primary errors keep their signs. The fourth D pair, the E force and both signed mass
budgets are unchanged (`full_scalar_nonpositive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

abbrev Regime := NegativeEHBT3.Source.Regime
abbrev ehWeight := NegativeEHBT3.Source.ehWeight
abbrev errorCharge := NegativeEHBT3.Source.errorCharge
abbrev ehLower := NegativeEHBT3.Source.ehLower

def fullBlock (r : Regime) (k l c : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  mixedBlock R (PositiveBT3.pWeights k l c c i)
    (PositiveBT3.qWeights k l c c i) P N-errorCharge r*P

theorem full_blocks_lower {Q : ℝ} {C : SignedCycle} (r : Regime)
    (hg : Fin 4) (ga ab : Bool) {k l c : ℝ}
    (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : k≤l) (hc : 0<c)
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5)) (i : Fin 4) :
    fullBlock r k l c i
      (blocks C hg ga ab k l c i).P (blocks C hg ga ab k l c i).N≤
        actualBlocks C hg ga ab k l c (ehWeight r) i := by
  have hb := budgets hg ga ab k l c hvar ha hs
  have hcoef := block_coefficients (C:=C) (hg:=hg) (c:=c) ga ab
    (show k≤1 by linarith [hk.2]) hl
  have hk0 : 0<k := by linarith [hk.1]
  have hp (j : Fin 4) : 0<PositiveBT3.pWeights k l c c j := by
    fin_cases j <;> simp [PositiveBT3.pWeights,lt_min_iff,hk0,hc] <;> linarith
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y)
      (hP : P.Contained Q) :
      fullBlock r k l c j
        (blocks C hg ga ab k l c j).P (blocks C hg ga ab k l c j).N≤
      PositiveTD.actualPairIncrement (blocks C hg ga ab k l c j) P := by
    have hpos : 0≤(blocks C hg ga ab k l c j).p := by
      rw [(hcoef j).1]
      exact (hp j).le
    have hmin := PositiveTD.actual_block_minorant hy hP hQ hpos
      (block_budgets hg ga ab k l c hvar ha hs j).1
      (block_budgets hg ga ab k l c hvar ha hs j).2
    rw [(hcoef j).1,(hcoef j).2] at hmin
    have hcost := mul_nonneg (NegativeEHBT3.Source.charge_nonnegative r)
      (blocks C hg ga ab k l c j).P_nonneg
    dsimp [fullBlock]
    linarith
  fin_cases i
  · have hP : positivePart (if hg=0 then 0 else delta C.theta H)≤frameCap := by
      simpa [blocks,NonnegativeTotals.TD0.blocks,Block.P] using
        (block_budgets hg ga ab k l c hvar ha hs 0).1
    have hN : negativePart (if hg=0 then 0 else delta C.theta H)≤frameCap := by
      simpa [blocks,NonnegativeTotals.TD0.blocks,Block.N] using
        (block_budgets hg ga ab k l c hvar ha hs 0).2
    have hh := NegativeEHPositiveTD.Source.actual_H_minorant r
      hHy (hcontained H) hQ hk hfar hP hN
    simpa [fullBlock,PositiveBT3.pWeights,PositiveBT3.qWeights,
      blocks,NonnegativeTotals.TD0.blocks,hBlock,actualBlocks,
      ehWeight,errorCharge,NegativeEHBT3.Source.ehWeight,NegativeEHBT3.Source.errorCharge,
      NegativeEHPositiveTD.Explicit.ehWeight,
      NegativeEHPositiveTD.Explicit.errorCharge,Block.P,Block.N] using hh
  · simpa [actualBlocks] using hordinary 1
      (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hcontained G)
  · simpa [actualBlocks] using hordinary 2
      (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hcontained B)
  · simpa [actualBlocks] using hordinary 3
      (P:=(C.point D).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hcontained D)

theorem stress_nonpositive {C : SignedCycle} (hg : Fin 4)
    (ga ab : Bool) {k l c w : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c) (hw : 0≤w)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    stress C hg ga ab k l c w≤0 := by
  have hweights (i : Vertex) : 0≤weights k l c w i := by
    fin_cases i <;> simp [weights] <;> positivity
  apply Finset.sum_nonpos
  intro i _
  have hi : edgeWidth (delta C.theta i)≤C.edge i (owners hg ga ab i) := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,sub_nonneg] using hf i
  exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (sub_nonpos.mpr hi)

/-- The stress of the cycle is nonpositive, with all its angles in four blocks. Every witness is
that of the cycle; none is inferred from another owner. -/
theorem full_scalar_nonpositive {Q : ℝ} {C : SignedCycle}
    (r : Regime) {hg : Fin 4} (ga ab : Bool) {k l c : ℝ}
    (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : k≤l) (hc : 0<c)
    (hfar : r=.far→k∈Icc (3/5:ℝ) (4/5))
    (hflat : (C.point E).a=7/12)
    (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (he : magnitude C∈Icc (NegativeEHPositiveTD.Explicit.eLeft r)
      (NegativeEHPositiveTD.Explicit.eRight r))
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) :
    PositiveATD0.fullBaseline k l c+
      l*TwoPositive.ASupport.charge (aTotal C ga ab)+
      ehLower r (magnitude C)+
        (∑i,fullBlock r k l c i
          (blocks C hg ga ab k l c i).P
          (blocks C hg ga ab k l c i).N)≤0 := by
  have hbud := budgets hg ga ab k l c hvar ha hs
  have hn : negativeVariation C.theta≤frameCap := by
    rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    hbud.a_domain
  have hAg := mul_le_mul_of_nonneg_left hA (show 0≤l by linarith [hk.1,hl])
  have hE := NegativeEHBT3.Source.eh_gain_lower r
    (k:=k) hflat hb he hfar
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower r hg ga ab hcontained hQ hHy hGy hBy hDy
      hvar ha hs hk hl hc hfar i)
  have hid := decomposition C ga ab hhg k l c (ehWeight r)
  have hupper := stress_nonpositive (k:=k) (l:=l) (c:=c) (w:=ehWeight r) hg ga ab
    (by linarith [hk.1])
    (by linarith [hk.1,hl]) hc.le
    (NegativeEHBT3.Source.weight_nonnegative r) hf
  change l*TwoPositive.ASupport.charge (aTotal C ga ab)≤
    l*PairedE.primaryGain (C.point A) ga ab
      (delta C.theta G) (delta C.theta A) at hAg
  linarith

theorem full_block_eq_scalar (f : NegativeEHBT3.Family)
    (hf : f≠.smallLow) (a : ℝ) (i : Fin 4) (P N : ℝ) :
    fullBlock (if NegativeEHBT3.far f then .far else .small)
      (NegativeEHBT3.Explicit.k f a) (NegativeEHBT3.Explicit.l f a)
      (NegativeEHBT3.Explicit.m f a) i P N =
      NegativeEHBT3.Scalar.block f a 0 P N i := by
  cases f with
  | smallLow => exact (hf rfl).elim
  | smallHigh => simp [fullBlock,NegativeEHBT3.Scalar.block,
      NegativeEHBT3.Blocks.block,ChargedOrdinaryConcentration.block,
      NegativeEHBT3.Blocks.p,NegativeEHBT3.Blocks.q,
      errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,
      NegativeEHBT3.epsilon,NegativeEHBT3.far,
      NegativeEHBT3.Explicit.c,PositiveBT3.tilted]
  | farLow => simp [fullBlock,NegativeEHBT3.Scalar.block,
      NegativeEHBT3.Blocks.block,ChargedOrdinaryConcentration.block,
      NegativeEHBT3.Blocks.p,NegativeEHBT3.Blocks.q,
      errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,
      NegativeEHBT3.epsilon,NegativeEHBT3.far,
      NegativeEHBT3.Explicit.c,PositiveBT3.tilted]
  | farHigh => simp [fullBlock,NegativeEHBT3.Scalar.block,
      NegativeEHBT3.Blocks.block,ChargedOrdinaryConcentration.block,
      NegativeEHBT3.Blocks.p,NegativeEHBT3.Blocks.q,
      errorCharge,NegativeEHPositiveTD.Explicit.errorCharge,
      NegativeEHBT3.epsilon,NegativeEHBT3.far,
      NegativeEHBT3.Explicit.c,PositiveBT3.tilted]

end SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
