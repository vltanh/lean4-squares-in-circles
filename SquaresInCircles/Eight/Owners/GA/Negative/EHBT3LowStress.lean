module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SourceHSupport
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsTD0Data
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Stress

/-!
# Eight squares: original sorted-D necessity in the small-EH small-total sector

The distinguished D block is bounded on its
original two signed arguments. The fixed-K negative reserve from the
sorted-D theorem dominates the current k reserve by an explicit
coefficient comparison. No E nonnegative-total hypothesis is imported
from the positive-BT source theorem.
-/

section
/-!
## Original EH1 / BT3 / TD0 stress and signed budgets

The original TD0 and DE2 arguments both remain in D's block. Only
selected A primaries, BT3, and EH1 are removed from the mass ledger.
The EH multiplier changes H's actual support, not its nominal masses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev aTotal := PositiveBT3.Source.aTotal

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta B
def magnitude (C : SignedCycle) : ℝ := -delta C.theta E

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  PositiveBT3.Source.owners hg ga ab false true

def weights (C : SignedCycle) (k l m u : ℝ) : Vertex→ℝ :=
  ![k,l,l,m,PositiveBT3.tilted m (delta C.theta B),1,u]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m u : ℝ) : ℝ :=
  ∑i,weights C k l m u i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

abbrev blocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ) : Fin 4→Block :=
  PositiveBT3.Source.blocks C hg ga ab false true k l m

def hBlock (C : SignedCycle) (hg : Fin 4) (k u : ℝ) : Block :=
  ⟨k,u,if hg=0 then 0 else delta C.theta H,0⟩

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m u : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (hBlock C hg k u) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l m 3) (C.point Candidate.D).reflect]

abbrev ehGain := NegativeEHPositiveTD.Source.ehGain

def selectedA (C : SignedCycle) (ga ab : Bool) (f : ℝ→ℝ) : ℝ :=
  f (PairedE.selected ga (delta C.theta G))+f (PairedE.selected ab (delta C.theta A))

/-- Exact original-point identity, before any support estimate. -/
theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k l m u : ℝ) :
    stress C hg ga ab k l m u=
      PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+
        (∑i,actualBlocks C hg ga ab k l m u i)+
        l*PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        PositiveBT3.Source.tReserve C m+ehGain C k u := by
  cases ga <;> cases ab <;> rcases hhg with rfl|rfl <;>
    simp [stress,weights,owners,PositiveBT3.Source.owners,blocks,
      PositiveBT3.Source.blocks,hBlock,actualBlocks,ehGain,NegativeEHPositiveTD.Source.ehGain,
      PositiveBT3.Analytic.fullBaseline,PositiveBT3.Source.tReserve,PositiveBT3.tilted,
      PositiveTD.actualPairIncrement,pairF,pairG,PairedE.primaryGain,NegativePrimary.erase,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,Candidate.D,E,SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

theorem selectedA_nonnegative (C : SignedCycle) (ga ab : Bool)
    (f : ℝ→ℝ) (hf : ∀x,0≤f x) : 0≤ selectedA C ga ab f := by
  exact add_nonneg (hf _) (hf _)

theorem selectedA_signed (C : SignedCycle) (ga ab : Bool) :
    selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab := by
  have hG := positive_sub_negative (PairedE.selected ga (delta C.theta G))
  have hA := positive_sub_negative (PairedE.selected ab (delta C.theta A))
  dsimp [selectedA,aTotal,PositiveBT3.Source.aTotal,PairedE.total]
  linarith

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l m i).u+f (blocks C hg ga ab k l m i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta B)-f (delta C.theta E) := by
  have hh := PositiveBT3.Source.sum_parts C hg ga ab false true k l m f hf
  have e : PositiveBT3.Source.selectedSum C ga ab false true f=
      selectedA C ga ab f+f (delta C.theta E) := by
    simp only [PositiveBT3.Source.selectedSum,selectedA,PairedE.selected,Bool.false_eq_true,
      ↓reduceIte,hf,add_zero]
  rw [e] at hh
  calc _=_ := hh
    _=_ := by ring

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l m : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  bt_domain : delta C.theta B∈Icc 0 (total C ga ab)
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l m i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l m i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l m i).N)-(∑i,(blocks C hg ga ab k l m i).P)=
    total C ga ab-magnitude C

/-- Signed A constituents are not separately required to be nonnegative. -/
theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0) : Budgets C hg ga ab k l m := by
  have hp := sum_parts C hg ga ab k l m positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l m negativePart negativePart_zero
  have hA := selectedA_signed C ga ab
  have hAP := selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hzN : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta E)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta E)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l m i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta B := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l m i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l m i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ magnitude C := neg_nonneg.mpr hs
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l m : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0) (i : Fin 4) :
    (blocks C hg ga ab k l m i).P≤frameCap ∧ (blocks C hg ga ab k l m i).N≤frameCap := by
  have hb := budgets hg ga ab k l m hvar ha hz hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l m j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.total_domain.1],
    by linarith [hb.negative_bound,hb.eh_domain.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    {k l m : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l m i).p=
      PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i ∧
    (blocks C hg ga ab k l m i).q=
      PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i :=
  PositiveBT3.Source.block_coefficients ga ab false true hk hl i

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
end
end
end

section
/-!
## Original EH1 / BT3 full-circle necessary inequality

The actual H support is compared with its
nominal pair only after retaining the EH multiplier and its zero-angle
support loss. The positive-mass charge is subtracted once per block.
D retains both original signed arguments, including arbitrary TD0.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
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

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
end
end
end

section
/-!
## Negative EH1 and the four circles with BT2 and TD0

The two BT2 and TD0 angles stay: BT in the two-angle block of B and TD in the two-angle block of D
(`blocks`). Only the selected A primaries and the negative EH1 are deleted. The E multiplier enters
H and keeps the EH support correction. All statements concern one `SignedCycle` and one radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

abbrev aTotal := NegativeEHBT3.Source.aTotal
abbrev magnitude := NegativeEHBT3.Source.magnitude
abbrev selectedA := NegativeEHBT3.Source.selectedA

def owners (hg : Fin 4) (ga ab : Bool) : Vertex→Fin 4 :=
  NonnegativeTotals.TD0.owners hg ga ab false true

def weights (k l c w : ℝ) : Vertex→ℝ := ![k,l,l,c,c,1,w]

def stress (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c w : ℝ) : ℝ :=
  ∑i,weights k l c w i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

/-- The order H, G, B, D matches the four pairs of the scalar certificate. In particular D uses the
angles `(delta TD, delta DE)` of the cycle, not those of a TD2. -/
def blocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 1,
    NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 0,
    NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 2,
    NonnegativeTotals.TD0.blocks C hg ga ab false true k l c 3]

def hBlock (C : SignedCycle) (hg : Fin 4) (k w : ℝ) : Block :=
  ⟨k,w,if hg=0 then 0 else delta C.theta H,0⟩

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c w : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (hBlock C hg k w) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 3) (C.point D).reflect]

/-- The force sum. Both multipliers of T and B equal `c`, so the T support cancels and no
assumption on the tangent or the radial kind of T is used. -/
theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k l c w : ℝ) :
    stress C hg ga ab k l c w =
      PositiveATD0.fullBaseline k l c+
        (∑i,actualBlocks C hg ga ab k l c w i)+
        l*PairedE.primaryGain (C.point A) ga ab
          (delta C.theta G) (delta C.theta A)+
        NegativeEHPositiveTD.Source.ehGain C k w := by
  cases ga <;> cases ab <;> rcases hhg with rfl|rfl <;>
    simp [stress,weights,owners,NonnegativeTotals.TD0.owners,
      blocks,NonnegativeTotals.TD0.blocks,hBlock,actualBlocks,
      PositiveATD0.fullBaseline,PositiveTD.actualPairIncrement,
      NegativeEHPositiveTD.Source.ehGain,PairedE.primaryGain,
      pairF,pairG,erase,SignedCycle.edge,zeroProjection,quarterProjection,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

/-- Every unselected signed argument of the cycle appears exactly once. -/
theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l c i).u+
      f (blocks C hg ga ab k l c i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta E) := by
  have hh := NonnegativeTotals.TD0.sum_parts C hg ga ab false true k l c f hf
  have hperm : (∑i,(f (blocks C hg ga ab k l c i).u+f (blocks C hg ga ab k l c i).v))=
      ∑i,(f (NonnegativeTotals.TD0.blocks C hg ga ab false true k l c i).u+
        f (NonnegativeTotals.TD0.blocks C hg ga ab false true k l c i).v) := by
    simp only [blocks,Fin.sum_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.head_cons]
    ring
  rw [hperm,hh]
  simp only [NonnegativeTotals.Source.selectedSum,selectedA,NegativeEHBT3.Source.selectedA,
    PairedE.selected,Bool.false_eq_true,↓reduceIte,hf]
  ring

structure Budgets (C : SignedCycle) (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) : Prop where
  a_domain : aTotal C ga ab∈Icc 0 frameCap
  eh_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-aTotal C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-
    (∑i,(blocks C hg ga ab k l c i).P)=aTotal C ga ab-magnitude C

/-- The two sign budgets, opposite signs of GA and AB included. -/
theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0) :
    Budgets C hg ga ab k l c := by
  have hp := sum_parts C hg ga ab k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l c negativePart negativePart_zero
  have hA := NegativeEHBT3.Source.selectedA_signed C ga ab
  have hAP := NegativeEHBT3.Source.selectedA_nonnegative C ga ab
    positivePart positivePart_nonneg
  have hAN := NegativeEHBT3.Source.selectedA_nonnegative C ga ab
    negativePart negativePart_nonneg
  have hsP : positivePart (delta C.theta E)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta E)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l c i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart := by
    simpa only [Block.P,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l c i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hsN,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).N_nonneg)
  have heq := variations_equal C.theta
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact ⟨ha,by linarith⟩
  · exact ⟨neg_nonneg.mpr hs,by linarith⟩
  · linarith
  · linarith
  · linarith

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (k l c : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hs : delta C.theta E≤0)
    (i : Fin 4) :
    (blocks C hg ga ab k l c i).P≤frameCap ∧
    (blocks C hg ga ab k l c i).N≤frameCap := by
  have hb := budgets hg ga ab k l c hvar ha hs
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.a_domain.1],
    by linarith [hb.negative_bound,hb.eh_domain.1]⟩

/-- The B and D pairs keep their own signed errors. -/
theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    {k l c : ℝ} (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg ga ab k l c i).p=
      PositiveBT3.pWeights k l c c i ∧
    (blocks C hg ga ab k l c i).q=
      PositiveBT3.qWeights k l c c i := by
  fin_cases i <;>
    simp [blocks,NonnegativeTotals.TD0.blocks,Block.p,Block.q,
      PositiveBT3.pWeights,PositiveBT3.qWeights,
      min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl,
      min_comm,max_comm]

end SquaresInCircles.Eight.GlobalGA.NegativeEHTD0
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev lowP := PositiveBT3.LowEnvelope.p
abbrev lowQ := PositiveBT3.LowEnvelope.q

def lowBlock (t : ℝ) (i : Fin 4) (P N : ℝ) : ℝ :=
  PositiveTD.Hybrid.block R PositiveBT3.slope (lowP t) (lowQ t) 3 i P N

def sortedBlocks (C : SignedCycle) (hg : Fin 4) (ga ab : Bool) (k m : ℝ) : Fin 4→ℝ :=
  ![actualBlocks C hg ga ab k 1 m 1 0,actualBlocks C hg ga ab k 1 m 1 1,
    actualBlocks C hg ga ab k 1 m 1 2,PositiveBT3.Source.sortedD C false m]

theorem sorted_decomposition (C : SignedCycle) {hg : Fin 4} (ga ab : Bool)
    (hhg : hg=0∨hg=2) (k m : ℝ) :
    stress C hg ga ab k 1 m 1=
      PositiveBT3.Analytic.lowBaseline k m (delta C.theta B)+
        (∑i,sortedBlocks C hg ga ab k m i)+
        PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        PositiveBT3.Source.tReserve C m+ehGain C k 1 := by
  rw [decomposition C ga ab hhg]
  have hD := PositiveBT3.Source.sortedD_identity C hg ga ab false true k 1 m
  have hsame : PositiveBT3.Source.actualBlocks C hg ga ab false true k 1 m 3=
      actualBlocks C hg ga ab k 1 m 1 3 := rfl
  rw [hsame] at hD
  simp only [sortedBlocks,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero]
  rw [hD]
  have hk : fullSupport 1 k=fullSupport k 1 := by simp [fullSupport,add_comm]
  have hm : fullSupport m 1=fullSupport 1 m := by simp [fullSupport,add_comm]
  dsimp [PositiveBT3.Analytic.fullBaseline,PositiveBT3.Analytic.lowBaseline]
  rw [hk,hm]
  ring

theorem low_blocks_lower {Q : ℝ} {C : SignedCycle} (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (ht : total C ga ab∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    lowBlock (total C ga ab) i
      (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
        (PositiveBT3.lowM (total C ga ab)) i).P
      (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
        (PositiveBT3.lowM (total C ga ab)) i).N≤
      sortedBlocks C hg ga ab (PositiveBT3.lowK (total C ga ab))
        (PositiveBT3.lowM (total C ga ab)) i := by
  let t := total C ga ab
  let k := PositiveBT3.lowK t
  let m := PositiveBT3.lowM t
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hbud := budgets hg ga ab k 1 m hvar ha hz hs
  have hrot := PositiveBT3.Analytic.low_tilted_ranges ht hbud.bt_domain
  have hk : k∈Icc (1/2:ℝ) (17/20) := by
    dsimp [k,PositiveBT3.K] at *
    exact ⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩
  have hm : 0< m := by dsimp [m,t]; linarith [hr.2.1]
  have hm1 : 1≤ m := by dsimp [m,t]; linarith [hr.2.1]
  have hc1 : 1≤PositiveBT3.tilted m (delta C.theta B) := hm1.trans hrot.1
  have hfull (j : Fin 4) : fullBlock .small k 1 m (delta C.theta B) j
      (blocks C hg ga ab k 1 m j).P (blocks C hg ga ab k 1 m j).N≤
        actualBlocks C hg ga ab k 1 m 1 j :=
    actual_blocks_lower .small hg ga ab hcontained hQ
      hHy hGy hBy hDy hvar ha hz hs hk (by linarith [hk.2] : k≤1) hm (by simp) j
  have hzero : errorCharge .small=0 := rfl
  have h0 : lowBlock t 0 (blocks C hg ga ab k 1 m 0).P (blocks C hg ga ab k 1 m 0).N≤
      sortedBlocks C hg ga ab k m 0 := by
    have hh := hfull 0
    simp only [fullBlock,hzero,zero_mul,sub_zero] at hh
    simpa [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
      PositiveBT3.LowEnvelope.q,sortedBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,k] using hh
  have h1 : lowBlock t 1 (blocks C hg ga ab k 1 m 1).P (blocks C hg ga ab k 1 m 1).N≤
      sortedBlocks C hg ga ab k m 1 := by
    have hh := hfull 1
    simp only [fullBlock,hzero,zero_mul,sub_zero] at hh
    simpa [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
      PositiveBT3.LowEnvelope.q,sortedBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,k] using hh
  have h2 : lowBlock t 2 (blocks C hg ga ab k 1 m 2).P (blocks C hg ga ab k 1 m 2).N≤
      sortedBlocks C hg ga ab k m 2 := by
    have hh := hfull 2
    simp only [fullBlock,hzero,zero_mul,sub_zero] at hh
    simpa [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
      PositiveBT3.LowEnvelope.q,sortedBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,
      min_eq_left hm1,max_eq_right hm1,m] using hh
  have h3 : lowBlock t 3 (blocks C hg ga ab k 1 m 3).P (blocks C hg ga ab k 1 m 3).N≤
      sortedBlocks C hg ga ab k m 3 := by
    have hb3 : blocks C hg ga ab k 1 m 3=
        ⟨PositiveBT3.tilted m (delta C.theta B),1,delta C.theta T,delta C.theta Candidate.D⟩ :=
      rfl
    have hbn := block_budgets hg ga ab k 1 m hvar ha hz hs 3
    rw [hb3] at hbn
    have hdom : PositiveBT3.SignedDomain (delta C.theta T) (delta C.theta Candidate.D) := hbn
    have hcoef : PositiveBT3.tilted m (delta C.theta B)∈Icc 1 PositiveBT3.Cmax := ⟨hc1,hrot.2⟩
    have hminor := PositiveBT3.signed_minorant hcoef hdom
    have hactual : PositiveBT3.D (PositiveBT3.tilted m (delta C.theta B)) (delta C.theta T)
        (delta C.theta Candidate.D)≤PositiveBT3.Source.sortedD C false m :=
      PositiveBT3.Source.sortedD_lower false (hsorted Candidate.D)
        (hcontained Candidate.D) hQ hDy hcoef hdom
    have hN : negativePart (delta C.theta T)+negativePart (delta C.theta Candidate.D)∈
        Icc 0 frameCap :=
      ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hbn.2⟩
    have hmono := OrdinaryNegativeEnvelope.V_monotone_smaller (Real.sqrt_nonneg qCap)
      (by norm_num : (0:ℝ)<1) hN
      (show k∈Icc ((1:ℝ)/2) 1 from ⟨hk.1,by linarith [hk.2]⟩)
      (show PositiveBT3.K∈Icc ((1:ℝ)/2) 1 by norm_num [PositiveBT3.K]) hr.1.2
    simp only [PositiveBT3.positiveTotal,PositiveBT3.negativeTotal,PositiveBT3.vstar] at hminor
    have hl : lowBlock t 3 (blocks C hg ga ab k 1 m 3).P (blocks C hg ga ab k 1 m 3).N=
        -PositiveBT3.slope*(positivePart (delta C.theta T)+
          positivePart (delta C.theta Candidate.D))+
        V R k 1 (negativePart (delta C.theta T)+negativePart (delta C.theta Candidate.D)) := by
      rw [hb3]
      simp [lowBlock,PositiveTD.Hybrid.block,lowP,lowQ,PositiveBT3.LowEnvelope.p,
        PositiveBT3.LowEnvelope.q,Block.P,Block.N,k]
    have hs3 : sortedBlocks C hg ga ab k m 3=PositiveBT3.Source.sortedD C false m := rfl
    rw [hl,hs3]
    linarith
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem low_scalar_nonpositive {Q : ℝ} {C : SignedCycle} {hg : Fin 4} (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hz : 0≤delta C.theta B) (hs : delta C.theta E≤0)
    (ht : total C ga ab∈Icc 0 (1/6:ℝ))
    (hflat : (C.point E).a=7/12) (hb : -(C.point E).y∈Icc (0:ℝ) (39/250))
    (he : magnitude C∈Icc (0:ℝ) (1/10))
    (hhg : hg=0∨hg=2) (hfeasible : ∀i,C.Feasible i (owners hg ga ab i)) :
    PositiveBT3.Analytic.lowBaseline (PositiveBT3.lowK (total C ga ab))
      (PositiveBT3.lowM (total C ga ab)) (delta C.theta B)+
      TwoPositive.ASupport.charge (aTotal C ga ab)+NegativeEH.g (magnitude C)+
      (∑i,lowBlock (total C ga ab) i
        (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
          (PositiveBT3.lowM (total C ga ab)) i).P
        (blocks C hg ga ab (PositiveBT3.lowK (total C ga ab)) 1
          (PositiveBT3.lowM (total C ga ab)) i).N)≤0 := by
  let k := PositiveBT3.lowK (total C ga ab)
  let m := PositiveBT3.lowM (total C ga ab)
  have hbud := budgets hg ga ab k 1 m hvar ha hz hs
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hA := PairedE.selected_charge ga ab (hsorted A) (hcontained A) hQ
    (original_error_bound hvar hn G) (original_error_bound hvar hn A)
    (show aTotal C ga ab∈Icc 0 frameCap from ⟨ha,hbud.a_domain.2.trans hbud.total_domain.2⟩)
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hm : 0< m := by dsimp [m]; linarith [hr.2.1]
  have hzframe : delta C.theta B∈Icc 0 frameCap :=
    ⟨hz,hbud.bt_domain.2.trans hbud.total_domain.2⟩
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hQ hm.le hzframe
  have hE := eh_gain_lower .small (k:=k) hflat hb he (by simp)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    low_blocks_lower hg ga ab hsorted hcontained hQ hHy hGy hBy hDy hvar ha hz hs ht i)
  have hid := sorted_decomposition C ga ab hhg k m
  have hupper := stress_nonpositive hg ga ab (show 0≤k by dsimp [k]; linarith [hr.1.1])
    (by norm_num : (0:ℝ)≤1) hm (by norm_num : (0:ℝ)≤1) hzframe hfeasible
  change TwoPositive.ASupport.charge (aTotal C ga ab)≤
    PairedE.primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A) at hA
  change NegativeEH.g (magnitude C)≤ehGain C k 1 at hE
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Source
end
end
end
