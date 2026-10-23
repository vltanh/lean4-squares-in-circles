module

public import SquaresInCircles.Eight.TableFree.SourcePrimaryRecovery
public import SquaresInCircles.Eight.TableFree.OrderedHardSharp
public import SquaresInCircles.Eight.TableFree.BoundarySourceRigidity

/-!
# Original-source recovery from the full ordered hard terminal

Uncompiled source draft.  The ordered hard theorem covers every actual
HG/TD owner, arbitrary individual outer-error signs, and the original
intermediate signs.  Its retained-contact equalities contradict each
source-aware obstruction to an initially missing GA0 or BT2 axis.
Only after recovering those original hard axes does fixed-if-hard
identify the pair descendant with its original source.  The physical
rigidity theorem then concerns that same untouched boundary record.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate ExactFamily GeometricModel

namespace SignedCycle.NormalizedBoundaryInput

theorem ordered_pair_source_recovery {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hcap : q≤qCap)
    (hGA : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible B 2)
    (hAB : (I.pairDescendant hcap SG.output ST.output).cycle.theta A=
      (I.pairDescendant hcap SG.output ST.output).cycle.theta B)
    (hnorm : ((I.pairDescendant hcap SG.output ST.output).cycle.point A).y-
      ((I.pairDescendant hcap SG.output ST.output).cycle.point B).y=1)
    (hAH : (I.pairDescendant hcap SG.output ST.output).cycle.theta A≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta H)
    (hAG : (I.pairDescendant hcap SG.output ST.output).cycle.theta A≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta G)
    (hDB : (I.pairDescendant hcap SG.output ST.output).cycle.theta D≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta B)
    (hTB : (I.pairDescendant hcap SG.output ST.output).cycle.theta T≤
      (I.pairDescendant hcap SG.output ST.output).cycle.theta B) :
    I.cycle.HardOwners ∧
      (I.pairDescendant hcap SG.output ST.output).cycle=I.cycle ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta A=I.cycle.theta B ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  let J := I.pairDescendant hcap SG.output ST.output
  let K := J.toHard hGA hBT
  obtain ⟨hAB',_,hq',hG',hBT',hT',hE',ht',hOn',hslack⟩ :=
    K.ordered_hard_sharp hqL hqq hAB hnorm hAH hAG hDB hTB
  have hHGzero : J.cycle.slack H SG.output.hgOwner=0 := by
    apply hslack
    rcases SG.output.hg_allowed with h | h <;> simp [h,terminalOwners,H]
  have hTDzero : J.cycle.slack T ST.output.tdOwner=0 := by
    apply hslack
    rcases ST.output.td_allowed with h | h <;> simp [h,terminalOwners,T]
  have hhard := I.toBoundaryInput.original_hard_of_pair_contacts hcap SG ST hGA hBT
    hAH hDB hHGzero hTDzero
  have heq := I.toBoundaryInput.pairDescendant_eq_original_of_hard hcap SG ST hhard
  refine ⟨hhard,heq,?_⟩
  have hs : q=qStar ∧ J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta B=J.cycle.theta T ∧ J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta E=J.cycle.theta D ∧
      J.cycle.theta H-J.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar J.cycle ∧
      ∀i j,j∈terminalOwners i → J.cycle.slack i j=0 :=
    ⟨hq',hG',hAB',hBT',hT',hE',ht',hOn',hslack⟩
  simpa only [show J.cycle=I.cycle from heq] using hs

end SignedCycle.NormalizedBoundaryInput

/-- The initially selected physical axes are recovered from the original
ordered hard source.  No original G/T sign and no individual HG/TD
error sign is supplied; the actual hard theorem proves their terminal
equalities before the strict stationary owner exclusions are applied. -/
theorem boundary_source_rigidity_of_ordered {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (I : SignedCycle.HardInput q)
    (hcycle : I.cycle=SignedCycle.atFrame F)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (ho : Candidate.OwnerRestriction C sourceOwners)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B) :
    q=qStar ∧ StationaryFrames sharpData C.square ∧
      (∀ i,(C.selected i).normal (C.square i) (C.square (next i))=
        stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,(C.square (OriginalFiveCorner.anchorIndex i)).center=
        sharpData.anchorCenters i) ∧
      dot sharpData.e (sub (C.square G).center (C.square H).center)=1 := by
  obtain ⟨_,_,_,hG,hBT,hT,hE,_,_,hslack⟩ :=
    I.ordered_hard_sharp hqL hqq hAB hnorm hAH hAG hDB hTB
  have hEH : I.cycle.Feasible E 1 := by
    change 0≤I.cycle.slack E 1
    rw [hslack E 1 (by simp [terminalOwners,E])]
  apply boundary_source_rigidity_of_canonical F I hcycle hqq ho hG hAB hT
    (hAB.trans (hBT.trans hT)) hE
  · rw [←hAB] at hDB
    exact hDB.trans hAH
  · exact hEH

end SquaresInCircles.Eight.TableFree
