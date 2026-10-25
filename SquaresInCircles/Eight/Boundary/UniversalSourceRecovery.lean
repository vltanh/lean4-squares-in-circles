module

public import SquaresInCircles.Eight.Boundary.UniversalHardSharp
public import SquaresInCircles.Eight.Boundary.SourcePrimaryRecovery
public import SquaresInCircles.Eight.Boundary.SourceRigidity

/-!
# Eight squares: sharpness of the source

Let `I` be a normalized boundary input at a level `qLow ≤ q ≤ qStar`, with pair moves of G and T
that keep track of their source. If G–A is separated along the axis zero and B–T along the axis
two after both moves, the cycle after the moves is a hard input, hence sharp, with ordered frames
and tight contacts H–G and T–D. The moves then recover the hard axes on `I` itself, leave `I`
unchanged, and `I` is sharp (`NormalizedBoundaryInput.pair_source_recovery`). A hard input on a
boundary cycle whose witnesses are source owners is stationary: its frames, the normals of all
its witnesses, that of E–H included, its five anchor centres and the contact H–G are those of
`sharpData` (`boundary_source_rigidity_of_hard`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle.NormalizedBoundaryInput

theorem pair_source_recovery {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (SG : GPairSourceOutput q (I.cycle.point H) (I.cycle.point G)
      (I.cycle.point A) (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A))
    (ST : TPairSourceOutput q (I.cycle.point B) (I.cycle.point T)
      (I.cycle.point D) (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D))
    (hcap : q≤qCap)
    (hGA : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible G 0)
    (hBT : (I.pairDescendant hcap SG.output ST.output).cycle.Feasible B 2) :
    I.cycle.HardOwners ∧
      (I.pairDescendant hcap SG.output ST.output).cycle=I.cycle ∧
      I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  let J := I.pairDescendant hcap SG.output ST.output
  let K := J.toHard hGA hBT
  obtain ⟨hAB,_,_,hG,hBT',hTD,hE,_,_,hslack⟩ := K.hard_sharp hqL hq
  obtain ⟨_,hrange,_⟩ := K.hard_middle hqL hq
  have hAH : J.cycle.theta A≤J.cycle.theta H := hrange.2.trans hG.le
  have hDB : J.cycle.theta D≤J.cycle.theta B := (hTD.symm.trans hBT'.symm).le
  have hHGzero : J.cycle.slack H SG.output.hgOwner=0 := by
    apply hslack
    rcases SG.output.hg_allowed with h | h <;> simp [h,terminalOwners,H]
  have hTDzero : J.cycle.slack T ST.output.tdOwner=0 := by
    apply hslack
    rcases ST.output.td_allowed with h | h <;> simp [h,terminalOwners,T]
  have hhard := I.toBoundaryInput.original_hard_of_pair_contacts hcap SG ST hGA hBT
    hAH hDB hHGzero hTDzero
  have heq := I.toBoundaryInput.pairDescendant_eq_original_of_hard hcap SG ST hhard
  exact ⟨hhard,heq,(I.toHard hhard.1 hhard.2).hard_sharp hqL hq⟩

end SignedCycle.NormalizedBoundaryInput

/-- A hard input at a level in `[qLow, qStar]`, on a boundary cycle whose witnesses are source
owners, is stationary: `q = qStar`, the frames and the normals of `sharpData`, its anchor centres
and the tight contact H–G. -/
theorem boundary_source_rigidity_of_hard {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (I : SignedCycle.HardInput q)
    (hcycle : I.cycle=SignedCycle.atFrame F)
    (hqL : qLow≤q) (hq : q≤qStar)
    (ho : Candidate.OwnerRestriction C sourceOwners) :
    q=qStar ∧ StationaryFrames sharpData C.square ∧
      (∀ i,(C.selected i).normal (C.square i) (C.square (next i))=
        stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,(C.square (OriginalFiveCorner.anchorIndex i)).center=
        sharpData.anchorCenters i) ∧
      dot sharpData.e (sub (C.square G).center (C.square H).center)=1 := by
  obtain ⟨hAB,_,_,hG,hBT,hT,hE,_,_,hslack⟩ := I.hard_sharp hqL hq
  obtain ⟨_,hrange,_⟩ := I.hard_middle hqL hq
  have hEH : I.cycle.Feasible E 1 := by
    change 0≤I.cycle.slack E 1
    rw [hslack E 1 (by simp [terminalOwners,E])]
  apply boundary_source_rigidity_of_canonical F I hcycle hq ho hG hAB hT
    (hAB.trans (hBT.trans hT)) hE
  · exact hT.symm.le.trans (hrange.1.trans (hrange.2.trans hG.le))
  · exact hEH

end SquaresInCircles.Eight
