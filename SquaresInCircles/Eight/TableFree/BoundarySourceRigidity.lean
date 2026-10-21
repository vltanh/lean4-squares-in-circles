module

public import SquaresInCircles.Eight.TableFree.SourcePrimaryRecovery
public import SquaresInCircles.Eight.TableFree.BoundaryBridge
public import SquaresInCircles.Eight.TableFree.StationarySourceOwners

/-!
# The sharp hard source retains its initially selected physical normals

Uncompiled source draft.  A candidate frame is normalized at the actual
source A, so recovering the original common A/B/T/D/E frame identifies
that frame with zero without rotating or moving the source.  The physical
five-corner equality theorem then supplies its own anchor centers and HG
contact.  The strict stationary GA1/EH0 exclusions apply to every original
weak owner, including the initially selected radial-boundary witnesses.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate ExactFamily GeometricModel

/-- Actual canonical source geometry is sufficient for the initially
selected physical-normal interface.  Neither an endpoint equality nor
stationary coordinates are assumed. -/
theorem boundary_source_rigidity_of_canonical {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (I : SignedCycle.HardInput q)
    (hcycle : I.cycle=SignedCycle.atFrame F) (hqq : q≤qStar)
    (ho : Candidate.OwnerRestriction C sourceOwners)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hAD : I.cycle.theta A=I.cycle.theta D)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (horder : I.cycle.theta D≤I.cycle.theta H)
    (hEH : I.cycle.Feasible E 1) :
    q=qStar ∧ StationaryFrames sharpData C.square ∧
      (∀ i,(C.selected i).normal (C.square i) (C.square (next i))=
        stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,(C.square (OriginalFiveCorner.anchorIndex i)).center=
        sharpData.anchorCenters i) ∧
      dot sharpData.e (sub (C.square G).center (C.square H).center)=1 := by
  have hAz : I.cycle.theta A=0 := by
    rw [hcycle]
    exact F.theta_A
  have hDz : I.cycle.theta D=0 := hAD.symm.trans hAz
  have hBD : I.cycle.theta B=I.cycle.theta D := hAB.symm.trans hAD
  let t := I.cycle.theta H-I.cycle.theta D
  have htheta : I.cycle.theta=SourceRecovery.endpointTheta t := by
    funext i
    fin_cases i <;>
      simp [SourceRecovery.endpointTheta,t,H,G,A,B,T,D,E,hHG,hBD,hTD,hAD,hED,hDz]
  have hphysical : I.cycle.actualSquare=C.square := by
    funext i
    rw [hcycle]
    exact SignedCycle.atFrame_actualSquare F i
  have hframes := SourceRecovery.physical_frames htheta
  have ht : 0≤t ∧ t≤Real.pi/4 := I.canonical_tilt horder
  let w : AlignedEndpoint.Witnesses I.cycle.actualSquare :=
    SourceRecovery.endpointWitnesses (SignedCycle.canonicalOwner I.witnesses)
      (SignedCycle.canonicalOwner_allowed I.witnesses) (I.canonicalOwner_feasible hEH)
  have hc := SignedCycle.actualSquare_points_contained I.necessary.sorted I.necessary.contained
  have hs := AlignedEndpoint.sharp_rigidity ht hframes w hc hqq
  have hf : StationaryFrames sharpData I.cycle.actualSquare :=
    AlignedEndpoint.stationary_frames_of_selected_angle hframes hs.2.1
  have hanchors : ∀i : Fin 5,
      (I.cycle.actualSquare (OriginalFiveCorner.anchorIndex i)).center=
        sharpData.anchorCenters i := by
    intro i
    exact (hs.2.2.2.1 i).trans (AlignedEndpoint.selected_anchor_centers i)
  have hA : (I.cycle.actualSquare 2).center=sharpData.pA := by
    simpa [OriginalFiveCorner.anchorIndex,Coordinates.anchorCenters] using hanchors 0
  have hH : (I.cycle.actualSquare 0).center=sharpData.pH := by
    simpa [OriginalFiveCorner.anchorIndex,Coordinates.anchorCenters] using hanchors 4
  have hE : (I.cycle.actualSquare 6).center=sharpData.pE := by
    simpa [OriginalFiveCorner.anchorIndex,Coordinates.anchorCenters] using hanchors 3
  have hcontact : dot sharpData.e
      (sub (I.cycle.actualSquare G).center (I.cycle.actualSquare H).center)=1 := by
    have hg := hs.2.2.2.2.1 H
    have hz : dot sharpData.e
        (sub (I.cycle.actualSquare G).center (I.cycle.actualSquare H).center)-1=0 := by
      simpa [OriginalFiveCorner.gap,hs.2.1,AlignedEndpoint.normal_at_selected_angle,
        OriginalFiveCorner.width,stationaryNormal,projection_eq_dot,H,G,next] using hg
    linarith
  rw [hphysical] at hf hanchors hA hH hE hcontact
  exact ⟨hs.1,hf,selected_normals_after_source_equality C F hf hA hH hE hcontact ho,
    hanchors,hcontact⟩

/-- The full nonpositive hard theorem supplies the original canonical
frames, so the initially selected axes can now be recovered on this same
unmoved boundary source.  All E frames and mixed-owner alternatives remain
part of the actual input. -/
theorem boundary_source_rigidity_of_nonpositive {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (I : SignedCycle.HardInput q)
    (hcycle : I.cycle=SignedCycle.atFrame F)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (ho : Candidate.OwnerRestriction C sourceOwners)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    q=qStar ∧ StationaryFrames sharpData C.square ∧
      (∀ i,(C.selected i).normal (C.square i) (C.square (next i))=
        stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,(C.square (OriginalFiveCorner.anchorIndex i)).center=
        sharpData.anchorCenters i) ∧
      dot sharpData.e (sub (C.square G).center (C.square H).center)=1 := by
  have hs := I.nonpositive_sharp hqL hqq hAB hnorm hAG hGH hDT hTB hHG hTD
  have hG := hs.2.1
  have hBT := hs.2.2.1
  have hT := hs.2.2.2.1
  have hE := hs.2.2.2.2.1
  have hslack := hs.2.2.2.2.2.2.2
  have hEH : I.cycle.Feasible E 1 := by
    change 0≤I.cycle.slack E 1
    rw [hslack E 1 (by simp [terminalOwners,E])]
  apply boundary_source_rigidity_of_canonical F I hcycle hqq ho hG hAB hT
    (hAB.trans (hBT.trans hT)) hE
  · rw [←hAB] at hTB
    exact hDT.trans (hTB.trans (hAG.trans hGH))
  · exact hEH

end SquaresInCircles.Eight.TableFree
