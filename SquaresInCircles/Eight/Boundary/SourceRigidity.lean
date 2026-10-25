module

public import SquaresInCircles.Eight.Boundary.Bridge
public import SquaresInCircles.Eight.Owners.Canonical.HardEndpoint
public import SquaresInCircles.Eight.Owners.Stationary.SourceOwners

/-!
# Eight squares: the aligned hard source is stationary

Let `C` be a boundary cycle at a level `q ≤ qStar` with a candidate frame `F`, and `I` the hard
input on the signed cycle `atFrame F`, with source owners as witnesses. If A, B, T, D and E have a
common frame, G and H a common frame at least as large, and E–H is separated along the axis one,
then `q = qStar`, the squares of `C` have the frames of the stationary configuration `sharpData`,
its five anchors are at the anchor centres of `sharpData`, the contact H–G is tight, and every
witness has the stationary normal (`boundary_source_rigidity_of_canonical`). The frame `F`
vanishes at A, so the common frame is `0` and the cycle is an aligned endpoint; its sharp
rigidity (`AlignedEndpoint.sharp_rigidity`) gives the anchors and the contact, and the strict
comparisons of GA1 with GA0 and of EH0 with EH1 give the normals of all the witnesses
(`selected_normals_after_source_equality`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

/-- A hard input on a boundary cycle with source owners, A, B, T, D and E on a common frame, G
and H on a common frame no smaller, and E–H feasible along the axis one, is stationary:
`q = qStar`, the frames and the normals of `sharpData`, its anchor centres and the tight contact
H–G. -/
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
  set t := I.cycle.theta H-I.cycle.theta D with ht_def
  have htheta : I.cycle.theta=SourceRecovery.endpointTheta t := by
    simp only [H,G,A,B,T,D,E] at hHG hBD hTD hAD hED hDz ht_def
    funext i
    fin_cases i <;>
      simp [SourceRecovery.endpointTheta,ht_def,hHG,hBD,hTD,hAD,hED,hDz]
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
    rw [hs.2.1] at hg
    unfold OriginalFiveCorner.gap at hg
    rw [AlignedEndpoint.normal_at_selected_angle] at hg
    have hw : OriginalFiveCorner.width FiveCorner.selected.angle H=1 := by
      simp [OriginalFiveCorner.width,H]
    have hn : stationaryNormal sharpData H=sharpData.e := by
      simp [stationaryNormal,H]
    rw [hw,hn,projection_eq_dot] at hg
    have hnext : next H=G := rfl
    rw [hnext] at hg
    linarith
  rw [hphysical] at hf hanchors hA hH hE hcontact
  exact ⟨hs.1,hf,selected_normals_after_source_equality C F hf hA hH hE hcontact ho,
    hanchors,hcontact⟩

end SquaresInCircles.Eight
