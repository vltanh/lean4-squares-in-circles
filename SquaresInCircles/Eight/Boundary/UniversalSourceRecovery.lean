module

public import SquaresInCircles.Eight.Boundary.SourcePrimaryRecovery
public import SquaresInCircles.Eight.Owners.Canonical.NegativeCycle
public import SquaresInCircles.Eight.Owners.Stationary.SourceOwners
public import SquaresInCircles.Eight.Words.Crossed.ClampMotionCycle
public import SquaresInCircles.Eight.Words.Crossed.ClampTerminal
public import SquaresInCircles.Eight.Words.One.NegativeEntry

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

section
/-!
## The aligned hard source is stationary

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
end
end
end

section
/-!
## Sharpness of the hard inputs

A hard input at a level `qLow ≤ q ≤ qStar` is sharp (`HardInput.hard_sharp`): `q = qStar`, A and
B have a common frame with `yA - yB = 1`, G has the frame of H, B, T, D and E have a common frame,
the turn `θH - θD` is the angle of `FiveCorner.selected`, the five anchors lie on the circle of
squared radius `qStar`, and every terminal owner of every edge is tight.

The middle conditions `θA = θB`, `yA - yB = 1` and `θT ≤ θA ≤ θG` come first
(`canonical_hard_sharp`). Under them the outer frames are ordered, `θA ≤ θH` and `θD ≤ θB`
(`canonical_hard_outer_order`), and `ordered_hard_sharp` concludes. A crossed order gives a hard
input with a common-frame entry, which the common clamp at the level `q` excludes through the
strict losses of the middle anchors (`common_frame_entry_impossible`; on the side of T the clamp
is built for the reflected geometry and reflected back,
`reflected_common_frame_entry_impossible`). The side with the larger tangent, `yA ≥ 1/2` or
`-yB ≥ 1/2`, is ordered first; its upper bound then puts the other tangent in `[67/200, 1/2]`,
where the small crossed case applies (`crossed_large_HG_impossible`,
`crossed_small_HG_impossible` and their counterparts for T–D). Every hard input satisfies the
middle conditions (`hard_middle`): its canonical middle (`canonicalize_middle`) is sharp, so its
anchors lie on the circle of `qStar`, and a defect of the middle of the input would give one of
its anchors a strict loss against that circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate Stationary GeometricModel

theorem HardInput.common_frame_entry_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) (C : CommonFrameEntry I.outerGeometry) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨O⟩ := I.outerGeometry.common_clamp_data hqL hcap C
  exact I.crossed_clamp_endpoint_impossible hqL hq C.H_before.le O

/-- A common-frame entry of the reflected outer geometry is impossible: the clamp is built for
the reflected geometry, reflected back to the side of T, and excluded on the hard input itself,
with its own E. -/
theorem HardInput.reflected_common_frame_entry_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (C : CommonFrameEntry I.outerGeometry.reflected) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨O⟩ := I.outerGeometry.reflected.common_clamp_data hqL hcap C
  have O' : CrossedClampData q (I.cycle.point D).reflect (I.cycle.point G).reflect
      0 (I.cycle.theta G-I.cycle.theta D) := by
    change CrossedClampData q (I.cycle.point D).reflect (I.cycle.point G).reflect
      0 ((I.cycle.theta B-I.cycle.theta D)-(I.cycle.theta B-I.cycle.theta G)) at O
    convert O using 1
    ring
  have hBD : I.cycle.theta B≤I.cycle.theta D := by
    have hh := C.H_before
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta B at hh
    linarith
  exact I.crossed_TD_clamp_endpoint_impossible hqL hq hBD O'.reflectTD

theorem HardInput.crossed_large_HG_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A) (hlarge : 1/2≤(I.cycle.point A).y) : False := by
  obtain ⟨O,C⟩ := I.crossed_HG_large_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hHA hlarge
  exact (I.fromCrossedGAData hAB O).common_frame_entry_impossible hqL hq C

theorem HardInput.crossed_small_HG_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hsmall : (I.cycle.point A).y∈Icc (67/200:ℝ) (1/2)) : False := by
  obtain ⟨O,C⟩ := I.crossed_HG_small_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hHA hsmall
  exact (I.fromCrossedGAData hAB O).common_frame_entry_impossible hqL hq C

theorem HardInput.crossed_large_TD_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D) (hlarge : 1/2≤ -(I.cycle.point B).y) : False := by
  obtain ⟨O,C⟩ := I.crossed_TD_large_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hBD hlarge
  exact (I.fromCrossedBTData hAB O).reflected_common_frame_entry_impossible hqL hq C

theorem HardInput.crossed_small_TD_impossible {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hBD : I.cycle.theta B<I.cycle.theta D)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200:ℝ) (1/2)) : False := by
  obtain ⟨O,C⟩ := I.crossed_TD_small_entry hqL (hq.trans qStar_limits.2.2.le)
    hAB hnorm hTA hAG hBD hsmall
  exact (I.fromCrossedBTData hAB O).reflected_common_frame_entry_impossible hqL hq C

/-- Under the middle conditions the outer frames are ordered: `θA ≤ θH` and `θD ≤ θB`. The side
with the larger tangent is ordered first, and its upper bound puts the other tangent in
`[67/200, 1/2]`, so no bound on that tangent is assumed. -/
theorem HardInput.canonical_hard_outer_order {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) :
    I.cycle.theta A≤I.cycle.theta H ∧ I.cycle.theta D≤I.cycle.theta B := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  have hTB : I.cycle.theta T≤I.cycle.theta B := by rw [←hAB]; exact hTA
  by_cases hlargeA : 1/2≤(I.cycle.point A).y
  · have hAH : I.cycle.theta A≤I.cycle.theta H := by
      by_contra! hHA
      exact I.crossed_large_HG_impossible hqL hq hAB hnorm hTA hAG hHA hlargeA
    have hG := I.large_middle_G_negative hcap hAB hnorm hTA hAG hlargeA
    have hAy := I.ordered_large_A_upper hqL hcap hAH hAG hG.le hlargeA
    have hsmallB : -(I.cycle.point B).y∈Icc (67/200:ℝ) (1/2) := by
      constructor <;> linarith
    refine ⟨hAH,?_⟩
    by_contra! hBD
    exact I.crossed_small_TD_impossible hqL hq hAB hnorm hTA hAG hBD hsmallB
  · have hlargeB : 1/2≤ -(I.cycle.point B).y := by linarith
    have hDB : I.cycle.theta D≤I.cycle.theta B := by
      by_contra! hBD
      exact I.crossed_large_TD_impossible hqL hq hAB hnorm hTA hAG hBD hlargeB
    have hT := I.large_middle_T_positive hcap hAB hnorm hTA hAG hlargeB
    have hBy := I.ordered_large_B_upper hqL hcap hDB hTB hT.le hlargeB
    have hsmallA : (I.cycle.point A).y∈Icc (67/200:ℝ) (1/2) := by
      constructor <;> linarith
    refine ⟨?_,hDB⟩
    by_contra! hHA
    exact I.crossed_small_HG_impossible hqL hq hAB hnorm hTA hAG hHA hsmallA

theorem HardInput.canonical_hard_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  obtain ⟨hAH,hDB⟩ := I.canonical_hard_outer_order hqL hq hAB hnorm hTA hAG
  exact I.ordered_hard_sharp hqL hq hAB hnorm hAH hAG hDB (by rw [←hAB]; exact hTA)

/-- Every hard input at a level in `[qLow, qStar]` satisfies the middle conditions `θA = θB`,
`θT ≤ θA ≤ θG` and `yA - yB = 1`: a defect would give one of its anchors a strict loss against
its sharp canonical middle, whose anchors lie on the circle of `qStar`. -/
theorem HardInput.hard_middle {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) :
    I.cycle.theta A=I.cycle.theta B ∧
      I.cycle.theta A∈Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hJAB,hJrange,hJnorm,hnon,hstrict,hfixed⟩ := I.canonicalize_middle hcap
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by rw [hG.2]; exact hJrange.2
  have hJTA : J.cycle.theta T≤J.cycle.theta A := by rw [hT.2]; exact hJrange.1
  obtain ⟨_,_,_,_,_,_,_,_,hJon,_⟩ := J.canonical_hard_sharp hqL hq hJAB hJnorm hJTA hJAG
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle (fun i _ => (I.necessary.contained i).trans hq) hJon
  have hAB : I.cycle.theta A=I.cycle.theta B := by
    by_contra hne
    exact hnoloss (hstrict (Or.inl hne))
  have hTA : I.cycle.theta T≤I.cycle.theta A := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inl hbad)))
  have hAG : I.cycle.theta A≤I.cycle.theta G := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inr (Or.inl hbad))))
  have hsum : (I.cycle.point A).y-(I.cycle.point B).y≤1 := by
    by_contra! hbad
    exact hnoloss (hstrict (Or.inr (Or.inr (Or.inr hbad))))
  exact ⟨hAB,⟨hTA,hAG⟩,le_antisymm hsum (I.aligned_AB_gap hAB)⟩

/-- A hard input at a level in `[qLow, qStar]` is sharp: `q = qStar`, the frames and the turn of
the optimal configuration, the anchors on the circle of `qStar` and every terminal owner tight.
Nothing is assumed about its middle, its tangents, the signs of G and T, the order of its outer
frames or the signs of the errors of H–G and T–D. -/
theorem HardInput.hard_sharp {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  obtain ⟨hAB,hrange,hnorm⟩ := I.hard_middle hqL hq
  exact I.canonical_hard_sharp hqL hq hAB hnorm hrange.1 hrange.2

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
/-!
## The negative terminal cases

The anchors of a hard input at a level `qLow ≤ q ≤ qStar` lie on the circle of squared radius
`qStar` (`HardInput.all_anchors_on`, from `HardInput.hard_sharp`). Each negative terminal case of
a normalized boundary input leads to a hard input at which the anchor H, or D, has a strict loss
against that circle, which is impossible (`NegativeGEntry.false_at_sharp`,
`HardTEntry.false_at_sharp`). So neither the case of G negative and T hard
(`negative_g_impossible`) nor that of G hard and T negative (`negative_t_impossible`) occurs,
whatever the error of the opposite edge, T–D or H–G.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle

theorem HardInput.all_anchors_on {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) : AllAnchorsOn qStar I.cycle := by
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ := I.hard_sharp hqL hq
  exact hcircle

end SignedCycle

namespace AlignedNegative

/-- A negative G entry at a level in `[qLow, qStar]` is impossible: the anchor H of its target
hard input, which keeps the E of the cycle, lies on the circle of `qStar`, while the entry gives H
a strict loss. -/
theorem NegativeGEntry.false_at_sharp {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : NegativeGEntry q C w)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hH : (C.point H).Contained q) : False := by
  have hcircle := J.target.all_anchors_on hqL hq
  exact circle_loss_impossible (hH.trans hq) J.H_circle_loss
    (hcircle H (by simp [anchorVertices]))

/-- The case of G negative and T hard does not occur: G on the frame of H with `θA < θH` and
`yG ≤ 0`, G–A separated along the axis one but not zero, and B–T along the axis two, for any
error and either owner of T–D. -/
theorem negative_g_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnotGA : ¬I.cycle.Feasible G 0) (hBT : I.cycle.Feasible B 2) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := aligned_negative_boundary_entry I hqL hcap
    hHG htG hyG hGA hnotGA hBT
  exact J.false_at_sharp hqL hq (I.necessary.contained H)

end AlignedNegative

namespace DirectNegativeT

/-- A hard T entry at a level in `[qLow, qStar]` is impossible: the anchor D of its hard input
lies on the circle of `qStar`, while the entry gives D a strict loss, whatever the error of
H–G. -/
theorem HardTEntry.false_at_sharp {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : HardTEntry q C w)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hD : (C.point D).Contained q) : False := by
  have hcircle := J.input.all_anchors_on hqL hq
  exact circle_loss_impossible (hD.trans hq) J.D_circle_loss
    (hcircle D (by simp [anchorVertices]))

/-- The case of G hard and T negative does not occur: T on the frame of D with `θD < θB` and
`yT ≥ 0`, B–T separated along the axis three but not two, and G–A along the axis zero. E is the
point of the input, on the core or on the outer circle, with `y ≤ 0`. -/
theorem negative_t_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hyT : 0≤(I.cycle.point T).y) (hBT : I.cycle.Feasible B 3)
    (hnotBT : ¬I.cycle.Feasible B 2) (hGA : I.cycle.Feasible G 0) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := one_negative_t_entry I.necessary hqL hcap I.anchors_normal
    I.witnesses I.zero_signs I.E_nonpos (I.radial E)
    hTD htT hyT hBT hnotBT hGA
  exact J.false_at_sharp hqL hq (I.necessary.contained D)

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
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
end
end
end
