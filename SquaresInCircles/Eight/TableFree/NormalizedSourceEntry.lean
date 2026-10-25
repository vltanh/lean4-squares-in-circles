module

public import SquaresInCircles.Eight.TableFree.PairTerminalRecovery
public import SquaresInCircles.Eight.TableFree.NormalizationBridge
public import SquaresInCircles.Eight.TableFree.SharpEntry

/-!
# Original sharp source after the normal-owner classification

Uncompiled transcription of the assembly in Sections 2--8 of
`HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md` and the original-equality
pullback.  The source-aware G/T outputs are constructed here.  Their actual
paired descendant has hard owners by the complete terminal matrix; the
retained contact obstructions then recover those owners on the untouched
source.  No output, hard witness, frame order, endpoint equality or circle
loss is supplied by the caller.

The last theorem takes the original normal-owner classification as an
explicit argument so the source-to-equality logic remains independently
typeable. The global high-GA/BT2 proof now provides that argument in
`GlobalGAHighSourceComplete`, and constructs an unconditional (uncompiled)
`SharpSourceEntry`. No generated capture is used.
It joins that precise classification obligation to the already drafted
same-radius terminal and initially selected physical-normal conclusions.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate ExactFamily GeometricModel

namespace SignedCycle.NormalizedBoundaryInput

/-- The pair outputs and every terminal alternative are discharged inside
the proof.  The hard axes in the conclusion belong to the original cycle. -/
theorem original_hard_owners {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar) : I.cycle.HardOwners := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨SG⟩ := I.g_source_output hqL hcap
  obtain ⟨ST⟩ := I.t_source_output hqL hcap
  exact (PairTerminalDescendant.source_recovery I hqL hq SG ST hcap).1

/-- The universal hard theorem is applied again to the unchanged source,
after the two original hard axes have been recovered. -/
theorem original_sharp {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar) :
    I.cycle.theta A=I.cycle.theta B ∧
      (I.cycle.point A).y-(I.cycle.point B).y=1 ∧
      q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hh := I.original_hard_owners hqL hq
  exact (I.toHard hh.1 hh.2).hard_sharp hqL hq

end SignedCycle.NormalizedBoundaryInput

/-- Actual normal-owner input gives source physical frames, all initially
selected normals, and the original five anchors.  Neither G/T endpoint
existence nor availability of the hard axes is an extra premise. -/
theorem boundary_source_rigidity_of_normal_input {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (I : SignedCycle.NormalizedBoundaryInput q)
    (hcycle : I.cycle=SignedCycle.atFrame F)
    (hqL : qLow≤q) (hq : q≤qStar)
    (ho : Candidate.OwnerRestriction C SignedCycle.normalOwners) :
    q=qStar ∧ StationaryFrames sharpData C.square ∧
      (∀ i,(C.selected i).normal (C.square i) (C.square (next i))=
        stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,(C.square (OriginalFiveCorner.anchorIndex i)).center=
        sharpData.anchorCenters i) ∧
      dot sharpData.e (sub (C.square G).center (C.square H).center)=1 := by
  have hh := I.original_hard_owners hqL hq
  have hs : Candidate.OwnerRestriction C sourceOwners := by
    simpa only [sourceOwners,SignedCycle.normalOwners] using ho
  exact boundary_source_rigidity_of_hard F (I.toHard hh.1 hh.2) hcycle hqL hq hs

/-- The recovered source radius is literally `qStar`.  Its all-owner
classification is the sole remaining global entry premise of this adapter.
The selected-normal conclusion is transported to the initial source using
the retained physical frames and the original selection equality. -/
theorem source_witnesses_of_normal_owners
    {S : Fin 8 → UnitSquare} (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected)
    (ho : Candidate.OwnerRestriction N.recovered SignedCycle.normalOwners) :
    StationaryFrames sharpData N.source.square ∧
      ∀ i,(N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i := by
  let F := NormalizationBridge.recoveredFrame N
  let I := NormalizationBridge.normalizedInput N sharp_le_Q1 ho
  have hcycle : I.cycle=SignedCycle.atFrame F := rfl
  have hqL : qLow ≤ sourceLevel qStar := by
    rw [sharp_source_level]
    exact le_trans (by norm_num [qLow]) qStar_limits.1.le
  have hq : sourceLevel qStar ≤ qStar := sharp_source_level.le
  obtain ⟨_,hf,hn,_,_⟩ :=
    boundary_source_rigidity_of_normal_input F I hcycle hqL hq ho
  exact ⟨frames_of_same_frames (source_recovered_frames N) hf,
    normals_of_same_frames (source_recovered_frames N) hselected hn⟩

end SquaresInCircles.Eight.TableFree
