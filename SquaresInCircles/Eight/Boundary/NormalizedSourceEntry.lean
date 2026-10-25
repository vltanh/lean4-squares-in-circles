module

public import SquaresInCircles.Eight.Equality.SharpBoundary
public import SquaresInCircles.Eight.Owners.NormalizationBridge
public import SquaresInCircles.Eight.Frames.Pair.TerminalRecovery

/-!
# Eight squares: the sharp source with normal owners

A normalized boundary input at a level `qLow ≤ q ≤ qStar` has hard owners
(`NormalizedBoundaryInput.original_hard_owners`): the pair moves of G and T that keep track of
their source exist, the terminal matrix gives hard owners on the cycle after both moves, and the
contacts that the moves keep recover them on the input itself
(`PairTerminalDescendant.source_recovery`). With normal owners on its boundary cycle, the input
is then stationary: `q = qStar`, the frames and the normals of `sharpData`, the five anchor
centres and the tight contact H–G (`boundary_source_rigidity_of_normal_input`). For the global
normalization of a packing at `qStar` whose recovered cycle has normal owners and the witnesses
of the source, the squares of the source have the stationary frames and its witnesses the
stationary normals (`source_witnesses_of_normal_owners`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle.NormalizedBoundaryInput

/-- A normalized boundary input at a level in `[qLow, qStar]` has hard owners on its own
cycle. -/
theorem original_hard_owners {q : ℝ} (I : NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar) : I.cycle.HardOwners := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨SG⟩ := I.g_source_output hqL hcap
  obtain ⟨ST⟩ := I.t_source_output hqL hcap
  exact (PairTerminalDescendant.source_recovery I hqL hq SG ST hcap).1

end SignedCycle.NormalizedBoundaryInput

/-- A normalized boundary input at a level in `[qLow, qStar]`, on a boundary cycle with normal
owners, is stationary: `q = qStar`, the frames and the normals of `sharpData`, its anchor
centres and the tight contact H–G. -/
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

/-- In the global normalization of a packing at `qStar`, if the recovered cycle has normal
owners and the witnesses of the source, the squares of the source have the stationary frames and
its witnesses the stationary normals. The source level is `qStar` (`sharp_source_level`), and
frames and normals pass from the recovered cycle to the source, which has the same frames. -/
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

end SquaresInCircles.Eight
