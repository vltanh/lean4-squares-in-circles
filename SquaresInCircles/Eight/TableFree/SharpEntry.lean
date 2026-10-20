module

public import SquaresInCircles.Eight.GeometricModel.SharpBoundary
public import SquaresInCircles.Eight.TableFree.SourceEquality
public import SquaresInCircles.Eight.TableFree.StationarySourceOwners

/-!
# Exact replacement obligation for table-free sharp source entry

Uncompiled interface draft.

The completed hand proof supplies the contract below by the global primary
entry matrix and the source-aware equality pullback. SourceEquality contains
the exhaustive source cases, and StationarySourceOwners applies the two
strict mixed-witness exclusions to actual boundary squares. The same-radius
endpoint constructions and the global positive/negative terminal exclusions
have not yet been transcribed in this module.

This file does not postulate their truth: there is no axiom, admitted theorem,
or instance of the contract here. SharpAssembly.compatibility_source_entry is
a concrete implementation from the existing capture theorem and explicitly
inherits its generated dependencies. Replacing that implementation requires
the actual same-radius G/T transports, strict anchor losses, hard-owner
equality and original-source witness comparisons of the hand proof.

In particular, feasibility of newly selected hard owners on a moved endpoint
is not sufficient for this contract. The equalities below concern the
initially retained signed normals on the unchanged original records.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open ExactFamily Coordinates GeometricModel

/-- An explicit construction obligation, not a claimed table-free theorem. -/
def SharpSourceEntry : Prop :=
  ∀ {S : Fin 8 → UnitSquare} (N : GlobalNormalization S qStar),
    N.source.selected=N.recovered.selected →
      StationaryFrames sharpData N.source.square ∧
      ∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i

/-- The remaining geometric theorem must identify this recovered source
itself, before any G/T replacement. Once it does, the actual mixed-owner
pruning and the retained-normal transport are fully instantiated here. -/
theorem source_witnesses_of_recovered_equality
    {S : Fin 8 → UnitSquare} (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected)
    (F : Candidate.Frame N.recovered)
    (hf : StationaryFrames sharpData N.recovered.square)
    (hA : (N.recovered.square 2).center=sharpData.pA)
    (hH : (N.recovered.square 0).center=sharpData.pH)
    (hE : (N.recovered.square 6).center=sharpData.pE)
    (hHG : dot sharpData.e
      (sub (N.recovered.square 1).center (N.recovered.square 0).center)=1)
    (ho : Candidate.OwnerRestriction N.recovered sourceOwners) :
    StationaryFrames sharpData N.source.square ∧
      ∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i := by
  have hn := selected_normals_after_source_equality
    N.recovered F hf hA hH hE hHG ho
  exact ⟨frames_of_same_frames (source_recovered_frames N) hf,
    normals_of_same_frames (source_recovered_frames N) hselected hn⟩

/-- Once the source construction has supplied actual witnesses, the
original-radius dual closes the proof without any local center bounds. -/
theorem sharp_source_entry_original_rigidity
    (entry : SharpSourceEntry) {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected)
    (hp : SqPacking N.squares (0,0) q)
    (hq : q ≤ qStar) :
    q=qStar ∧
      StationaryFrames sharpData N.source.square ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,
        originalPositions N i.castSucc.castSucc=sharpData.anchorCenters i) ∧
      (∀ e : Fin 7, OriginalDual.gap sharpData (originalPositions N) e=0) ∧
      ∃ Z η : ℝ, originalPositions N 5=sharpData.pT Z ∧
        originalPositions N 6=sharpData.pG η := by
  obtain ⟨hf,hn⟩ := entry N hselected
  have hr := sharp_rigidity_of_original_witnesses hq
    (source_contained_at_original_radius N hp) hf
    N.source.selected N.source.feasible hn
  exact ⟨hr.1,hf,hn,hr.2⟩

end SquaresInCircles.Eight.TableFree
