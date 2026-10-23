module

public import SquaresInCircles.Eight.GeometricModel.SharpBoundary
public import SquaresInCircles.Eight.TableFree.SourceEquality
public import SquaresInCircles.Eight.TableFree.StationarySourceOwners

/-!
# Original-source sharp entry: exact table-free interface

This module defines `SharpSourceEntry`, which refers to the *initially*
retained physical normals of the actual original source and to the
actual squared radius, not the hard witness of a moved G or T endpoint.

The unconditional proof body has now been drafted in
`GlobalGAHighSourceComplete.table_free_sharp_source_entry`.
`GeometricModel.SharpAssembly` imports that theorem rather than the
generated-capture compatibility implementation. This interface module
keeps the conditional original-radius dual and therefore does not
import the downstream source construction (which would cause a cycle).

No axiom or admission supplies `SharpSourceEntry` in this module.
The full source-to-public proof remains uncompiled and unverified.
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
