module

public import SquaresInCircles.Eight.Equality.SharpBoundary
public import SquaresInCircles.Eight.Equality.SharpOriginal

/-!
# Eight squares: the stationary frames as the entry to the dual

`SharpSourceEntry` states that every boundary normalization at the stationary level whose
separating axes are those chosen on the packing has the stationary frames and the stationary
normals (`stationaryNormal`). Given it, the dual at the original centres closes the proof
(`sharp_source_entry_original_rigidity`): the squared radius is `qStar`, the five squares with a
corner on the circle are those of the stationary packing, every gap vanishes, and `T` and `G`
lie on their slider lines. `SharpSourceEntry` is proved in `Owners/GA/High/SourceComplete.lean`.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Stationary Coordinates GeometricModel

/-- Every boundary normalization at `qStar` with the separating axes of the packing has the
stationary frames and normals. -/
def SharpSourceEntry : Prop :=
  ∀ {S : Fin 8 → UnitSquare} (N : GlobalNormalization S qStar),
    N.source.selected=N.recovered.selected →
      StationaryFrames sharpData N.source.square ∧
      ∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i

/-- With the stationary frames and normals, the dual at the original centres gives the radius,
the five fixed squares, the vanishing gaps and the two slider lines. -/
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

end SquaresInCircles.Eight
