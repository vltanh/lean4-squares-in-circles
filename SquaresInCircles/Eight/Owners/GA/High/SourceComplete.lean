module

public import SquaresInCircles.Eight.Owners.GA.High.BT2Complete

/-!
# Eight squares: the stationary frames of every boundary cycle

`sharp_source_entry` combines `high_GA_BT2_exclusion` with `sharp_source_entry_of_BT2_exclusion`:
the boundary cycle at the stationary level has the stationary frames and normals. With the dual
at the original centres, a packing in the disk of squared radius `q ≤ qStar` has `q = qStar`, its
five squares with a corner on the circle are those of the stationary packing, every gap vanishes,
and `T` and `G` lie on their slider lines (`sharp_original_rigidity`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Stationary Coordinates GeometricModel

/-- Every boundary normalization at `qStar` with the separating axes of the packing has the
stationary frames and normals. -/
theorem sharp_source_entry : SharpSourceEntry :=
  sharp_source_entry_of_BT2_exclusion high_GA_BT2_exclusion

/-- A packing in the disk of squared radius `q ≤ qStar` has `q = qStar`, the five anchors at
their stationary positions, no gap, and `T`, `G` on their slider lines. -/
theorem sharp_original_rigidity
    {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected)
    (hp : SqPacking N.squares (0,0) q)
    (hq : q≤qStar) :
    q=qStar ∧
      StationaryFrames sharpData N.source.square ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,
        GeometricModel.originalPositions N i.castSucc.castSucc=
          sharpData.anchorCenters i) ∧
      (∀ e : Fin 7,
        OriginalDual.gap sharpData (GeometricModel.originalPositions N) e=0) ∧
      ∃ Z η : ℝ,
        GeometricModel.originalPositions N 5=sharpData.pT Z ∧
        GeometricModel.originalPositions N 6=sharpData.pG η :=
  sharp_source_entry_original_rigidity
    sharp_source_entry N hselected hp hq

end SquaresInCircles.Eight
