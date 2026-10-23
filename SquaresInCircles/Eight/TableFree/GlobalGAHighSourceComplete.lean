module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2Complete

/-!
# Unconditional table-free source entry from the full original-owner proof

The final high-GA/BT2 source exclusion is derived for all original
physical candidate sources, all admissible weakly feasible selected
normals, signed error patterns, E radial kinds and same-q A/T/E
normalizations. It is fed to the source-to-hard-terminal equality
transport and the original selected-normal recovery from the existing
source module.

Unlike the former conditional adapter, the result below has no
parameter of type HighGABT2Exclusion or SharpSourceEntry. It does not
import Candidate.Capture or a generated owner/word lookup.

This is the end-to-end uncompiled table-free source draft, not a
kernel-certified proof. Compilation/CI deliberately remain deferred.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree

/-- The original sharp source is stationary with every originally
retained selected physical normal, without generated capture. -/
theorem table_free_sharp_source_entry : SharpSourceEntry :=
  sharp_source_entry_of_BT2_exclusion high_GA_BT2_exclusion

/-- The original-radius sharp rigidity and anchor/equality conclusions
follow through the already-drafted original-center dual. -/
theorem table_free_original_rigidity
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
    table_free_sharp_source_entry N hselected hp hq

end SquaresInCircles.Eight.TableFree
