module

public import SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideHigh.Data
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: rows 0 to 40 of the pair table `FourTypeCoreSideHigh`

Each part of 100 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideHigh
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/four_type_core_side_high.rows" 1 42 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

/-- Rows 0 to 40. -/
def chunk000 : List AffineRow :=
  rows000_0

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, rows000_0_check]

end SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideHigh
