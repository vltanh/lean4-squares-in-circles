module

public import SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideMiddle.Data
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: rows 0 to 38 of the pair table `FourTypeCoreSideMiddle`

Each part of 100 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideMiddle
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/four_type_core_side_middle.rows" 1 40 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

/-- Rows 0 to 38. -/
def chunk000 : List AffineRow :=
  rows000_0

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, rows000_0_check]

end SquaresInCircles.Eight.Generated.Pairs.FourTypeCoreSideMiddle
