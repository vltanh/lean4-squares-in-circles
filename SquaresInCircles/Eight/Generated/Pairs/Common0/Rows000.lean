module

public import SquaresInCircles.Eight.Generated.Pairs.Common0.Data
public meta import SquaresInCircles.Eight.IntRows

/-!
# Eight squares: rows 0 to 119 of the pair table `Common0`

Each part of 100 rows passes `checkRows`, evaluated by the kernel.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Common0
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/common_0.rows" 1 101 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

def rows000_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/common_0.rows" 101 121 ↦ AffineRow.ofData

theorem rows000_1_check : checkRows ctx rows000_1 = true := by decide +kernel

/-- Rows 0 to 119. -/
def chunk000 : List AffineRow :=
  rows000_0 ++ rows000_1

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, checkRows_append, rows000_0_check, rows000_1_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Pairs.Common0
