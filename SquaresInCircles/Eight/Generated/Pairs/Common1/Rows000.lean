module

public import SquaresInCircles.Eight.Generated.Pairs.Common1.Data
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 0 to 175 of the table, checked by `decide +kernel`, a hundred rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Common1
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/common_1.rows" 1 101 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

def rows000_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/common_1.rows" 101 177 ↦ AffineRow.ofData

theorem rows000_1_check : checkRows ctx rows000_1 = true := by decide +kernel

/-- Rows 0 to 175. -/
def chunk000 : List AffineRow :=
  rows000_0 ++ rows000_1

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, checkRows_append, rows000_0_check, rows000_1_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Pairs.Common1
