module

public import SquaresInCircles.Eight.Generated.Pairs.FourTypeLowLow.Data
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 0 to 35 of the table, checked by `decide +kernel`, a hundred rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.FourTypeLowLow
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/four_type_low_low.rows" 1 37 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

/-- Rows 0 to 35. -/
def chunk000 : List AffineRow :=
  rows000_0

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, checkRows_append, rows000_0_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Pairs.FourTypeLowLow
