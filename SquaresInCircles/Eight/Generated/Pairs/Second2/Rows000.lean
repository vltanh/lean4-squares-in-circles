module

public import SquaresInCircles.Eight.Generated.Pairs.Second2.Data
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 0 to 397 of the table, checked by `decide +kernel`, a hundred rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Second2
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_2.rows" 1 101 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

def rows000_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_2.rows" 101 201 ↦ AffineRow.ofData

theorem rows000_1_check : checkRows ctx rows000_1 = true := by decide +kernel

def rows000_2 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_2.rows" 201 301 ↦ AffineRow.ofData

theorem rows000_2_check : checkRows ctx rows000_2 = true := by decide +kernel

def rows000_3 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_2.rows" 301 399 ↦ AffineRow.ofData

theorem rows000_3_check : checkRows ctx rows000_3 = true := by decide +kernel

/-- Rows 0 to 397. -/
def chunk000 : List AffineRow :=
  rows000_0 ++ rows000_1 ++ rows000_2 ++ rows000_3

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, checkRows_append, rows000_0_check, rows000_1_check, rows000_2_check,
    rows000_3_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Pairs.Second2
