module

public import SquaresInCircles.Eight.Generated.Pairs.Second5.Data
public meta import SquaresInCircles.Eight.IntRows

/-! Rows 0 to 1577 of the table, checked by `decide +kernel`, a hundred rows a theorem. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Pairs.Second5
open Arithmetic Arithmetic.PairCover

set_option maxRecDepth 100000

def rows000_0 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1 101 ↦ AffineRow.ofData

theorem rows000_0_check : checkRows ctx rows000_0 = true := by decide +kernel

def rows000_1 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 101 201 ↦ AffineRow.ofData

theorem rows000_1_check : checkRows ctx rows000_1 = true := by decide +kernel

def rows000_2 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 201 301 ↦ AffineRow.ofData

theorem rows000_2_check : checkRows ctx rows000_2 = true := by decide +kernel

def rows000_3 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 301 401 ↦ AffineRow.ofData

theorem rows000_3_check : checkRows ctx rows000_3 = true := by decide +kernel

def rows000_4 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 401 501 ↦ AffineRow.ofData

theorem rows000_4_check : checkRows ctx rows000_4 = true := by decide +kernel

def rows000_5 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 501 601 ↦ AffineRow.ofData

theorem rows000_5_check : checkRows ctx rows000_5 = true := by decide +kernel

def rows000_6 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 601 701 ↦ AffineRow.ofData

theorem rows000_6_check : checkRows ctx rows000_6 = true := by decide +kernel

def rows000_7 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 701 801 ↦ AffineRow.ofData

theorem rows000_7_check : checkRows ctx rows000_7 = true := by decide +kernel

def rows000_8 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 801 901 ↦ AffineRow.ofData

theorem rows000_8_check : checkRows ctx rows000_8 = true := by decide +kernel

def rows000_9 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 901 1001 ↦ AffineRow.ofData

theorem rows000_9_check : checkRows ctx rows000_9 = true := by decide +kernel

def rows000_10 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1001 1101 ↦ AffineRow.ofData

theorem rows000_10_check : checkRows ctx rows000_10 = true := by decide +kernel

def rows000_11 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1101 1201 ↦ AffineRow.ofData

theorem rows000_11_check : checkRows ctx rows000_11 = true := by decide +kernel

def rows000_12 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1201 1301 ↦ AffineRow.ofData

theorem rows000_12_check : checkRows ctx rows000_12 = true := by decide +kernel

def rows000_13 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1301 1401 ↦ AffineRow.ofData

theorem rows000_13_check : checkRows ctx rows000_13 = true := by decide +kernel

def rows000_14 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1401 1501 ↦ AffineRow.ofData

theorem rows000_14_check : checkRows ctx rows000_14 = true := by decide +kernel

def rows000_15 : List AffineRow :=
  nat_rows% "../../../../../data/eight/pairs/second_5.rows" 1501 1579 ↦ AffineRow.ofData

theorem rows000_15_check : checkRows ctx rows000_15 = true := by decide +kernel

/-- Rows 0 to 1577. -/
def chunk000 : List AffineRow :=
  rows000_0 ++ rows000_1 ++ rows000_2 ++ rows000_3 ++ rows000_4 ++ rows000_5 ++ rows000_6 ++
    rows000_7 ++ rows000_8 ++ rows000_9 ++ rows000_10 ++ rows000_11 ++ rows000_12 ++ rows000_13 ++
    rows000_14 ++ rows000_15

theorem chunk000_check : checkRows ctx chunk000 = true := by
  simp only [chunk000, checkRows_append, rows000_0_check, rows000_1_check, rows000_2_check,
    rows000_3_check, rows000_4_check, rows000_5_check, rows000_6_check, rows000_7_check,
    rows000_8_check, rows000_9_check, rows000_10_check, rows000_11_check, rows000_12_check,
    rows000_13_check, rows000_14_check, rows000_15_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Pairs.Second5
