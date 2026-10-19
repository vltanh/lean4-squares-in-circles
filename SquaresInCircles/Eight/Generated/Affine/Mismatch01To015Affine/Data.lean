module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows000
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows001
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows002
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows003
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows004
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows005
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows006
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows007
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Rows008

/-! All rows of the table. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

set_option maxRecDepth 100000

/-- The rows in parts of 200, in natural numbers, sorted by source, target, axis and half. -/
noncomputable def chunks : List (List AffineRow) :=
  parts000 ++ (parts001 ++ (parts002 ++ (parts003 ++ (parts004 ++ (parts005 ++ (parts006 ++
  (parts007 ++ parts008)))))))

/-- All rows. -/
noncomputable def data : List AffineRow := chunks.flatten

theorem data_check : checkRows ctx data = true := by
  simp only [data, chunks, checkRows_flatten, List.all_append, parts000_check, parts001_check,
    parts002_check, parts003_check, parts004_check, parts005_check, parts006_check, parts007_check,
    parts008_check, Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
