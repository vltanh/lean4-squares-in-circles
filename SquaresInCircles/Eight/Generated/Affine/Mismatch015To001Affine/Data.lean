module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows000
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows001
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows002
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows003
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows004
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows005
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows006
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows007
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows008
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows009
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows010
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows011
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows012
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Rows013

/-!
# Eight squares: the rows of the affine table `Mismatch015To001Affine`

All rows of the table, as the list of their parts; together they pass `checkRows`.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

set_option maxRecDepth 100000

/-- The rows in parts of 200, in natural numbers, sorted by source, target, axis and half. -/
noncomputable def chunks : List (List AffineRow) :=
  parts000 ++ (parts001 ++ (parts002 ++ (parts003 ++ (parts004 ++ (parts005 ++ (parts006 ++
  (parts007 ++ (parts008 ++ (parts009 ++ (parts010 ++ (parts011 ++ (parts012 ++
  parts013))))))))))))

/-- All rows. -/
noncomputable def data : List AffineRow := chunks.flatten

theorem data_check : checkRows ctx data = true := by
  simp only [data, chunks, checkRows_flatten, List.all_append, parts000_check, parts001_check,
    parts002_check, parts003_check, parts004_check, parts005_check, parts006_check, parts007_check,
    parts008_check, parts009_check, parts010_check, parts011_check, parts012_check, parts013_check,
    Bool.and_true]

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
