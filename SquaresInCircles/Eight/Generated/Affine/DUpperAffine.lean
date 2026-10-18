module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Chunk000
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Chunk001
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Chunk002
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Chunk003
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Chunk004
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Chunk005

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

def rows : List AffineTableRow := rows000 ++ rows001 ++ rows002 ++ rows003 ++ rows004 ++ rows005
theorem complete_row_count : rows.length = 24197 := by
  simp only [rows,List.length_append,rows000_count,rows001_count,rows002_count,rows003_count,rows004_count,rows005_count]
  norm_num

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
