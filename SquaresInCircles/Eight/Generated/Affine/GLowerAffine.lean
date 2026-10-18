module

public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Chunk000
public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Chunk001
public import SquaresInCircles.Eight.Generated.Affine.GLowerAffine.Chunk002

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.GLowerAffine
open Arithmetic

def rows : List AffineTableRow := rows000 ++ rows001 ++ rows002
theorem complete_row_count : rows.length = 9087 := by
  simp only [rows,List.length_append,rows000_count,rows001_count,rows002_count]
  norm_num

end SquaresInCircles.Eight.Generated.Affine.GLowerAffine
