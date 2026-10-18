module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Chunk000
public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Chunk001
public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Chunk002

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

def rows : List AffineTableRow := rows000 ++ rows001 ++ rows002
theorem complete_row_count : rows.length = 9796 := by
  simp only [rows,List.length_append,rows000_count,rows001_count,rows002_count]
  norm_num

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
