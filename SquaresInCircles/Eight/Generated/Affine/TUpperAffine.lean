module

public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Chunk000
public import SquaresInCircles.Eight.Generated.Affine.TUpperAffine.Chunk001

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.TUpperAffine
open Arithmetic

def rows : List AffineTableRow := rows000 ++ rows001
theorem complete_row_count : rows.length = 7078 := by
  simp only [rows,List.length_append,rows000_count,rows001_count]
  norm_num

end SquaresInCircles.Eight.Generated.Affine.TUpperAffine
