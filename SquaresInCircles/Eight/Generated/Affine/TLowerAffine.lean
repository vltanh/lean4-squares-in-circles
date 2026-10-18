module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk000
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk001
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk002
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk003
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk004
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk005
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk006
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk007
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk008
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk009
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk010
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk011
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Chunk012

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

def rows : List AffineTableRow := rows000 ++ rows001 ++ rows002 ++ rows003 ++ rows004 ++ rows005 ++ rows006 ++ rows007 ++ rows008 ++ rows009 ++ rows010 ++ rows011 ++ rows012
theorem complete_row_count : rows.length = 49971 := by
  simp only [rows,List.length_append,rows000_count,rows001_count,rows002_count,rows003_count,rows004_count,rows005_count,rows006_count,rows007_count,rows008_count,rows009_count,rows010_count,rows011_count,rows012_count]
  norm_num

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
