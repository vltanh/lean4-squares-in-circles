module

public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk000
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk001
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk002
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk003
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk004
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk005
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk006
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk007
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk008
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk009
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk010
public import SquaresInCircles.Eight.Generated.Affine.HLowerAffine.Chunk011

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.HLowerAffine
open Arithmetic

def rows : List AffineTableRow := rows000 ++ rows001 ++ rows002 ++ rows003 ++ rows004 ++ rows005 ++ rows006 ++ rows007 ++ rows008 ++ rows009 ++ rows010 ++ rows011
theorem complete_row_count : rows.length = 48050 := by
  simp only [rows,List.length_append,rows000_count,rows001_count,rows002_count,rows003_count,rows004_count,rows005_count,rows006_count,rows007_count,rows008_count,rows009_count,rows010_count,rows011_count]
  norm_num

end SquaresInCircles.Eight.Generated.Affine.HLowerAffine
