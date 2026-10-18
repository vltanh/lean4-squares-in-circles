module

public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof000
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof001
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof002
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof003
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof004
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof005
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof006
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof007
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof008
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof009
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof010
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof011
public import SquaresInCircles.Eight.Generated.Affine.TLowerAffine.Proof012

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.TLowerAffine
open Arithmetic

/-- Every supplied original row has the full continuous semantic Claim. -/
theorem all_row_claims : ∀ r ∈ rows, r.Claim meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact rows000_claims r h0
  · exact rows001_claims r h1
  · exact rows002_claims r h2
  · exact rows003_claims r h3
  · exact rows004_claims r h4
  · exact rows005_claims r h5
  · exact rows006_claims r h6
  · exact rows007_claims r h7
  · exact rows008_claims r h8
  · exact rows009_claims r h9
  · exact rows010_claims r h10
  · exact rows011_claims r h11
  · exact rows012_claims r h12

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact rows000_structural r h0
  · exact rows001_structural r h1
  · exact rows002_structural r h2
  · exact rows003_structural r h3
  · exact rows004_structural r h4
  · exact rows005_structural r h5
  · exact rows006_structural r h6
  · exact rows007_structural r h7
  · exact rows008_structural r h8
  · exact rows009_structural r h9
  · exact rows010_structural r h10
  · exact rows011_structural r h11
  · exact rows012_structural r h12

end SquaresInCircles.Eight.Generated.Affine.TLowerAffine
