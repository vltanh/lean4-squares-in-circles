module

public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Proof000
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Proof001
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Proof002
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Proof003
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Proof004
public import SquaresInCircles.Eight.Generated.Affine.DUpperAffine.Proof005

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.DUpperAffine
open Arithmetic

/-- Every supplied original row has the full continuous semantic Claim. -/
theorem all_row_claims : ∀ r ∈ rows, r.Claim meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5
  · exact rows000_claims r h0
  · exact rows001_claims r h1
  · exact rows002_claims r h2
  · exact rows003_claims r h3
  · exact rows004_claims r h4
  · exact rows005_claims r h5

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5
  · exact rows000_structural r h0
  · exact rows001_structural r h1
  · exact rows002_structural r h2
  · exact rows003_structural r h3
  · exact rows004_structural r h4
  · exact rows005_structural r h5

end SquaresInCircles.Eight.Generated.Affine.DUpperAffine
