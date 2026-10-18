module

public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine
public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Proof000
public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Proof001
public import SquaresInCircles.Eight.Generated.Affine.GUpperAffine.Proof002

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.GUpperAffine
open Arithmetic

/-- Every supplied original row has the full continuous semantic Claim. -/
theorem all_row_claims : ∀ r ∈ rows, r.Claim meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2
  · exact rows000_claims r h0
  · exact rows001_claims r h1
  · exact rows002_claims r h2

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2
  · exact rows000_structural r h0
  · exact rows001_structural r h1
  · exact rows002_structural r h2

end SquaresInCircles.Eight.Generated.Affine.GUpperAffine
