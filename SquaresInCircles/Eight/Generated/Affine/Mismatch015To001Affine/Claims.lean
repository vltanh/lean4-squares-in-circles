module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof000
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof001
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof002
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof003
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof004
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof005
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof006
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof007
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof008
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof009
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof010
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof011
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof012
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof013
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof014
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof015
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof016
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof017
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof018
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof019
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof020
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof021
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof022
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof023
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof024
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof025
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof026
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof027
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof028
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof029
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof030
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof031
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof032
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof033
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof034
public import SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.Proof035

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
open Arithmetic

/-- Every supplied original row has the full continuous semantic Claim. -/
theorem all_row_claims : ∀ r ∈ rows, r.Claim meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35
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
  · exact rows013_claims r h13
  · exact rows014_claims r h14
  · exact rows015_claims r h15
  · exact rows016_claims r h16
  · exact rows017_claims r h17
  · exact rows018_claims r h18
  · exact rows019_claims r h19
  · exact rows020_claims r h20
  · exact rows021_claims r h21
  · exact rows022_claims r h22
  · exact rows023_claims r h23
  · exact rows024_claims r h24
  · exact rows025_claims r h25
  · exact rows026_claims r h26
  · exact rows027_claims r h27
  · exact rows028_claims r h28
  · exact rows029_claims r h29
  · exact rows030_claims r h30
  · exact rows031_claims r h31
  · exact rows032_claims r h32
  · exact rows033_claims r h33
  · exact rows034_claims r h34
  · exact rows035_claims r h35

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35
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
  · exact rows013_structural r h13
  · exact rows014_structural r h14
  · exact rows015_structural r h15
  · exact rows016_structural r h16
  · exact rows017_structural r h17
  · exact rows018_structural r h18
  · exact rows019_structural r h19
  · exact rows020_structural r h20
  · exact rows021_structural r h21
  · exact rows022_structural r h22
  · exact rows023_structural r h23
  · exact rows024_structural r h24
  · exact rows025_structural r h25
  · exact rows026_structural r h26
  · exact rows027_structural r h27
  · exact rows028_structural r h28
  · exact rows029_structural r h29
  · exact rows030_structural r h30
  · exact rows031_structural r h31
  · exact rows032_structural r h32
  · exact rows033_structural r h33
  · exact rows034_structural r h34
  · exact rows035_structural r h35

end SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine
