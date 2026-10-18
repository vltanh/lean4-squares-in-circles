module

public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof000
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof001
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof002
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof003
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof004
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof005
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof006
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof007
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof008
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof009
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof010
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof011
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof012
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof013
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof014
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof015
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof016
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof017
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof018
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof019
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof020
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof021
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof022
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof023
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof024
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof025
public import SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.Proof026

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
open Arithmetic

/-- Every supplied original row has the full continuous semantic Claim. -/
theorem all_row_claims : ∀ r ∈ rows, r.Claim meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26
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

theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta := by
  intro r hr
  simp only [rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26
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

end SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine
