module

public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Cover
public import SquaresInCircles.Eight.Candidate.Mismatch

/-! The coarse table with its retained per-edge reserves. Uncompiled.
All expressions, state data, row intervals, and closed covers are shared. -/

@[expose] public section
namespace SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Enhanced
open Arithmetic

def reserve : Vertex→ℚ := ![15/1000000,13/1000000,18/1000000,12/1000000,
  15/1000000,23/1000000,6/1000000]
def meta : AffineTableMeta := {SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta with
  target:=fun i => SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta.target i+reserve i}
def upgrade (r : AffineTableRow) : AffineTableRow :=
  {r with lowerTarget:=r.lowerTarget+reserve r.edge}
def upgradeProof (p : PreparedRow) : PreparedRow := {p with row:=upgrade p.row}
def rows : List AffineTableRow := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows.map upgrade

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows000_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows000.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow000 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow000 i)).Matches meta := by
  decide

theorem rowClaims000 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows000, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows000_numeric i).1 (proofRows000_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows001_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows001.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow001 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow001 i)).Matches meta := by
  decide

theorem rowClaims001 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows001, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows001_numeric i).1 (proofRows001_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows002_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows002.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow002 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow002 i)).Matches meta := by
  decide

theorem rowClaims002 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows002, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows002_numeric i).1 (proofRows002_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows003_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows003.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow003 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow003 i)).Matches meta := by
  decide

theorem rowClaims003 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows003, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows003_numeric i).1 (proofRows003_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows004_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows004.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow004 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow004 i)).Matches meta := by
  decide

theorem rowClaims004 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows004, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows004_numeric i).1 (proofRows004_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows005_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows005.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow005 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow005 i)).Matches meta := by
  decide

theorem rowClaims005 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows005, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows005_numeric i).1 (proofRows005_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows006_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows006.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow006 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow006 i)).Matches meta := by
  decide

theorem rowClaims006 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows006, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows006_numeric i).1 (proofRows006_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows007_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows007.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow007 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow007 i)).Matches meta := by
  decide

theorem rowClaims007 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows007, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows007_numeric i).1 (proofRows007_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows008_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows008.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow008 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow008 i)).Matches meta := by
  decide

theorem rowClaims008 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows008, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows008_numeric i).1 (proofRows008_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows009_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows009.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow009 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow009 i)).Matches meta := by
  decide

theorem rowClaims009 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows009, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows009_numeric i).1 (proofRows009_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows010_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows010.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow010 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow010 i)).Matches meta := by
  decide

theorem rowClaims010 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows010, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows010_numeric i).1 (proofRows010_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows011_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows011.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow011 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow011 i)).Matches meta := by
  decide

theorem rowClaims011 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows011, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows011_numeric i).1 (proofRows011_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows012_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows012.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow012 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow012 i)).Matches meta := by
  decide

theorem rowClaims012 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows012, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows012_numeric i).1 (proofRows012_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows013_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows013.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow013 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow013 i)).Matches meta := by
  decide

theorem rowClaims013 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows013, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows013_numeric i).1 (proofRows013_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows014_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows014.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow014 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow014 i)).Matches meta := by
  decide

theorem rowClaims014 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows014, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows014_numeric i).1 (proofRows014_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows015_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows015.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow015 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow015 i)).Matches meta := by
  decide

theorem rowClaims015 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows015, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows015_numeric i).1 (proofRows015_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows016_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows016.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow016 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow016 i)).Matches meta := by
  decide

theorem rowClaims016 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows016, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows016_numeric i).1 (proofRows016_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows017_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows017.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow017 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow017 i)).Matches meta := by
  decide

theorem rowClaims017 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows017, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows017_numeric i).1 (proofRows017_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows018_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows018.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow018 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow018 i)).Matches meta := by
  decide

theorem rowClaims018 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows018, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows018_numeric i).1 (proofRows018_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows019_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows019.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow019 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow019 i)).Matches meta := by
  decide

theorem rowClaims019 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows019, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows019_numeric i).1 (proofRows019_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows020_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows020.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow020 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow020 i)).Matches meta := by
  decide

theorem rowClaims020 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows020, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows020_numeric i).1 (proofRows020_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows021_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows021.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow021 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow021 i)).Matches meta := by
  decide

theorem rowClaims021 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows021, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows021_numeric i).1 (proofRows021_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows022_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows022.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow022 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow022 i)).Matches meta := by
  decide

theorem rowClaims022 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows022, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows022_numeric i).1 (proofRows022_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows023_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows023.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow023 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow023 i)).Matches meta := by
  decide

theorem rowClaims023 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows023, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows023_numeric i).1 (proofRows023_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows024_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows024.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow024 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow024 i)).Matches meta := by
  decide

theorem rowClaims024 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows024, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows024_numeric i).1 (proofRows024_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows025_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows025.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow025 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow025 i)).Matches meta := by
  decide

theorem rowClaims025 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows025, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows025_numeric i).1 (proofRows025_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows026_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows026.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow026 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow026 i)).Matches meta := by
  decide

theorem rowClaims026 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows026, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows026_numeric i).1 (proofRows026_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows027_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows027.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow027 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow027 i)).Matches meta := by
  decide

theorem rowClaims027 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows027, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows027_numeric i).1 (proofRows027_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows028_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows028.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow028 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow028 i)).Matches meta := by
  decide

theorem rowClaims028 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows028, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows028_numeric i).1 (proofRows028_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows029_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows029.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow029 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow029 i)).Matches meta := by
  decide

theorem rowClaims029 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows029, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows029_numeric i).1 (proofRows029_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows030_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows030.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow030 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow030 i)).Matches meta := by
  decide

theorem rowClaims030 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows030, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows030_numeric i).1 (proofRows030_numeric i).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem proofRows031_numeric : ∀ i : Fin SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows031.length,
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow031 i)).NumericValid ∧
    (upgradeProof (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.proofRow031 i)).Matches meta := by
  decide

theorem rowClaims031 : ∀ r∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows031, (upgrade r).Claim meta := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  exact PreparedRow.claim (proofRows031_numeric i).1 (proofRows031_numeric i).2

theorem all_row_claims : ∀ r∈rows, r.Claim meta := by
  intro r hr
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
  simp only [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.rows,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · exact rowClaims000 r h0
  · exact rowClaims001 r h1
  · exact rowClaims002 r h2
  · exact rowClaims003 r h3
  · exact rowClaims004 r h4
  · exact rowClaims005 r h5
  · exact rowClaims006 r h6
  · exact rowClaims007 r h7
  · exact rowClaims008 r h8
  · exact rowClaims009 r h9
  · exact rowClaims010 r h10
  · exact rowClaims011 r h11
  · exact rowClaims012 r h12
  · exact rowClaims013 r h13
  · exact rowClaims014 r h14
  · exact rowClaims015 r h15
  · exact rowClaims016 r h16
  · exact rowClaims017 r h17
  · exact rowClaims018 r h18
  · exact rowClaims019 r h19
  · exact rowClaims020 r h20
  · exact rowClaims021 r h21
  · exact rowClaims022 r h22
  · exact rowClaims023 r h23
  · exact rowClaims024 r h24
  · exact rowClaims025 r h25
  · exact rowClaims026 r h26
  · exact rowClaims027 r h27
  · exact rowClaims028 r h28
  · exact rowClaims029 r h29
  · exact rowClaims030 r h30
  · exact rowClaims031 r h31

def cover : AffineCover := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.cover

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover_numeric : cover.NumericValid meta rows := by
  decide

noncomputable def charged_bound (C : BoundaryCycle (meta.radius:ℝ))
    (F : Candidate.Frame C)
    (hcuts : ∀ i, (meta.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (meta.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈meta.allowedAxes i) :
    Candidate.ChargedBound C F Candidate.coarseBeta Candidate.enhancedGamma := by
  have hw : ∀ i, (meta.word i:ℝ)=(Candidate.word i:ℝ) := by
    intro i; fin_cases i <;> norm_num [meta,SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,Candidate.word]
  have hb : ∀ i, (meta.charge i:ℝ)=Candidate.charge Candidate.coarseBeta i := by
    intro i; fin_cases i <;> norm_num [meta,SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,Candidate.charge,Candidate.charged,Candidate.coarseBeta]
  have P := cover.chargedBound cover_numeric all_row_claims C F Candidate.coarseBeta hw hb hcuts hdiff haxes
  simpa [meta,SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.meta,reserve,Candidate.enhancedGamma,Candidate.coarseGamma,Candidate.retainedReserve] using P

end SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Enhanced
