import SquaresInCircles.Six.Normalization.StrongCardinal

/-!
# Canonical five-bit patterns

The numbering is the manuscript's E+2N+4W+8D+16S, with true meaning OWN.
The partition below is an exhaustive finite identity, not an assumed A2
classification. Its geometric input is only the already proved D-own bit.
No case is discarded by this module.
-/

namespace SquaresInCircles.Six

abbrev CentralPattern := Fin 5 → Bool

namespace CentralPattern

def code (p : CentralPattern) : ℕ :=
  (if p 0 then 1 else 0) + (if p 1 then 2 else 0) +
  (if p 2 then 4 else 0) + (if p 3 then 8 else 0) +
  (if p 4 then 16 else 0)

def allCardinalExceptD : CentralPattern := ![false,false,false,true,false]

def forbidden : Finset ℕ := {10,12,13,14,26,28,29,30,31}
def noncandidateSurvivors : Finset ℕ := {9,11,15,24,25,27}
def admissibleCodes : Finset ℕ := {8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31}

lemma code_lt (p : CentralPattern) : p.code < 32 := by
  have h : ∀ q : CentralPattern, q.code < 32 := by decide
  exact h p

lemma code_injective : Function.Injective code := by
  have h : ∀ p q : CentralPattern, code p = code q → p = q := by decide
  exact h

@[simp] lemma code_candidate : code allCardinalExceptD = 8 := by decide

lemma code_eq_eight_iff (p : CentralPattern) : p.code = 8 ↔ p = allCardinalExceptD := by
  constructor
  · intro h
    apply code_injective
    simpa only [code_candidate] using h
  · rintro rfl
    exact code_candidate

lemma code_mem_of_D_own (p : CentralPattern) (hD : p 3 = true) : p.code ∈ admissibleCodes := by
  have h : ∀ q : CentralPattern, q 3 = true → q.code ∈ admissibleCodes := by decide
  exact h p hD

/-- All sixteen possible codes are retained until a concrete elimination is proved. -/
theorem exhaustive_partition (p : CentralPattern) (hD : p 3 = true) :
    p.code = 8 ∨ p.code ∈ forbidden ∨ p.code ∈ noncandidateSurvivors := by
  have h : ∀ q : CentralPattern, q 3 = true →
      q.code = 8 ∨ q.code ∈ forbidden ∨ q.code ∈ noncandidateSurvivors := by decide
  exact h p hD

lemma disjoint_parts : Disjoint forbidden noncandidateSurvivors := by decide
lemma candidate_not_forbidden : 8 ∉ forbidden := by decide
lemma candidate_not_survivor : 8 ∉ noncandidateSurvivors := by decide

/-- The C/W/D/S data are independent of the E and N bits. -/
def sameWDS (p q : CentralPattern) : Prop := p 2=q 2 ∧ p 3=q 3 ∧ p 4=q 4

lemma sameWDS_iff (p q : CentralPattern) : sameWDS p q ↔
    ∀ i : Fin 5, i=2 ∨ i=3 ∨ i=4 → p i=q i := by
  constructor
  · rintro ⟨hW,hD,hS⟩ i (rfl | rfl | rfl)
    · exact hW
    · exact hD
    · exact hS
  · intro h
    exact ⟨h 2 (Or.inl rfl),h 3 (Or.inr (Or.inl rfl)),h 4 (Or.inr (Or.inr rfl))⟩

/-- Every forbidden case except 10 contains an OWN W or S. This is only bit
bookkeeping; the argument forcing a zero angle is supplied by the case closure. -/
lemma forbidden_own_west_or_south (p : CentralPattern)
    (h : p.code ∈ forbidden) (h10 : p.code ≠ 10) : p 2=true ∨ p 4=true := by
  have all : ∀ q : CentralPattern, q.code ∈ forbidden → q.code ≠ 10 →
      q 2=true ∨ q 4=true := by decide
  exact all p h h10

lemma code_ten_north_own (p : CentralPattern) (h : p.code=10) : p 1=true := by
  have all : ∀ q : CentralPattern, q.code=10 → q 1=true := by decide
  exact all p h

lemma survivor_own_bits (p : CentralPattern) :
    (p.code=9 → p 0=true) ∧ (p.code=11 → p 0=true) ∧
    (p.code=15 → p 2=true) ∧ (p.code=24 → p 4=true) ∧
    (p.code=25 → p 4=true) ∧ (p.code=27 → p 4=true) := by
  have all : ∀ q : CentralPattern,
      (q.code=9 → q 0=true) ∧ (q.code=11 → q 0=true) ∧
      (q.code=15 → q 2=true) ∧ (q.code=24 → q 4=true) ∧
      (q.code=25 → q 4=true) ∧ (q.code=27 → q 4=true) := by decide
  exact all p

end CentralPattern

noncomputable section
namespace Normalization.NormalizedPacking
variable {R : ℝ} (P : NormalizedPacking R)

def patternCode : ℕ := CentralPattern.code P.ownBits

lemma pattern_inventory : P.patternCode ∈ CentralPattern.admissibleCodes :=
  CentralPattern.code_mem_of_D_own P.ownBits P.diagonal_own

lemma pattern_partition : P.patternCode=8 ∨ P.patternCode ∈ CentralPattern.forbidden ∨
    P.patternCode ∈ CentralPattern.noncandidateSurvivors :=
  CentralPattern.exhaustive_partition P.ownBits P.diagonal_own

lemma candidate_bits (h : P.patternCode=8) : P.ownBits=CentralPattern.allCardinalExceptD :=
  (CentralPattern.code_eq_eight_iff P.ownBits).mp h

end Normalization.NormalizedPacking
end SquaresInCircles.Six
