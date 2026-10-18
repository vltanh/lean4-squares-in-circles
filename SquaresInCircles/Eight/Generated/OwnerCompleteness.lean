module

public import SquaresInCircles.Eight.Generated.OwnerData

/-! Finite owner-pattern completeness and closed tilt-tail coverage.
These predicates enumerate concrete four-owner functions; they contain no
geometric exclusion conclusion. Ordinary `decide` is left for Lean to check. -/

@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

def QuarterPattern (p : Vertex → Fin 4) : Prop :=
  p 0=0 ∧ p 2=0 ∧ p 4=0 ∧ (p 3=0 ∨ p 3=2) ∧
    (p 5=0 ∨ p 5=2) ∧ (p 3=0 ∨ p 5=0)

def MixedPattern (p : Vertex → Fin 4) : Prop :=
  p 0=0 ∧ p 2=0 ∧ p 4=0 ∧ p 3=2 ∧ p 5=2 ∧ (p 1≠0 ∨ p 6≠1)

instance (p : Vertex → Fin 4) : Decidable (QuarterPattern p) := by
  unfold QuarterPattern; infer_instance
instance (p : Vertex → Fin 4) : Decidable (MixedPattern p) := by
  unfold MixedPattern; infer_instance

def quarterByIndex (k : Fin 48) : OwnerTable :=
  quarterTables.get ⟨k.val, by simpa only [quarterTables, List.length_cons, List.length_nil] using k.isLt⟩
def mixedByIndex (k : Fin 15) : OwnerTable :=
  mixedTables.get ⟨k.val, by simpa only [mixedTables, List.length_cons, List.length_nil] using k.isLt⟩

theorem quarter_pattern_complete : ∀ p : Vertex → Fin 4,
    QuarterPattern p → ∃ k : Fin 48, (quarterByIndex k).owners=p := by decide

theorem mixed_pattern_complete : ∀ p : Vertex → Fin 4,
    MixedPattern p → ∃ k : Fin 15, (mixedByIndex k).owners=p := by decide

theorem quarterByIndex_mode (k : Fin 48) : (quarterByIndex k).mode=.quarter := by
  fin_cases k <;> rfl
theorem mixedByIndex_mode (k : Fin 15) : (mixedByIndex k).mode=.mixed := by
  fin_cases k <;> rfl

theorem quarter_certificate {p : Vertex → Fin 4} (hp : QuarterPattern p) :
    ∃ T : OwnerTable, T.mode=.quarter ∧ T.owners=p := by
  obtain ⟨k,hk⟩ := quarter_pattern_complete p hp
  exact ⟨quarterByIndex k,quarterByIndex_mode k,hk⟩

theorem mixed_certificate {p : Vertex → Fin 4} (hp : MixedPattern p) :
    ∃ T : OwnerTable, T.mode=.mixed ∧ T.owners=p := by
  obtain ⟨k,hk⟩ := mixed_pattern_complete p hp
  exact ⟨mixedByIndex k,mixedByIndex_mode k,hk⟩

theorem tilt_tail_certificate {z : ℝ} (hz : -(3/8:ℝ) ≤ z ∧ z ≤ 3/8)
    (htail : z ≤ 1001/20000 ∨ 2/25 ≤ z) :
    ∃ B : TiltBundle, B.interval.Mem z := by
  rcases htail with hl | hr
  · obtain ⟨I,hI,hIz⟩ := tilt_left_cover.covers (x := z) ⟨hz.1,hl⟩
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hI
    exact ⟨B,hIz⟩
  · obtain ⟨I,hI,hIz⟩ := tilt_right_cover.covers (x := z) ⟨hr,hz.2⟩
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hI
    exact ⟨B,hIz⟩

end SquaresInCircles.Eight.Generated.Owner
