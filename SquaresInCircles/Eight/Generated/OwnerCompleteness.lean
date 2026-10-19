module

public import SquaresInCircles.Eight.Generated.OwnerData

/-!
# Eight squares: completeness of the owner tables

Every owner pattern of the mixed mode (`MixedPattern`) is the pattern of one of the 7 mixed tables.
A pattern is determined by its owners at `G` and `E`, so this is a finite test over these values,
evaluated by the kernel. The tilt bundles cover both tails of the positive half-angle chart.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 1000000
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

/-- The intended axes of `B` and `D`, the `E` axis `0` or `1`, and owners other than `0` at `G`
and `1` at `E`; the `E` axes `2` and `3` are excluded geometrically in `mixed_E_owners`. -/
def MixedPattern (p : Vertex → Fin 4) : Prop :=
  p 0=0 ∧ p 2=0 ∧ p 4=0 ∧ p 3=2 ∧ p 5=2 ∧ p 6<2 ∧ (p 1≠0 ∨ p 6≠1)

def mixedByIndex (k : Fin 7) : OwnerTable :=
  mixedTables.get ⟨k.val, by simpa only [mixedTables, List.length_cons, List.length_nil] using k.isLt⟩

/-- The owners `g`, `b`, `d`, `e` at `G`, `B`, `D`, `E`, and `0` at `H`, `A`, `T`. -/
def ownersOf (g b d e : Fin 4) : Vertex → Fin 4 := ![0, g, 0, b, 0, d, e]

theorem eq_ownersOf {p : Vertex → Fin 4} (h0 : p 0 = 0) (h2 : p 2 = 0) (h4 : p 4 = 0) :
    p = ownersOf (p 1) (p 3) (p 5) (p 6) := by
  funext i
  fin_cases i <;> simp [ownersOf, h0, h2, h4]

/-- `f = g`, as a Boolean. -/
def ownersEq (f g : Vertex → Fin 4) : Bool := all7 fun i => f i == g i

theorem ownersEq_spec {f g : Vertex → Fin 4} (h : ownersEq f g = true) : f = g :=
  funext fun i => by simpa [ownersEq, all7_eq_true] using all7_eq_true.1 h i

theorem mixed_tables_cover : ((List.finRange 4).all fun g => ([0, 1] : List (Fin 4)).all fun e =>
    (g == 0 && e == 1) ||
      (List.finRange 7).any fun k => ownersEq (mixedByIndex k).owners (ownersOf g 2 2 e))
    = true := by
  decide +kernel

theorem mixed_pattern_complete : ∀ p : Vertex → Fin 4,
    MixedPattern p → ∃ k : Fin 7, (mixedByIndex k).owners=p := by
  rintro p ⟨h0, h2, h4, h3, h5, h6, h16⟩
  have he : p 6 ∈ ([0, 1] : List (Fin 4)) := by
    revert h6
    generalize p 6 = a
    fin_cases a <;> decide
  have h := List.all_eq_true.1 (List.all_eq_true.1 mixed_tables_cover
    (p 1) (List.mem_finRange _)) (p 6) he
  have hne : (p 1 == 0 && p 6 == 1) = false := by
    rcases h16 with h | h <;> simp [h]
  rw [hne, Bool.false_or] at h
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 h
  have hp := eq_ownersOf h0 h2 h4
  rw [h3, h5] at hp
  exact ⟨k, (ownersEq_spec hk).trans hp.symm⟩

theorem mixedByIndex_mode (k : Fin 7) : (mixedByIndex k).mode=.mixed := by
  fin_cases k <;> rfl

theorem mixed_certificate {p : Vertex → Fin 4} (hp : MixedPattern p) :
    ∃ T : OwnerTable, T.mode=.mixed ∧ T.owners=p := by
  obtain ⟨k,hk⟩ := mixed_pattern_complete p hp
  exact ⟨mixedByIndex k,mixedByIndex_mode k,hk⟩

/-- The nonpositive half-angles are excluded by `negative_tilt_excluded`; the bundles cover the
two closed tails of the positive half-chart. -/
theorem positive_tilt_tail_certificate {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 3/8)
    (htail : z ≤ 1001/20000 ∨ 2/25 ≤ z) :
    ∃ B : TiltBundle, B.interval.Mem z := by
  rcases htail with hl | hr
  · have hmem : Arithmetic.QInterval.Mem ⟨0, 1001/20000⟩ z := by
      unfold Arithmetic.QInterval.Mem
      push_cast
      exact ⟨hz.1, hl⟩
    obtain ⟨I,hI,hIz⟩ := tilt_left_cover.covers hmem
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hI
    exact ⟨B,hIz⟩
  · have hmem : Arithmetic.QInterval.Mem ⟨2/25, 3/8⟩ z := by
      unfold Arithmetic.QInterval.Mem
      push_cast
      constructor <;> linarith [hz.2]
    obtain ⟨I,hI,hIz⟩ := tilt_right_cover.covers hmem
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hI
    exact ⟨B,hIz⟩

end SquaresInCircles.Eight.Generated.Owner
