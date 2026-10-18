module

public import SquaresInCircles.Eight.Generated.OwnerData

/-! Finite owner-pattern completeness and closed tilt-tail coverage.
Owner completeness uses explicit selectors for the varying axes. The
remaining closed interval chains use ordinary `decide`. -/

@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

/-- D is captured geometrically; only the forbidden B direction remains. -/
def QuarterPattern (p : Vertex → Fin 4) : Prop :=
  p 0=0 ∧ p 2=0 ∧ p 4=0 ∧ p 3=0 ∧ p 5=2 ∧ p 1≠2

def MixedPattern (p : Vertex → Fin 4) : Prop :=
  p 0=0 ∧ p 2=0 ∧ p 4=0 ∧ p 3=2 ∧ p 5=2 ∧ (p 1≠0 ∨ p 6≠1)

instance (p : Vertex → Fin 4) : Decidable (QuarterPattern p) := by
  unfold QuarterPattern; infer_instance
instance (p : Vertex → Fin 4) : Decidable (MixedPattern p) := by
  unfold MixedPattern; infer_instance

def quarterByIndex (k : Fin 12) : OwnerTable :=
  quarterTables.get ⟨k.val, by simpa only [quarterTables, List.length_cons, List.length_nil] using k.isLt⟩
def mixedByIndex (k : Fin 15) : OwnerTable :=
  mixedTables.get ⟨k.val, by simpa only [mixedTables, List.length_cons, List.length_nil] using k.isLt⟩

/-- The three surviving G axes, in source-table order. -/
def quarterG : Fin 3 → Fin 4 := ![0,1,3]

def quarterIndex (k : Fin 3) (e : Fin 4) : Fin 12 :=
  ⟨4*k.val+e.val, by omega⟩

theorem quarterByIndex_owners (k : Fin 3) (e : Fin 4) :
    (quarterByIndex (quarterIndex k e)).owners =
      ![0,quarterG k,0,0,0,2,e] := by
  fin_cases k <;> fin_cases e <;> rfl

theorem quarterG_complete (g : Fin 4) (hg : g≠2) :
    ∃ k : Fin 3, quarterG k=g := by
  fin_cases g
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact False.elim (hg rfl)
  · exact ⟨2,rfl⟩

theorem quarter_pattern_complete : ∀ p : Vertex → Fin 4,
    QuarterPattern p → ∃ k : Fin 12, (quarterByIndex k).owners=p := by
  intro p hp
  rcases hp with ⟨h0,h2,h4,h3,h5,hG⟩
  obtain ⟨k,hkg⟩ := quarterG_complete (p 1) hG
  refine ⟨quarterIndex k (p 6), ?_⟩
  rw [quarterByIndex_owners,hkg]
  funext i
  fin_cases i <;> simp [h0,h2,h3,h4,h5]

/-- Row-major order on the mixed-axis pairs, skipping the intended (0,1). -/
def mixedIndex (g e : Fin 4) : Fin 15 :=
  ⟨if 4*g.val+e.val=0 then 0 else 4*g.val+e.val-1, by
    have hg := g.isLt
    have he := e.isLt
    split_ifs <;> omega⟩

theorem mixedByIndex_owners (g e : Fin 4) (hbad : g≠0 ∨ e≠1) :
    (mixedByIndex (mixedIndex g e)).owners = ![0,g,0,2,0,2,e] := by
  fin_cases g <;> fin_cases e <;> first | rfl | (norm_num at hbad)

theorem mixed_pattern_complete : ∀ p : Vertex → Fin 4,
    MixedPattern p → ∃ k : Fin 15, (mixedByIndex k).owners=p := by
  intro p hp
  rcases hp with ⟨h0,h2,h4,h3,h5,hbad⟩
  refine ⟨mixedIndex (p 1) (p 6), ?_⟩
  rw [mixedByIndex_owners _ _ hbad]
  funext i
  fin_cases i <;> simp [h0,h2,h3,h4,h5]

theorem quarterByIndex_mode (k : Fin 12) : (quarterByIndex k).mode=.quarter := by
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

/-- Nonpositive half-angles are excluded by `negative_tilt_excluded`.
Only the two remaining closed positive tails require a bundle. -/
theorem positive_tilt_tail_certificate {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 3/8)
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
