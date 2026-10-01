import SquaresInCircles.Six.Analytic.SecondaryTransverseSigns
import SquaresInCircles.Six.Analytic.SouthTransverseBudget
import SquaresInCircles.Six.Analytic.CoupledWingBudget
import SquaresInCircles.Six.Analytic.FixedDiagonalWork

/-!
# Exact logical frontier of the candidate-edge reduction

A pair can admit more than one separating axis. Therefore a noncandidate
selected index is not itself a missing candidate edge. The cases below retain
the FAILURE of the corresponding wing inequality, and then derive a genuine
D-sourced inequality from full secondary selection. The double-D exclusion
forces the opposite wing. This avoids discarding configurations at source ties.

The two mixed cases remain to be excluded by substantive analytic inequalities.
This module states their exact geometric content and proves the exhaustive
reduction; it supplies neither exclusion as an assumption on Packing.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- W/D can separate only through D when its candidate wing inequality fails. -/
structure MissingWestWing {R : ℝ} (P : NormalizedPacking R) : Prop where
  not_west : ¬ Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)
  from_diagonal : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)
  south_wing : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

/-- D/S can separate only through D when its candidate wing inequality fails. -/
structure MissingSouthWing {R : ℝ} (P : NormalizedPacking R) : Prop where
  west_wing : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)
  from_diagonal : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)
  not_south : ¬ Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

/-- A failure of the west wing forces precisely the mixed source case (6,6).
This is the source combination in the historical 53-cell hard table. -/
lemma missing_west_of_failure {R : ℝ} (P : NormalizedPacking R)
    (hW : ¬ Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)) :
    MissingWestWing P := by
  obtain ⟨k,hk,hchoice⟩ := DW_secondary_exists P
  have hD : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center) := by
    rcases hchoice with rfl | rfl
    · exact False.elim (hW hk)
    · exact hk
  have hS : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center) := by
    rcases south_secondary_choice P with h | h
    · exact False.elim (double_Dsecondary_impossible P hD h)
    · exact h
  exact ⟨hW,hD,hS⟩

/-- A failure of the south wing forces the other mixed source case (2,2). -/
lemma missing_south_of_failure {R : ℝ} (P : NormalizedPacking R)
    (hS : ¬ Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)) :
    MissingSouthWing P := by
  have hD : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center) := by
    rcases south_secondary_choice P with h | h
    · exact h
    · exact False.elim (hS h)
  obtain ⟨k,hk,hchoice⟩ := DW_secondary_exists P
  have hW : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) := by
    rcases hchoice with rfl | rfl
    · exact hk
    · exact False.elim (double_Dsecondary_impossible P hk hD)
  exact ⟨hW,hD,hS⟩

/-- The actual normalized packing falls into exactly the intended logical
frontier: both candidate inequalities, or one of the two missing-wing cases. -/
theorem candidate_or_missing_wing {R : ℝ} (P : NormalizedPacking R) :
    FixedPair.CandidateDSeparators P ∨ MissingWestWing P ∨ MissingSouthWing P := by
  by_cases hW : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)
  · by_cases hS : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
        dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)
    · exact Or.inl ⟨hW,hS⟩
    · exact Or.inr (Or.inr (missing_south_of_failure P hS))
  · exact Or.inr (Or.inl (missing_west_of_failure P hW))

lemma MissingWestWing.phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.helperAngle 2 < P.diagonalAngle-Real.pi/4 :=
  DW_Dsecondary_west_of_wall P h.from_diagonal

lemma MissingSouthWing.phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) : P.diagonalAngle-Real.pi/4 < P.helperAngle 4 :=
  DS_Dsecondary_south_of_wall P h.from_diagonal

lemma MissingWestWing.cardinal_wedge {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) (hcard : P.ownBits 2=false) :
    P.helperAngle 2 < P.diagonalAngle-Real.pi/4 ∧
      P.diagonalAngle-Real.pi/4 < P.helperAngle 4 :=
  cardinal_W_non_candidate_phase_wedge P hcard h.from_diagonal

/-- At this interface, eliminating the two missing-wing cases is exactly the
candidate-edge obligation. The equivalence is not a proof of either exclusion. -/
theorem candidate_edges_iff_no_missing_wing {R : ℝ} (P : NormalizedPacking R) :
    FixedPair.CandidateDSeparators P ↔ (¬ MissingWestWing P ∧ ¬ MissingSouthWing P) := by
  constructor
  · intro h
    exact ⟨fun hW => hW.not_west h.1,fun hS => hS.not_south h.2⟩
  · rintro ⟨hW,hS⟩
    rcases candidate_or_missing_wing P with h | h | h
    · exact h
    · exact False.elim (hW h)
    · exact False.elim (hS h)

end SquaresInCircles.Six.Analytic
