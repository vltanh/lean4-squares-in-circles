import SquaresInCircles.Six.Analytic.SecondaryPhaseRestrictions
import SquaresInCircles.Six.Analytic.SouthTransverseBudget
import SquaresInCircles.Six.Analytic.CoupledWingBudget
import SquaresInCircles.Six.Analytic.FixedDiagonalWork

/-!
# Missing wings

In the model W and D are separated along the secondary axis of W, and D and S
along the secondary axis of S: these are the two wings. Each of the two pairs
is separated along the secondary axis of one of its squares, and not both
along that of D. So if W and D are not separated along the secondary axis of
W, they are separated along that of D, and D and S along that of S: the west
wing is missing. The same holds with W and S exchanged. `MissingWestWing` and
`MissingSouthWing` keep the failed separation as a hypothesis, and a missing
wing puts the angle of W or S beyond the wall `d - π/4`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- The west wing is missing: W and D are separated along the secondary axis of
D but not along that of W, and D and S along the secondary axis of S. -/
structure MissingWestWing {R : ℝ} (P : NormalizedPacking R) : Prop where
  not_west : ¬ Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)
  from_diagonal : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)
  south_wing : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

/-- The south wing is missing: D and S are separated along the secondary axis
of D but not along that of S, and W and D along the secondary axis of W. -/
structure MissingSouthWing {R : ℝ} (P : NormalizedPacking R) : Prop where
  west_wing : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)
  from_diagonal : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)
  not_south : ¬ Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

/-- If W and D are not separated along the secondary axis of W, the west wing
is missing. -/
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

/-- If D and S are not separated along the secondary axis of S, the south wing
is missing. -/
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

lemma MissingWestWing.phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.helperAngle 2 < P.diagonalAngle-Real.pi/4 :=
  DW_Dsecondary_west_of_wall P h.from_diagonal

lemma MissingSouthWing.phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) : P.diagonalAngle-Real.pi/4 < P.helperAngle 4 :=
  DS_Dsecondary_south_of_wall P h.from_diagonal

end SquaresInCircles.Six.Analytic
