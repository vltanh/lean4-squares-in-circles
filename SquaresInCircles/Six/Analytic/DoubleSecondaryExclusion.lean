module
public import SquaresInCircles.Six.Analytic.DoubleSecondaryCases

@[expose] public section

/-!
# No actual normalized packing has both diagonal edges sourced by D

The four canonical W/S cases now use whole-domain analytic inequalities:
OWN/OWN uses two affine secondary costs; cardinal/cardinal uses the exact
radial length sum; and the mixed cases use the proved one-variable depth
reserves. Every case uses the same four actual edge inequalities and cancels
D exactly. The former double-secondary hard tables are not imported.

This does not yet exclude a single D-sourced edge, or prove that every D/S
separator is secondary. Those independent classification tasks remain visible.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- Analytic exclusion of the entire double-D-secondary case. -/
theorem double_Dsecondary_impossible {R : ℝ} (P : NormalizedPacking R)
    (hWD : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center))
    (hDS : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) : False := by
  have hWphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hd : 1/2≤P.diagonalAngle ∧ P.diagonalAngle≤Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hs : -5/8≤P.helperAngle 4 ∧ P.helperAngle 4≤2/3 :=
    ⟨P.helper_windows.2.2.2.1.le,P.helper_windows.2.2.2.2.le⟩
  have hqS : 1/2≤Real.pi/2+P.helperAngle 4-P.diagonalAngle := by
    have h := DS_Dsecondary_gap_gt_half P hDS
    rw [hDphase,hSphase] at h
    linarith
  have hCW : 0≤centralMargin (if P.ownBits 2 then .own else .west)
      (Real.pi+P.helperAngle 2) (P.radial 2) (P.transverse 2) P.center.1 P.center.2 := by
    cases h : P.ownBits 2
    · simpa only [hWphase,h,Bool.false_eq_true,if_false] using P.cardinal_separator 2 h
    · simpa only [hWphase,h,if_true] using P.own_separator 2 h
  have hCS : 0≤centralMargin (if P.ownBits 4 then .own else .south)
      (3*Real.pi/2+P.helperAngle 4) (P.radial 4) (P.transverse 4) P.center.1 P.center.2 := by
    cases h : P.ownBits 4
    · simpa only [hSphase,h,Bool.false_eq_true,if_false] using P.cardinal_separator 4 h
    · simpa only [hSphase,h,if_true] using P.own_separator 4 h
  have hnegative := double_secondary_frozen_nonpositive (P.ownBits 2) (P.ownBits 4) hCW hCS
    (by simpa only [P.square_def,hWphase,hDphase] using hWD)
    (by simpa only [P.square_def,hDphase,hSphase] using hDS)
  cases hW : P.ownBits 2
  · have hw := (P.cardinal_angle 2 hW).le
    cases hS : P.ownBits 4
    · have hpositive := double_cardinal_secondary_gap_positive hw (P.cardinal_angle 4 hS).le hd
        (P.contained 2) (P.contained 4) P.box
      rw [hW,hS] at hnegative
      exact not_lt_of_ge hnegative hpositive
    · have hpositive := double_cardinalW_ownS_gap_positive hw hs hd hqS
        (P.contained 2) (P.contained 4) P.box
      rw [hW,hS] at hnegative
      exact not_lt_of_ge hnegative hpositive
  · have hsign := canonical_own_west_negative P hW
    have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/3 := by
      constructor <;> linarith [P.helper_windows.2.2.1.1]
    cases hS : P.ownBits 4
    · have hpositive := double_ownW_cardinalS_gap_positive hv (P.cardinal_angle 4 hS).le hd
        (P.contained 2) (P.contained 4) P.box
      simp only [neg_neg] at hpositive
      rw [hW,hS] at hnegative
      exact not_lt_of_ge hnegative hpositive
    · exact double_Dsecondary_own_impossible P hW hS hWD hDS

/-- When both selected edges are secondary, at least one has the candidate
wing source. This is a consequence, not a replacement for classifying D/S. -/
theorem one_candidate_secondary {R : ℝ} (P : NormalizedPacking R)
    (k l : Fin 8) (hk : k=2 ∨ k=6) (hl : l=2 ∨ l=6)
    (hWD : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (Stress.pairNormal k (P.square 2) (P.square 3))
        (sub (P.square 3).center (P.square 2).center))
    (hDS : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (Stress.pairNormal l (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center)) : k=2 ∨ l=6 := by
  rcases hk with rfl | rfl
  · exact Or.inl rfl
  · rcases hl with rfl | rfl
    · exact False.elim (double_Dsecondary_impossible P hWD hDS)
    · exact Or.inr rfl

end SquaresInCircles.Six.Analytic
