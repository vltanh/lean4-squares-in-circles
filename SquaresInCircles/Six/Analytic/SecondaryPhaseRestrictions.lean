import SquaresInCircles.Six.Analytic.NonnegativeWestSecondary
import SquaresInCircles.Six.Analytic.SouthSecondaryComplete

/-!
# Geometric phase restrictions for the remaining secondary sources

The core-constrained projection estimate excludes a D-sourced separator whenever
its actual inter-square phase gap is at most pi/4. This sharpens the earlier
1/2 gap bound on BOTH wings. No candidate-graph or pair-domain hypothesis is
used, and no reflection of the normalized packing is taken.

These restrictions do not exclude the entire mixed-source region. They locate
it on the actual geometric walls w=d-pi/4 and s=d-pi/4. Compilation is deferred;
all arguments below use previously written analytic lemmas, not certificates.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- A D-sourced W/D separator lies strictly beyond the quarter-turn gap. -/
theorem DW_Dsecondary_gap_gt_quarter {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    Real.pi/4 < P.phase 3-P.phase 2 := by
  by_contra! hsmall
  have hq : 0 ≤ P.phase 3-P.phase 2 ∧ P.phase 3-P.phase 2 ≤ Real.pi/4 :=
    ⟨sub_nonneg.mpr P.primary_order.2.2.1.le,hsmall⟩
  have hbD := (normalized_diagonal_core_bounds P).2.2
  have hbound := nonnegative_W_Dsecondary_excluded
    (P.contained 2) (P.avoidsCore 2) hq
    ((le_abs_self (P.transverse 3)).trans_lt hbD)
  change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right] at hsep
  linarith

/-- The same core support estimate applies to the S center with its transverse
coordinate negated, and to the negative D transverse coordinate. -/
theorem DS_Dsecondary_gap_gt_quarter {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    Real.pi/4 < P.phase 4-P.phase 3 := by
  by_contra! hsmall
  have hq : 0 ≤ P.phase 4-P.phase 3 ∧ P.phase 4-P.phase 3 ≤ Real.pi/4 :=
    ⟨sub_nonneg.mpr P.primary_order.2.2.2.1.le,hsmall⟩
  have hc : ContainedChart (P.radial 4) |-(P.transverse 4)| := by
    simpa only [abs_neg] using P.contained 4
  have hcore : AvoidsCore (P.radial 4) |-(P.transverse 4)| := by
    simpa only [abs_neg] using P.avoidsCore 4
  have hbD := (normalized_diagonal_core_bounds P).2.2
  have hbound := nonnegative_W_Dsecondary_excluded hc hcore hq
    ((neg_le_abs (P.transverse 3)).trans_lt hbD)
  change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
    frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left] at hsep
  nlinarith only [hsep,hbound]

/-- A noncandidate W/D edge is confined to w<d-pi/4, not just w<0. -/
theorem DW_Dsecondary_west_of_wall {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    P.helperAngle 2 < P.diagonalAngle-Real.pi/4 := by
  have h := DW_Dsecondary_gap_gt_quarter P hsep
  have hw : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [hw,hd] at h
  linarith

/-- A noncandidate D/S edge is confined to s>d-pi/4. -/
theorem DS_Dsecondary_south_of_wall {R : ℝ} (P : NormalizedPacking R)
    (hsep : Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    P.diagonalAngle-Real.pi/4 < P.helperAngle 4 := by
  have h := DS_Dsecondary_gap_gt_quarter P hsep
  have hs : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hd : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [hd,hs] at h
  linarith

/-- On this closed side of the wall the W-wing separator is automatic. -/
theorem west_wing_of_phase_wall {R : ℝ} (P : NormalizedPacking R)
    (hw : P.diagonalAngle-Real.pi/4 ≤ P.helperAngle 2) :
    Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) := by
  obtain ⟨k,hk,hchoice⟩ := DW_secondary_exists P
  rcases hchoice with rfl | rfl
  · exact hk
  · have h := DW_Dsecondary_west_of_wall P hk
    linarith

/-- On the other closed side the S-wing separator is automatic. -/
theorem south_wing_of_phase_wall {R : ℝ} (P : NormalizedPacking R)
    (hs : P.helperAngle 4 ≤ P.diagonalAngle-Real.pi/4) :
    Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center) := by
  rcases south_secondary_choice P with hD | hS
  · have h := DS_Dsecondary_south_of_wall P hD
    linarith
  · exact hS

end SquaresInCircles.Six.Analytic
