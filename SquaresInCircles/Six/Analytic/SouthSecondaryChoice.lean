import SquaresInCircles.Six.Analytic.SecondaryDominance
import SquaresInCircles.Six.Analytic.DoubleSecondaryExclusion

/-!
# Selecting a D/S secondary source without a stress table

If s<=d, the actual D/S phase gap lies in [0,pi/2]. Small-gap primary sources
are impossible. At larger gaps each primary can be replaced by a proved
stronger secondary projection. At q=pi/2 this replacement may be an equality,
so no false claim is made that every primary source must be strictly excluded.
Every cardinal S satisfies s<2/5<d, hence is covered unconditionally.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def SouthSecondaryChoice {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (Seven.SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) ∨
  (Seven.SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center))

/-- The choice is derived from the actual SAT inequality and the interior pins. -/
theorem south_secondary_choice_of_angle {R : ℝ} (P : NormalizedPacking R)
    (hs : P.helperAngle 4≤P.diagonalAngle) : SouthSecondaryChoice P := by
  obtain ⟨k,hsep,_,_,_⟩ := P.DS_source
  have hout := normalized_outward_axes_excluded P 3 4 k hsep
  have hpin := selected_axis_points_to_pin _ _ (P.pin 3) (P.pin 4) k hsep
  have hchord := P.DS_chord_signs
  have hk3 : k≠3 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 3))) (sub (fixedPin 4) (fixedPin 3)) at hpin
    rw [dot_scale_neg] at hpin
    linarith [hchord.2.1]
  have hk7 : k≠7 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 4))) (sub (fixedPin 4) (fixedPin 3)) at hpin
    rw [dot_scale_neg] at hpin
    linarith [hchord.2.2]
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hq0 : 0≤P.phase 4-P.phase 3 := sub_nonneg.mpr P.primary_order.2.2.2.1.le
  have hq1 : P.phase 4-P.phase 3≤Real.pi/2 := by rw [hDphase,hSphase]; linarith
  have hDprofile := P.high_diagonal_profile
  have hSrad := (P.contained 4).aMin_le (P.avoidsCore 4)
  have hStrans := (P.contained 4).u_le_U0 (P.avoidsCore 4)
  have hDtrans := (P.contained 3).u_lt_half (P.avoidsCore 3)
  have hDcore := (P.contained 3).aMin_le (P.avoidsCore 3)
  fin_cases k
  · exact False.elim (hout.1 rfl)
  · change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (scale (-1) (normalX (P.square 3)))
        (sub (P.square 4).center (P.square 3).center) at hsep
    rw [dot_scale_neg] at hsep
    change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      -frameX (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameX_left] at hsep
    by_cases hsmall : P.phase 4-P.phase 3≤11/10
    · have hc := cosine_lower_eleven_tenths
        (by simpa only [abs_of_nonneg hq0] using hsmall)
      have hb := inward_primary_cosine_bound (P.contained 3).a_le_rho0 hSrad
        ((P.contained 4).u_lt_half (P.avoidsCore 4)) hc
      exact False.elim (by linarith)
    · right
      change Seven.SAT.threshold (P.square 3) (P.square 4)≤
        frameY (P.square 4) (sub (P.square 4).center (P.square 3).center)
      rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_right]
      have hb := inward_Dprimary_le_Ssecondary (P.contained 3).a_le_rho0
        hDprofile.2.le hSrad hStrans ⟨(lt_of_not_ge hsmall).le,hq1⟩
      linarith
  · exact Or.inl hsep
  · exact False.elim (hk3 rfl)
  · change Seven.SAT.threshold (P.square 3) (P.square 4)≤
      frameX (P.square 4) (sub (P.square 4).center (P.square 3).center) at hsep
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameX_right] at hsep
    by_cases hsmall : P.phase 4-P.phase 3≤11/10
    · have hc := cosine_lower_eleven_tenths
        (by simpa only [abs_of_nonneg hq0] using hsmall)
      have hb := destination_primary_cosine_bound (P.contained 4).a_le_rho0 hDcore hDtrans hc
      exact False.elim (by linarith)
    · left
      change Seven.SAT.threshold (P.square 3) (P.square 4)≤
        frameY (P.square 3) (sub (P.square 4).center (P.square 3).center)
      rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left]
      have hb := Sprimary_le_Dsecondary hDprofile.1 hDprofile.2.le
        (P.contained 4).a_le_rho0 hStrans ⟨(lt_of_not_ge hsmall).le,hq1⟩
      linarith
  · exact False.elim (hout.2 rfl)
  · exact Or.inr hsep
  · exact False.elim (hk7 rfl)

/-- Every cardinal S admits an actual forward secondary source. -/
theorem south_secondary_choice_cardinal {R : ℝ} (P : NormalizedPacking R)
    (hS : P.ownBits 4=false) : SouthSecondaryChoice P := by
  apply south_secondary_choice_of_angle P
  have hs := (abs_lt.mp (P.cardinal_angle 4 hS)).2
  linarith [normalized_diagonal_gt_half P]

/-- When s<=d, the full pair of selected D edges contains a candidate wing
source. The two remaining mixed-source cases are not assumed away. -/
theorem one_wing_secondary_of_angle {R : ℝ} (P : NormalizedPacking R)
    (hs : P.helperAngle 4≤P.diagonalAngle) :
    (Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)) ∨
    (Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)) := by
  obtain ⟨k,hWD,hk⟩ := DW_secondary_exists P
  rcases hk with rfl | rfl
  · exact Or.inl hWD
  · rcases south_secondary_choice_of_angle P hs with hDS | hDS
    · exact False.elim (double_Dsecondary_impossible P hWD hDS)
    · exact Or.inr hDS

end SquaresInCircles.Six.Analytic
