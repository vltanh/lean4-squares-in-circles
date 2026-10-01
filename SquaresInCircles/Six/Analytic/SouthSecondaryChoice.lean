import SquaresInCircles.Six.Analytic.SecondaryDominance
import SquaresInCircles.Six.Analytic.DoubleSecondaryExclusion

/-!
# D and S along a secondary axis when s ≤ d

`SouthSecondaryChoice` says that D and S are separated along the secondary axis
of D or along that of S. If the angle `s` of S is at most the angle `d` of D,
their phases differ by `q` in `[0, π/2]`. The separating axis is not outward,
and it points from the pin of D towards the pin of S; this leaves one direction
of each of the four axes of D and S. A primary axis cannot separate for
`q ≤ 11/10`, by a cosine bound; for `q ≥ 11/10` the projection on the secondary
axis of the other square is at least the projection on the primary axis, so that
secondary axis separates as well.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- D and S are separated along the secondary axis of D or along that of S. -/
def SouthSecondaryChoice {R : ℝ} (P : NormalizedPacking R) : Prop :=
  (Seven.SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) ∨
  (Seven.SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center))

/-- If `s ≤ d`, D and S are separated along a secondary axis. -/
theorem south_secondary_choice_of_angle {R : ℝ} (P : NormalizedPacking R)
    (hs : P.helperAngle 4≤P.diagonalAngle) : SouthSecondaryChoice P := by
  obtain ⟨k,hsep,_,_,_⟩ := P.DS_source
  have hout := normalized_outward_axes_excluded P 3 4 k hsep
  have hpin := selected_axis_points_to_pin _ _ (P.pin 3) (P.pin 4) k hsep
  have hchord := P.DS_chord_signs
  have hk3 : k≠3 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 3))) (sub (Certificates.fixedPin 4) (Certificates.fixedPin 3)) at hpin
    rw [dot_scale_neg] at hpin
    linarith [hchord.2.1]
  have hk7 : k≠7 := by
    intro hk
    subst k
    change 0<dot (scale (-1) (normalY (P.square 4))) (sub (Certificates.fixedPin 4) (Certificates.fixedPin 3)) at hpin
    rw [dot_scale_neg] at hpin
    linarith [hchord.2.2]
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hq0 : 0≤P.phase 4-P.phase 3 := sub_nonneg.mpr P.primary_order.2.2.2.1.le
  have hq1 : P.phase 4-P.phase 3≤Real.pi/2 := by rw [hDphase,hSphase]; linarith
  have hDprofile := NormalizedPacking.high_diagonal_profile P
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
    · have hc := cosine_lower_eleven_tenths (q := P.phase 4-P.phase 3)
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
    · have hc := cosine_lower_eleven_tenths (q := P.phase 4-P.phase 3)
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

end SquaresInCircles.Six.Analytic
