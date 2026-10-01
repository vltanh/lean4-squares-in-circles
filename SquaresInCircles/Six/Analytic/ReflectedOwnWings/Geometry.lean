import SquaresInCircles.Six.Analytic.ReflectedOwnWings.Support
import SquaresInCircles.Six.Analytic.OwnWestOwnSouth.Geometry
import SquaresInCircles.Six.Analytic.OwnWestCardinalSouth.Geometry

/-!
# Both candidate diagonal separators now follow analytically

Only the two-OWN missing-west case with the south tilt larger remains.
Reflect its scalar coordinates, not its NormalizedPacking record. The actual
west-source bounds prove the enlarged reflected diagonal and south intervals.
The reflected five inequalities are derived from the original witnesses below.
The analytic scalar contradiction closes this ordering. Together with the
other bit/order cases, both missing-wing exclusions are now unconditional.
No finite classification or candidate W-source conclusion is a premise.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.ReflectedOwnWings
open Normalization

theorem not_missing_west_of_order {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true)
    (horder : -P.helperAngle 2 ≤ P.helperAngle 4) : ¬ MissingWestWing P := by
  intro hmissing
  let v := P.helperAngle 4
  let s := -P.helperAngle 2
  let d := Real.pi/2-P.diagonalAngle
  have hcore := hmissing.own_west_domain hW
  have hgap := hmissing.own_gap_reserve hW
  have hsumOld := normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths P hW hS
  have hdOld : P.diagonalAngle ≤ 11/14 := by
    linarith [P.diagonal_angle_range.2,Real.pi_lt_d4]
  have hs : 48/175 ≤ s ∧ s ≤ 12/25 := by
    dsimp [s]
    constructor <;> linarith
  have hvs : s ≤ v := horder
  have hv : v ≤ 2/3 := P.helper_windows.2.2.2.2.le
  have hsum : v+s ≤ 24/25 := by
    dsimp [v,s]
    linarith
  have hd : 157/200 ≤ d ∧ d ≤ 163/175 := by
    dsimp [d]
    constructor <;> linarith [hcore.2,P.diagonal_angle_range.2,Real.pi_gt_d2,Real.pi_lt_d4]
  have hWphase : P.phase 2=Real.pi-s := by
    rw [P.phase_from_deviation 2,show cardinalCenter (matchingCardinal 2)=Real.pi from rfl]
    dsimp [s]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+v := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+(Real.pi/2-d) := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 4+P.center.2*Real.cos v-P.center.1*Real.sin v := by
    have h := P.own_separator 4 hS
    rw [hSphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,neg_neg,add_zero,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCS : 1/2+angularWidth s ≤
      P.radial 2-P.center.2*Real.sin s+P.center.1*Real.cos s := by
    have h := P.own_separator 2 hW
    rw [hWphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.2*Real.cos d+P.center.1*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase,add_comm Real.pi] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add_pi,Real.sin_add_pi,
      Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (d+v) ≤
      P.radial 3*Real.sin (d+v)+(-P.transverse 3)*Real.cos (d+v)-(-P.transverse 4) := by
    have h := hmissing.south_wing
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_right,
      show (3*Real.pi/2+v)-(Real.pi+(Real.pi/2-d))=d+v by ring] at h
    nlinarith only [h]
  have hDS : 1/2+angularWidth (d-s) ≤
      P.radial 2*Real.cos (d-s)+(-P.transverse 2)*Real.sin (d-s)-(-P.transverse 3) := by
    have h := hmissing.from_diagonal
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_right,
      show (Real.pi+(Real.pi/2-d))-(Real.pi-s)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    nlinarith only [h]
  exact scalar_impossible hs hvs hv hsum hd
    (by simpa only [abs_neg] using P.contained 4)
    (by simpa only [abs_neg] using P.contained 3)
    (by simpa only [abs_neg] using P.contained 2)
    (P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    ⟨P.box.1.1,P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2⟩ hCW hCS hCD hWD hDS

end SquaresInCircles.Six.Analytic.ReflectedOwnWings

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- The two-OWN orderings and both cardinal-wing cases exhaust the actual geometry. -/
theorem not_missing_west {R : ℝ} (P : NormalizedPacking R) : ¬ MissingWestWing P := by
  intro h
  have hW := h.west_own
  have hS := h.south_own
  by_cases horder : P.helperAngle 4 ≤ -P.helperAngle 2
  · exact OwnWestOwnSouth.not_missing_west_of_order P hW hS horder h
  · exact ReflectedOwnWings.not_missing_west_of_order P hW hS (le_of_not_ge horder) h

/-- The actual candidate W-sourced separating inequality holds in every normalized packing. -/
theorem candidate_west_separator {R : ℝ} (P : NormalizedPacking R) :
    Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) := by
  by_contra h
  exact not_missing_west P (missing_west_of_failure P h)

/-- Both candidate edges are now obtained from analytic exclusions, not the finite classifier. -/
theorem candidate_diagonal_separators {R : ℝ} (P : NormalizedPacking R) :
    FixedPair.CandidateDSeparators P :=
  ⟨candidate_west_separator P,candidate_south_separator P⟩

end SquaresInCircles.Six.Analytic
