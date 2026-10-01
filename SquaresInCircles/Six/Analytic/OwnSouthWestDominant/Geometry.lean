import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Support
import SquaresInCircles.Six.Analytic.OwnSouthOrdered.Geometry
import SquaresInCircles.Six.Analytic.CanonicalSouthSign

/-!
# A missing south wing has S separated along the south side of C

In a missing south wing D and S are not separated along the secondary axis of
S; they are along that of D, and W and D along that of W. Let W and S, at the
phases `π - v` and `3π/2 + s`, be separated from C along their own axes, with
`0 ≤ s ≤ v`. With the separation of C and D along the own axis of D, these are
the five separations of the west-dominant stress, which exclude a missing
south wing. The order `v ≤ s` is excluded in `OwnSouthOrdered`, and a W
separated from C along the west side of C in `CardinalSouthTail`. So in a
missing south wing S is separated from C along the south side of C.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnSouthWestDominant
open Normalization

theorem not_missing_south_of_order {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true)
    (horder : P.helperAngle 4 ≤ -P.helperAngle 2) : ¬ MissingSouthWing P := by
  intro hmissing
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hv : v ≤ 2/3 := by
    dsimp [v]
    linarith [P.helper_windows.2.2.1.1]
  have hs : 0 ≤ s := (canonical_own_south_positive P hS).le
  have hvs : s ≤ v := horder
  have hsum : v+s ≤ 24/25 := by
    have h := normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths P hW hS
    dsimp [v,s]
    linarith
  have hd : 1/2 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hWphase : P.phase 2=Real.pi-v := by
    have h : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
    rw [h]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCW : 1/2+angularWidth v ≤
      P.radial 2+P.center.1*Real.cos v-P.center.2*Real.sin v := by
    have h := P.own_separator 2 hW
    rw [hWphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCS : 1/2+angularWidth s ≤
      P.radial 4-P.center.1*Real.sin s+P.center.2*Real.cos s := by
    have h := P.own_separator 4 hS
    rw [hSphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,add_zero,abs_neg,zero_sub,neg_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.1*Real.cos d+P.center.2*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase,add_comm Real.pi d] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add_pi,Real.sin_add_pi,
      abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (d+v) ≤
      P.radial 3*Real.sin (d+v)+P.transverse 3*Real.cos (d+v)-P.transverse 2 := by
    have h := hmissing.west_wing
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_left,
      show (Real.pi+d)-(Real.pi-v)=d+v by ring] at h
    exact h
  have hDS : 1/2+angularWidth (d-s) ≤
      P.radial 4*Real.cos (d-s)+P.transverse 4*Real.sin (d-s)-P.transverse 3 := by
    have h := hmissing.from_diagonal
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_left,
      show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    exact h
  exact scalar_impossible hv hs hvs hsum hd
    (P.contained 2) (P.contained 3) (P.contained 4)
    (P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2)
    ⟨P.box.2.1,P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2⟩ hCW hCS hCD hWD hDS

end SquaresInCircles.Six.Analytic.OwnSouthWestDominant

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- If S is separated from C along its own axis, the south wing is not
missing. -/
theorem not_missing_south_of_own_south {R : ℝ} (P : NormalizedPacking R)
    (hS : P.ownBits 4=true) : ¬ MissingSouthWing P := by
  intro hmissing
  have hW := CardinalSouthTail.missing_south_requires_own_west hmissing
  by_cases horder : -P.helperAngle 2 ≤ P.helperAngle 4
  · exact OwnSouthOrdered.not_missing_south_of_order P hW hS horder hmissing
  · exact OwnSouthWestDominant.not_missing_south_of_order P hW hS
      (le_of_not_ge horder) hmissing

/-- In a missing south wing S is separated from C along the south side of C. -/
lemma MissingSouthWing.south_cardinal {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) : P.ownBits 4=false := by
  cases hS : P.ownBits 4
  · rfl
  · exact False.elim (not_missing_south_of_own_south P hS h)

end SquaresInCircles.Six.Analytic
