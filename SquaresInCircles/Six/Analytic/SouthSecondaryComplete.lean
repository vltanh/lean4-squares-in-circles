import SquaresInCircles.Six.Analytic.CoupledOwnRadialBound
import SquaresInCircles.Six.Analytic.SouthSecondaryChoice

/-!
# D and S are separated along a secondary axis

In every normalized packing D and S are separated along the secondary axis of D
or along that of S. For `s ≤ d` this is `south_secondary_choice_of_angle`. If
`s > d`, then S is separated from C along its own axis, since otherwise
`s < 2/5 < d`, and `r = s - d` lies in `[0, 1/6]`. The radial profiles of D and
S then make the projections of the difference of their centres on the two
secondary axes sum to at least twice the threshold `(1 + cos r + sin r)/2`, so
one of the two axes separates.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma overtaking_own_secondary_choice {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownBits 4=true) (horder : P.diagonalAngle≤P.helperAngle 4) :
    SouthSecondaryChoice P := by
  let r := P.helperAngle 4-P.diagonalAngle
  have hd : 1/2≤P.diagonalAngle := (normalized_diagonal_gt_half P).le
  have hs : P.helperAngle 4≤2/3 := P.helper_windows.2.2.2.2.le
  have hr : 0≤r ∧ r≤1/6 := by dsimp [r]; constructor <;> linarith
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.helperAngle 4 := P.phase_from_deviation 4
  have hsum := coupled_own_radial_sum (P.contained 4) P.box.2.2 hd horder hs
    (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    (by simpa only [hSphase] using P.own_separator 4 hown)
  have hwork := overtaking_secondary_sum (r := r) (P.contained 3) (P.contained 4) hr hsum
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show r∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hr.1,hr.2,Real.pi_gt_d2])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hq : P.phase 4-P.phase 3=Real.pi/2+r := by
    rw [hDphase,hSphase]
    dsimp [r]
    ring
  have hthreshold : Seven.SAT.threshold (P.square 3) (P.square 4)=
      (1+Real.cos r+Real.sin r)/2 := by
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,hq,angularWidth]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,add_zero,abs_neg,
      abs_of_nonneg hsin,abs_of_nonneg hcos]
    ring
  have hDwork : dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)=
      P.radial 4*Real.cos r-P.transverse 4*Real.sin r-P.transverse 3 := by
    change frameY (P.square 3) (sub (P.square 4).center (P.square 3).center)=_
    rw [P.square_def 3,P.square_def 4,pair_frameY_left,hq]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,add_zero]
    ring
  have hSwork : dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)=
      P.transverse 4+P.radial 3*Real.cos r+P.transverse 3*Real.sin r := by
    change frameY (P.square 4) (sub (P.square 4).center (P.square 3).center)=_
    rw [P.square_def 3,P.square_def 4,pair_frameY_right,hq]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,add_zero]
    ring
  unfold SouthSecondaryChoice
  rw [hthreshold,hDwork,hSwork]
  by_cases h : (1+Real.cos r+Real.sin r)/2≤
      P.radial 4*Real.cos r-P.transverse 4*Real.sin r-P.transverse 3
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- In a normalized packing D and S are separated along a secondary axis. -/
theorem south_secondary_choice {R : ℝ} (P : NormalizedPacking R) : SouthSecondaryChoice P := by
  by_cases h : P.helperAngle 4≤P.diagonalAngle
  · exact south_secondary_choice_of_angle P h
  · have hown : P.ownBits 4=true := by
      cases hbit : P.ownBits 4
      · have hs := (abs_lt.mp (P.cardinal_angle 4 hbit)).2
        have hd := normalized_diagonal_gt_half P
        exfalso
        linarith
      · rfl
    exact overtaking_own_secondary_choice P hown (le_of_not_ge h)

end SquaresInCircles.Six.Analytic
