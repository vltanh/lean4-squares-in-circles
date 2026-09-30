module
public import SquaresInCircles.Six.Analytic.SouthOuterTail.ScalarGeometry
public import SquaresInCircles.Six.Analytic.ReflectedOwnWings.Geometry

@[expose] public section

/-!
# The last independent analytic reduction obligation

Both candidate D separators are now supplied by the analytic missing-wing
exclusions. Their already proved west-tail consequence bounds an OWN west
angle. The four actual scalar inequalities below then invoke the complete
cardinal or OWN tail argument, proving s<11/25 with no finite classifier.
The original Packing predicate and normalization record are unchanged.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail
open Normalization

/-- The canonical OWN-S upper tail, proved from actual geometry rather than a table. -/
theorem normalized_own_south_upper_tail {R : ℝ} (P : NormalizedPacking R)
    (hS : P.ownBits 4=true) : P.helperAngle 4 < 11/25 := by
  by_contra! htail
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hedges := candidate_diagonal_separators P
  have hs : 11/25 ≤ s ∧ s ≤ 2/3 := ⟨htail,P.helper_windows.2.2.2.2.le⟩
  have hd : 1/2 ≤ d ∧ d ≤ 11/14 := by
    have hlo := normalized_diagonal_gt_half P
    have hhi := P.diagonal_angle_range.2
    dsimp [d]
    constructor <;> linarith [Real.pi_lt_d4]
  have hx : 0 ≤ P.center.1 ∧ P.center.1 ≤ coreUpper := by
    refine ⟨P.box.1.1,?_⟩
    exact P.box.1.2.trans CandidateWestTail.ceiling_bounds.2.2.2
  have hy : P.center.2 ≤ coreUpper :=
    P.box.2.2.trans CandidateWestTail.ceiling_bounds.2.2.2
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hCS : 1/2+angularWidth s ≤
      P.radial 4-P.center.1*Real.sin s+P.center.2*Real.cos s := by
    have h := P.own_separator 4 hS
    rw [hSphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (d+v) ≤
      P.radial 3*Real.sin (d+v)+P.transverse 3*Real.cos (d+v)-P.transverse 2 := by
    have h := hedges.1
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 2) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,hWphase,hDphase,oriented_pair_threshold,pair_frameY_left,
      show (Real.pi+d)-(Real.pi-v)=d+v by ring] at h
    exact h
  have hDS : 1/2+angularWidth (d-s) ≤
      P.transverse 4+P.radial 3*Real.cos (d-s)-P.transverse 3*Real.sin (d-s) := by
    have h := hedges.2
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,hDphase,hSphase,oriented_pair_threshold,pair_frameY_right,
      show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2-(d-s) by ring,
      FixedPair.width_half_pi_sub,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] at h
    nlinarith only [h]
  cases hW : P.ownBits 2
  · have hw := abs_lt.mp (P.cardinal_angle 2 hW)
    have hv : -(2/5) < v ∧ v < 2/5 := by
      dsimp [v]
      constructor <;> linarith [hw.1,hw.2]
    have hCW : 1/2+angularWidth v ≤
        P.radial 2*Real.cos v+P.transverse 2*Real.sin v+P.center.1 := by
      have h := P.cardinal_separator 2 hW
      change 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
        P.center.1 P.center.2 at h
      rw [hWphase] at h
      simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
      dsimp [angularWidth]
      nlinarith only [h]
    by_cases hv0 : 0 ≤ v
    · exact cardinal_impossible false ⟨hv0,hv.2.le⟩ hs hd
        (P.contained 2) (P.contained 4) (P.contained 3) hx hy
        (by simpa [cardinalSign] using hCW) hCS
        (by simpa [cardinalSign] using hWD) hDS
    · exact cardinal_impossible true (x := -v)
        (by constructor <;> linarith [hv.1]) hs hd
        (P.contained 2) (P.contained 4) (P.contained 3) hx hy
        (by simpa [cardinalSign] using hCW) hCS
        (by simpa [cardinalSign] using hWD) hDS
  · have hwest := CandidateWestTail.normalized_own_west_tail_of_edges P hedges hW
    have hnegative := canonical_own_west_negative P hW
    have hv : 0 ≤ v ∧ v ≤ 11/25 := by
      dsimp [v]
      constructor <;> linarith
    have hCW : 1/2+angularWidth v ≤
        P.radial 2+P.center.1*Real.cos v-P.center.2*Real.sin v := by
      have h := P.own_separator 2 hW
      rw [hWphase] at h
      simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
      dsimp [angularWidth]
      nlinarith only [h]
    exact own_impossible hv hs hd (P.contained 2) (P.contained 4) (P.contained 3)
      P.high_diagonal_profile.2.le hx hy hCW hCS hWD hDS

end SquaresInCircles.Six.Analytic.SouthOuterTail
