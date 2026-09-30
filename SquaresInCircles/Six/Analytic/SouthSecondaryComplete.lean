module
public import SquaresInCircles.Six.Analytic.CoupledOwnRadialBound
public import SquaresInCircles.Six.Analytic.SouthSecondaryChoice

@[expose] public section

/-!
# Every normalized packing admits a forward secondary D/S source

For s<=d, primary directions are excluded or replaced by a stronger secondary
projection. For s>=d, S must be OWN; its central profile coupled with D's
forces the sum of the two secondary works above twice the threshold. Thus
one of them separates. This last argument does not assume a secondary source
in order to prove one, and does not reflect the global D half-window.
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
  have hsum := coupled_own_radial_sum (P.contained 3) (P.contained 4) P.box.2.2 hd horder hs
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
      zero_mul,one_mul,zero_sub,zero_add,add_zero,abs_neg,
      abs_of_nonneg hsin,abs_of_nonneg hcos]
    ring
  have hDwork : dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)=
      P.radial 4*Real.cos r-P.transverse 4*Real.sin r-P.transverse 3 := by
    change frameY (P.square 3) (sub (P.square 4).center (P.square 3).center)=_
    rw [P.square_def 3,P.square_def 4,pair_frameY_left,hq]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,zero_add,add_zero]
    ring
  have hSwork : dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)=
      P.transverse 4+P.radial 3*Real.cos r+P.transverse 3*Real.sin r := by
    change frameY (P.square 4) (sub (P.square 4).center (P.square 3).center)=_
    rw [P.square_def 3,P.square_def 4,pair_frameY_right,hq]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,zero_add,add_zero]
    ring
  unfold SouthSecondaryChoice
  rw [hthreshold,hDwork,hSwork]
  by_cases h : (1+Real.cos r+Real.sin r)/2≤
      P.radial 4*Real.cos r-P.transverse 4*Real.sin r-P.transverse 3
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Analytic source selection on the whole normalized S-angle range. -/
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

/-- The selected index and its actual inequality, for later finite source assembly. -/
theorem DS_secondary_exists_analytic {R : ℝ} (P : NormalizedPacking R) : ∃ k : Fin 8,
    Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (Stress.pairNormal k (P.square 3) (P.square 4))
        (sub (P.square 4).center (P.square 3).center) ∧ (k=2 ∨ k=6) := by
  rcases south_secondary_choice P with h | h
  · exact ⟨2,h,Or.inl rfl⟩
  · exact ⟨6,h,Or.inr rfl⟩

/-- At least one actual candidate wing separator always exists. Only the two
mixed secondary choices remain to be eliminated to obtain both candidate edges. -/
theorem one_wing_secondary {R : ℝ} (P : NormalizedPacking R) :
    (Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)) ∨
    (Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)) := by
  obtain ⟨k,hWD,hk⟩ := DW_secondary_exists P
  rcases hk with rfl | rfl
  · exact Or.inl hWD
  · rcases south_secondary_choice P with hDS | hDS
    · exact False.elim (double_Dsecondary_impossible P hWD hDS)
    · exact Or.inr hDS

end SquaresInCircles.Six.Analytic
