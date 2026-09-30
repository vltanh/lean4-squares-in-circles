import SquaresInCircles.Six.Analytic.FrozenPrimaryEndpoints
import SquaresInCircles.Six.Analytic.SmallGapPrimary

/-!
# Analytic exclusion of the inward W-primary D-edge for OWN W

For w<=0, freeze both local centers and the central coordinates. The three
stress contributions are nonnegative-coefficient trigonometric functions of
-v=w, d and v+d. Concavity and the four proved endpoint bounds contradict
the three actual separating inequalities. The w>=0 region uses the uniform
sixty-degree primary exclusion instead. No support switch is differentiated
and no previously certified fixed row is used.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma first_quadrant_signs {x : ℝ} (hx : 0≤x ∧ x≤Real.pi/2) :
    0≤Real.cos x ∧ 0≤Real.sin x :=
  ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hx.2⟩,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos])⟩

lemma inward_primary_frozen_positive {v d aw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤Real.pi/4)
    (haw : aw≤rho0) (hD : ContainedChart ad |bd|) (hb : |bd|<1/2)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<inwardPrimaryFrozen v d aw ad bd cx cy := by
  have hxhalf : 0≤1/2-cx := by linarith [hc.1.2,c0_lt_23_200]
  have hyhalf : 0≤1/2-cy := by linarith [hc.2.2,c0_lt_23_200]
  have had : 0≤1/2+ad := by linarith [hD.half_le]
  have hbd : 0≤1/2-bd := by linarith [(abs_lt.mp hb).2]
  unfold inwardPrimaryFrozen
  apply frozenTrig_positive
    (show 0≤(43/100)*(1/2-cx) by positivity)
    (show 0≤(43/100)*(1/2+cy) by positivity)
    (show 0≤(19/50)*(1/2-cx) by positivity)
    (show 0≤(19/50)*(1/2-cy) by positivity)
    (show 0≤(19/100)*(1/2+ad) by positivity)
    (show 0≤(19/100)*(1/2-bd) by positivity)
    (by norm_num) (by positivity)
    (show (2:ℝ)/3+Real.pi/4≤Real.pi/2 by linarith [Real.pi_gt_d2]) hv hd
  · exact inward_primary_corner_zero haw hD hc
  · exact inward_primary_corner_zero_quarter haw hD hc
  · exact inward_primary_corner_far_zero haw hD hc
  · exact inward_primary_corner_far_quarter haw hD hc

lemma inward_primary_frozen_nonpositive {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤Real.pi/4)
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (scale (-1) (normalX (orientedSquare (Real.pi-v) aw bw)))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    inwardPrimaryFrozen v d aw ad bd cx cy≤0 := by
  have hvtr := first_quadrant_signs ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩
  have hdtr := first_quadrant_signs ⟨hd.1,by linarith [hd.2,Real.pi_pos]⟩
  have hqtr := first_quadrant_signs
    (show 0≤v+d ∧ v+d≤Real.pi/2 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2])
  have hW : 1/2-aw+(1/2-cx)*Real.cos v+(1/2+cy)*Real.sin v≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,
      Real.sin_pi_sub,abs_neg,abs_of_nonneg hvtr.1,abs_of_nonneg hvtr.2] at hCW
    nlinarith only [hCW]
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,
      Real.sin_pi_add,abs_neg,abs_of_nonneg hdtr.1,abs_of_nonneg hdtr.2] at hCD
    nlinarith only [hCD]
  have hproj : dot (scale (-1) (normalX (orientedSquare (Real.pi-v) aw bw)))
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center)=
      -(ad*Real.cos (v+d)-bd*Real.sin (v+d)-aw) := by
    have hp := pair_frameX_left (Real.pi-v) aw bw (Real.pi+d) ad bd
    have hq : (Real.pi+d)-(Real.pi-v)=v+d := by ring
    rw [hq] at hp
    change -(frameX (orientedSquare (Real.pi-v) aw bw)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center))=_
    rw [hp]
  have hq : (Real.pi+d)-(Real.pi-v)=v+d := by ring
  rw [hproj,oriented_pair_threshold,hq,angularWidth,
    abs_of_nonneg hqtr.1,abs_of_nonneg hqtr.2] at hWD
  have hE : 1/2-aw+(1/2+ad)*Real.cos (v+d)+(1/2-bd)*Real.sin (v+d)≤0 := by
    nlinarith only [hWD]
  dsimp [inwardPrimaryFrozen,frozenTrig]
  nlinarith only [hW,hD,hE]

/-- Whole-domain negative-W exclusion using actual geometry at Q0. -/
theorem inward_primary_own_negative_impossible {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤Real.pi/4)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hDcore : AvoidsCore ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (scale (-1) (normalX (orientedSquare (Real.pi-v) aw bw)))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) : False := by
  have hpos := inward_primary_frozen_positive hv hd hW.a_le_rho0 hD
    (hD.u_lt_half hDcore) hc
  have hneg := inward_primary_frozen_nonpositive hv hd hCW hCD hWD
  linarith

/-- The entire OWN-W inward-primary branch is eliminated, not just a scalar row. -/
theorem normalized_ownW_inward_primary_excluded {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownBits 2=true) :
    ¬ Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (scale (-1) (normalX (P.square 2)))
        (sub (P.square 3).center (P.square 2).center) := by
  intro hsep
  have hwphase : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
  have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  by_cases hw : 0≤P.helperAngle 2
  · have hq : |P.phase 3-P.phase 2|≤Real.pi/3 := by
      rw [abs_of_nonneg (sub_nonneg.mpr P.primary_order.2.2.1.le),hwphase,hdphase]
      linarith [P.diagonal_angle_range.2,Real.pi_pos]
    have hn := oriented_inward_primary_excluded (P.contained 2) (P.contained 3)
      (P.avoidsCore 2) (P.avoidsCore 3) hq
    exact not_le_of_gt hn hsep
  · have hnegative : P.helperAngle 2<0 := lt_of_not_ge hw
    have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/3 := by
      constructor <;> linarith [P.helper_windows.2.2.1.1]
    have hW := P.own_separator 2 hown
    have hD := P.own_separator 3 P.diagonal_own
    have hwphase' : P.phase 2=Real.pi-(-P.helperAngle 2) := by rw [hwphase]; ring
    apply inward_primary_own_negative_impossible hv
      ⟨P.diagonal_angle_range.1.le,P.diagonal_angle_range.2⟩
      (P.contained 2) (P.contained 3) (P.avoidsCore 3) P.box
    · simpa only [hwphase'] using hW
    · simpa only [hdphase] using hD
    · simpa only [P.square_def,hwphase',hdphase] using hsep

end SquaresInCircles.Six.Analytic
