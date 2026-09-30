module
public import SquaresInCircles.Six.Analytic.LowDiagonalEndpoints
public import SquaresInCircles.Six.Analytic.CanonicalWestSign

@[expose] public section

/-!
# The low-diagonal tail for OWN W is excluded analytically

Freeze all center coordinates, prove separate concavity before maximizing
supports, and use the four original rectangle corners. The negative mixed
sine coefficient is compensated by the central-edge terms, as proved in
CompensatedTrigConcavity. The endpoint cap is invoked only with its proved
slope inequality. No old SD-Ws/SD-Ds checker or partition is imported.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma low_secondary_frozen_positive (ds : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hbW : |bw|<1/2) (hbD : |bd|<1/2)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<lowFrozen ds v d aw bw ad bd cx cy := by
  obtain ⟨h00,h0D,hV0,hVD⟩ := low_secondary_corners ds hW hD hc
  rw [low_frozen_formula] at h00 h0D hV0 hVD ⊢
  have hcx : 77/200≤1/2-cx := by linarith [hc.1.2,c0_lt_23_200]
  have hcy : 77/200≤1/2-cy := by linarith [hc.2.2,c0_lt_23_200]
  have hplus : 1/2≤1/2+cy := by linarith [hc.2.1]
  have haw : aw≤1113/1000 := hW.a_le_rho0.trans rho0_upper.le
  have had : ad≤1113/1000 := hD.a_le_rho0.trans rho0_upper.le
  apply compensated_frozen_positive
    (by cases ds <;> dsimp [lowBeta] <;> linarith)
    (by cases ds <;> dsimp [lowBeta] <;> linarith)
    (by cases ds <;> dsimp [lowAlpha] <;> linarith)
    (by cases ds <;> dsimp [lowAlpha] <;> linarith)
    (by cases ds <;> dsimp [lowMu] <;> linarith [(abs_lt.mp hbW).1,(abs_lt.mp hbD).2])
    (by cases ds <;> dsimp [lowMu] <;> linarith)
    hv hd h00 h0D hV0 hVD

private lemma low_secondary_trig {v d : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    (0≤Real.cos v ∧ 0≤Real.sin v) ∧ (0≤Real.cos d ∧ 0≤Real.sin d) ∧
      (0≤Real.cos (v+d) ∧ 0≤Real.sin (v+d)) := by
  have h (x : ℝ) (hx : 0≤x ∧ x≤7/6) : 0≤Real.cos x ∧ 0≤Real.sin x :=
    ⟨Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_gt_d2]⟩,
     Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2])⟩
  exact ⟨h v ⟨hv.1,by linarith [hv.2]⟩,h d ⟨hd.1,by linarith [hd.2]⟩,
    h (v+d) ⟨by linarith [hv.1,hd.1],by linarith [hv.2,hd.2]⟩⟩

/-- Each frozen stress is a nonnegative linear combination of three actual
separator gaps. The source flag selects W-secondary or D-secondary. -/
lemma low_secondary_frozen_nonpositive (ds : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi-v) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    lowFrozen ds v d aw bw ad bd cx cy≤0 := by
  obtain ⟨⟨hcv,hsv⟩,⟨hcd,hsd⟩,⟨hcq,hsq⟩⟩ := low_secondary_trig hv hd
  have hW : 1/2-aw+(1/2-cx)*Real.cos v+(1/2+cy)*Real.sin v≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
      abs_neg,abs_of_nonneg hcv,abs_of_nonneg hsv] at hCW
    nlinarith only [hCW]
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
      abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hCD
    nlinarith only [hCD]
  have hq : (Real.pi+d)-(Real.pi-v)=v+d := by ring
  cases ds
  · change Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi-v) aw bw)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_left,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hWD
    dsimp [lowFrozen,lowWForce,lowDForce,lowAlpha,lowBeta,lowMu,dot]
    nlinarith only [hW,hD,hWD]
  · change Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      frameY (orientedSquare (Real.pi+d) ad bd)
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center) at hWD
    rw [oriented_pair_threshold,pair_frameY_right,hq,
      angularWidth,abs_of_nonneg hcq,abs_of_nonneg hsq] at hWD
    dsimp [lowFrozen,lowWForce,lowDForce,lowAlpha,lowBeta,lowMu,dot]
    nlinarith only [hW,hD,hWD]

/-- Neither forward secondary source fits the low-diagonal OWN-W rectangle. -/
theorem low_diagonal_own_secondary_impossible (ds : Bool) {v d aw bw ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hWcore : AvoidsCore aw |bw|) (hDcore : AvoidsCore ad |bd|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (if ds then normalY (orientedSquare (Real.pi+d) ad bd)
        else normalY (orientedSquare (Real.pi-v) aw bw))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) : False := by
  have hpositive := low_secondary_frozen_positive ds hv hd hW hD
    (hW.u_lt_half hWcore) (hD.u_lt_half hDcore) hc
  have hnegative := low_secondary_frozen_nonpositive ds hv hd hCW hCD hWD
  linarith

/-- The analytic d>1/2 tail for every packing whose W helper is canonically OWN. -/
theorem own_west_diagonal_gt_half {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownBits 2=true) : 1/2<P.diagonalAngle := by
  by_contra! hd
  have hwneg := canonical_own_west_negative P hown
  have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/3 := by
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hdiag : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 :=
    ⟨P.diagonal_angle_range.1.le,hd⟩
  have hWphase : P.phase 2=Real.pi-(-P.helperAngle 2) := by
    rw [P.phase_from_deviation 2]
    ring
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  obtain ⟨k,hsep,hcases⟩ := DW_secondary_exists P
  rcases hcases with rfl | rfl
  · apply low_diagonal_own_secondary_impossible false hv hdiag (P.contained 2) (P.contained 3)
      (P.avoidsCore 2) (P.avoidsCore 3) P.box
      (by simpa only [hWphase] using P.own_separator 2 hown)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa only [Stress.pairNormal,Matrix.cons_val_zero,Matrix.cons_val_one,
      Bool.false_eq_true,if_false,P.square_def,hWphase,hDphase] using hsep
  · apply low_diagonal_own_secondary_impossible true hv hdiag (P.contained 2) (P.contained 3)
      (P.avoidsCore 2) (P.avoidsCore 3) P.box
      (by simpa only [hWphase] using P.own_separator 2 hown)
      (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    simpa [Stress.pairNormal,P.square_def,hWphase,hDphase] using hsep

end SquaresInCircles.Six.Analytic
