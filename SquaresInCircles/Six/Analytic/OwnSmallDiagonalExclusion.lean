module
public import SquaresInCircles.Six.Analytic.SmallDiagonalOwnEndpoints
public import SquaresInCircles.Six.Analytic.SmallDiagonalNonnegativeWest

@[expose] public section

/-!
# Small diagonal angles are impossible when W is OWN

The fixed (3/2,2,1) stress is a positive combination of the two actual central
separations and the actual D-secondary W/D separation. Its full-rectangle
positivity contradicts that combination. Together with the earlier W-secondary
exclusion, this proves d>1/2 for every normalized packing whose W bit is OWN.
The cardinal-W case remains a separate obligation.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma ownSmallD_nonpositive {aw bw ad bd cx cy v d : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) :
    ownSmallDStress aw bw ad bd cx cy v d≤0 := by
  have htv := small_secondary_trig ⟨hv.1,by linarith [hv.2]⟩
  have htd := small_secondary_trig ⟨hd.1,by linarith [hd.2]⟩
  have htq := small_secondary_trig
    (show 0≤v+d ∧ v+d≤7/6 by constructor <;> linarith [hv.1,hv.2,hd.1,hd.2])
  have hw : 1/2-aw+(1/2-cx)*Real.cos v+(1/2+cy)*Real.sin v≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
      abs_neg,abs_of_nonneg htv.1,abs_of_nonneg htv.2.1] at hCW
    nlinarith only [hCW]
  have hD : 1/2-ad+(1/2-cx)*Real.cos d+(1/2-cy)*Real.sin d≤0 := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
      abs_neg,abs_of_nonneg htd.1,abs_of_nonneg htd.2.1] at hCD
    nlinarith only [hCD]
  have hq : (Real.pi+d)-(Real.pi-v)=v+d := by ring
  change Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
      (orientedSquare (Real.pi+d) ad bd)≤
    frameY (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center) at hWD
  rw [pair_frameY_right,oriented_pair_threshold,hq,angularWidth,
    abs_of_nonneg htq.1,abs_of_nonneg htq.2.1] at hWD
  have he : 1/2+(1/2+bw)*Real.cos (v+d)+(1/2-aw)*Real.sin (v+d)-bd≤0 := by
    nlinarith only [hWD]
  dsimp [ownSmallDStress,frozenTrig]
  nlinarith only [hw,hD,he]

/-- The entire negative-W rectangle is excluded with one fixed stress. -/
theorem own_small_diagonal_Dsecondary_impossible {aw bw ad bd cx cy v d : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hb : |bw|≤1/2) (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2)
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCD : 0≤centralMargin .own (Real.pi+d) ad bd cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center)) : False := by
  have hp := ownSmallD_positive hW hD hb hC hv hd
  have hn := ownSmallD_nonpositive hv hd hCW hCD hWD
  linarith

/-- An unconditional d bound within the OWN-W canonical case. It uses no
D/S classification or candidate helper-domain premise. -/
theorem ownW_forces_large_diagonal {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownBits 2=true) : 1/2<P.diagonalAngle := by
  by_cases hw : 0≤P.helperAngle 2
  · exact nonnegative_W_forces_large_diagonal P hw
  · by_contra! hdsmall
    have hd : 0≤P.diagonalAngle ∧ P.diagonalAngle≤1/2 := ⟨P.diagonal_angle_range.1.le,hdsmall⟩
    obtain ⟨k,hsep,hk⟩ := DW_secondary_exists P
    rcases hk with rfl | rfl
    · linarith [W_secondary_forces_large_diagonal P hsep]
    · have hwindow := P.helper_windows.2.2.1
      have hv : 0≤-P.helperAngle 2 ∧ -P.helperAngle 2≤2/3 := by
        constructor <;> linarith [hwindow.1]
      have hwphase : P.phase 2=Real.pi-(-P.helperAngle 2) := by
        have hh : P.phase 2=Real.pi+P.helperAngle 2 := P.phase_from_deviation 2
        linarith
      have hdphase : P.phase 3=Real.pi+P.diagonalAngle := by
        dsimp [NormalizedPacking.diagonalAngle]
        ring
      apply own_small_diagonal_Dsecondary_impossible (P.contained 2) (P.contained 3)
        ((P.contained 2).u_lt_half (P.avoidsCore 2)).le P.box hv hd
      · simpa only [hwphase] using P.own_separator 2 hown
      · simpa only [hdphase] using P.own_separator 3 P.diagonal_own
      · change Seven.SAT.threshold (P.square 2) (P.square 3)≤
          dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center) at hsep
        simpa only [P.square_def,hwphase,hdphase] using hsep

end SquaresInCircles.Six.Analytic
