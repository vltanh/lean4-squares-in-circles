import SquaresInCircles.Six.Analytic.DoubleSecondaryOwnBound

/-!
# No double separation at D with own wings

In a normalized packing with W and S separated from C along their own axes,
W–D and D–S are not both separated along the secondary axis of D. The weighted
sum of the four separating inequalities makes the gap for own wings
nonpositive, while it is positive on the angle ranges of the normalization; the
angle `π/2 + s - d` between D and S exceeds `1/2` because D–S is separated
along the secondary axis of D (`DS_Dsecondary_gap_gt_half`).
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma double_own_secondary_frozen_nonpositive {v s d aw bw ad bd aS bS cx cy : ℝ}
    (hCW : 0≤centralMargin .own (Real.pi-v) aw bw cx cy)
    (hCS : 0≤centralMargin .own (3*Real.pi/2+s) aS bS cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi-v) aw bw).center))
    (hDS : Seven.SAT.threshold (orientedSquare (Real.pi+d) ad bd)
        (orientedSquare (3*Real.pi/2+s) aS bS)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (3*Real.pi/2+s) aS bS).center
          (orientedSquare (Real.pi+d) ad bd).center)) :
    doubleOwnSecondaryGap v s d aw bw aS bS cx cy≤0 := by
  have hw : angularWidth (Real.pi-v)=angularWidth v := by
    simp [angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg]
  have hs : angularWidth (3*Real.pi/2+s)=angularWidth s := by
    simp [angularWidth,Real.cos_add,Real.sin_add,south_cos,south_sin,abs_neg,add_comm]
  simp only [centralMargin,centralNormal,hw,Real.cos_pi_sub,Real.sin_pi_sub] at hCW
  simp only [centralMargin,centralNormal,hs,Real.cos_add,Real.sin_add,
    south_cos,south_sin,zero_mul,neg_one_mul,add_zero] at hCS
  change Seven.SAT.threshold (orientedSquare (Real.pi-v) aw bw)
      (orientedSquare (Real.pi+d) ad bd)≤
    frameY (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi-v) aw bw).center) at hWD
  change Seven.SAT.threshold (orientedSquare (Real.pi+d) ad bd)
      (orientedSquare (3*Real.pi/2+s) aS bS)≤
    frameY (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (3*Real.pi/2+s) aS bS).center
        (orientedSquare (Real.pi+d) ad bd).center) at hDS
  rw [oriented_pair_threshold,pair_frameY_right,
    show (Real.pi+d)-(Real.pi-v)=d+v by ring] at hWD
  rw [oriented_pair_threshold,pair_frameY_left,
    show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2+s-d by ring] at hDS
  dsimp [doubleOwnSecondaryGap]
  nlinarith only [hCW,hCS,hWD,hDS]

/-- With W and S separated from C along their own axes, W–D and D–S are not
both separated along the secondary axis of D. -/
theorem double_Dsecondary_own_impossible {R : ℝ} (P : NormalizedPacking R)
    (hWown : P.ownBits 2=true) (hSown : P.ownBits 4=true)
    (hWD : Seven.SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center))
    (hDS : Seven.SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) : False := by
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  let d := P.diagonalAngle
  have hWphase : P.phase 2=Real.pi-v := by
    have hc : cardinalCenter (matchingCardinal 2)=Real.pi := rfl
    rw [P.phase_from_deviation 2,hc]
    dsimp [v]
    ring
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hwneg := canonical_own_west_negative P hWown
  have hv : 0≤v ∧ v≤2/3 := by
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hs : -5/8≤ s ∧ s≤2/3 :=
    ⟨P.helper_windows.2.2.2.1.le,P.helper_windows.2.2.2.2.le⟩
  have hd : 1/2≤d ∧ d≤Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hqs : 1/2≤Real.pi/2+s-d := by
    have hh := DS_Dsecondary_gap_gt_half P hDS
    rw [hDphase,hSphase] at hh
    linarith
  have hpositive := double_own_secondary_gap_positive hv hs hd hqs
    (P.contained 2) (P.contained 4) P.box
  have hnegative := double_own_secondary_frozen_nonpositive
    (by simpa only [hWphase] using P.own_separator 2 hWown)
    (by simpa only [hSphase] using P.own_separator 4 hSown)
    (by simpa only [P.square_def,hWphase,hDphase] using hWD)
    (by simpa only [P.square_def,hDphase,hSphase] using hDS)
  exact not_lt_of_ge hnegative hpositive

end SquaresInCircles.Six.Analytic
