module

public import SquaresInCircles.Six.Separators.SmallAngle
public import SquaresInCircles.Six.Separators.SouthPair
public import SquaresInCircles.Six.Separators.WingCosts
public import SquaresInCircles.Six.Normalization.PinAxes

/-!
# Six squares: the walls and the missing wings

In the model W and D are separated along the secondary axis of W, and D and S
along that of S: these are the two wings. A separation along the secondary axis
of D needs a phase gap above `π/4`, by the bound on the projection of a square
that avoids the core and `|b_D| < 9/40`: so `w < d - π/4` if W and D are
separated that way, and `s > d - π/4` if D and S are. The two pairs are never
both separated along the secondary axis of D: with weight one on C–W, C–S, W–D
and D–S the two forces on D cancel, and the remaining gap is positive in each of
the four cases for the separators of W and S from C, by the costs of the wings.
As each pair is separated along a secondary axis, if a wing fails the pair is
separated along the secondary axis of D, and the other pair along its wing: the
wing is missing, and the angle of its square lies beyond the wall.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- A separation of W and D along the secondary axis of D needs a phase gap
above `π/4`. -/
theorem westDiagonal_gap_gt_quarter {R : ℝ} (P : NormalizedPacking R)
    (hsep : SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    Real.pi/4<P.phase 3-P.phase 2 := by
  by_contra! hsmall
  have hbound := diagonal_secondary_excluded (P.contained 2) (P.avoidsCore 2)
    ⟨sub_nonneg.mpr P.primary_order.2.2.1.le,hsmall⟩
    ((le_abs_self _).trans_lt (normalized_diagonal_transverse_small P))
  change _≤frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right] at hsep
  linarith

/-- A separation of D and S along the secondary axis of D needs a phase gap
above `π/4`. -/
theorem diagonalSouth_gap_gt_quarter {R : ℝ} (P : NormalizedPacking R)
    (hsep : SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    Real.pi/4<P.phase 4-P.phase 3 := by
  by_contra! hsmall
  have hbound := diagonal_secondary_excluded (b := -P.transverse 4)
    (by simpa only [abs_neg] using P.contained 4)
    (by simpa only [abs_neg] using P.avoidsCore 4)
    ⟨sub_nonneg.mpr P.primary_order.2.2.2.1.le,hsmall⟩
    ((neg_le_abs _).trans_lt (normalized_diagonal_transverse_small P))
  change _≤frameY (P.square 3) (sub (P.square 4).center (P.square 3).center) at hsep
  rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_left] at hsep
  linarith

/-- In angles: a separation of W and D along the secondary axis of D gives
`w < d - π/4`. -/
theorem westDiagonal_wall {R : ℝ} (P : NormalizedPacking R)
    (hsep : SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    P.deviation 2<P.diagonalAngle-Real.pi/4 := by
  have h := westDiagonal_gap_gt_quarter P hsep
  have hw : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  rw [hw,show P.phase 3=Real.pi+P.diagonalAngle by
    dsimp [NormalizedPacking.diagonalAngle]; ring] at h
  linarith

/-- In angles: a separation of D and S along the secondary axis of D gives
`s > d - π/4`. -/
theorem diagonalSouth_wall {R : ℝ} (P : NormalizedPacking R)
    (hsep : SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) :
    P.diagonalAngle-Real.pi/4<P.deviation 4 := by
  have h := diagonalSouth_gap_gt_quarter P hsep
  have hs : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  rw [hs,show P.phase 3=Real.pi+P.diagonalAngle by
    dsimp [NormalizedPacking.diagonalAngle]; ring] at h
  linarith

/-! ### No double separation at D -/

/-- The force of the separation from C on W or S in its frame: `(1, 0)` along
its own axis, `(cos t, -sin t)` along the side of C. -/
def wingBaseX (own : Bool) (t : ℝ) : ℝ := if own then 1 else Real.cos t
def wingBaseY (own : Bool) (t : ℝ) : ℝ := if own then 0 else -Real.sin t

/-- The threshold sum minus the works of the forces on W, S and C, when W–D and
D–S are both separated along the secondary axis of D; `wo` and `so` record
whether W and S are separated from C along their own axes. -/
def doubleSecondaryGap (wo so : Bool) (w s d aw bw aS bS cx cy : ℝ) : ℝ :=
  2+angularWidth w+angularWidth s+angularWidth (d-w)+angularWidth (Real.pi/2+s-d)-
    ((wingBaseX wo w+Real.sin (d-w))*aw+(wingBaseY wo w-Real.cos (d-w))*bw)-
    ((wingBaseX so s+Real.sin (Real.pi/2+s-d))*aS+
      (wingBaseY so s+Real.cos (Real.pi/2+s-d))*bS)-
    (((if wo then Real.cos w else 1)-(if so then Real.sin s else 0))*cx+
      ((if wo then Real.sin w else 0)+(if so then Real.cos s else 1))*cy)

/-- The sum of the four separating inequalities: the gap is nonpositive,
whichever separators W and S have from C. -/
lemma doubleSecondaryGap_nonpositive (wo so : Bool) {w s d aw bw ad bd aS bS cx cy : ℝ}
    (hCW : 0≤centralMargin (if wo then .own else .west) (Real.pi+w) aw bw cx cy)
    (hCS : 0≤centralMargin (if so then .own else .south) (3*Real.pi/2+s) aS bS cx cy)
    (hWD : SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center))
    (hDS : SAT.threshold (orientedSquare (Real.pi+d) ad bd)
        (orientedSquare (3*Real.pi/2+s) aS bS)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (3*Real.pi/2+s) aS bS).center
          (orientedSquare (Real.pi+d) ad bd).center)) :
    doubleSecondaryGap wo so w s d aw bw aS bS cx cy≤0 := by
  have e1 : Real.cos (Real.pi+w)=-Real.cos w := by rw [add_comm]; exact Real.cos_add_pi w
  have e2 : Real.sin (Real.pi+w)=-Real.sin w := by rw [add_comm]; exact Real.sin_add_pi w
  have e3 : Real.cos (3*Real.pi/2+s)=Real.sin s := by
    rw [Real.cos_add,south_cos,south_sin]; ring
  have e4 : Real.sin (3*Real.pi/2+s)=-Real.cos s := by
    rw [Real.sin_add,south_cos,south_sin]; ring
  have hw : angularWidth (Real.pi+w)=angularWidth w := by
    simp [angularWidth,e1,e2,abs_neg]
  have hs : angularWidth (3*Real.pi/2+s)=angularWidth s := by
    simp [angularWidth,Real.cos_add,Real.sin_add,south_cos,south_sin,abs_neg,add_comm]
  change _≤frameY (orientedSquare (Real.pi+d) ad bd) _ at hWD
  change _≤frameY (orientedSquare (Real.pi+d) ad bd) _ at hDS
  rw [oriented_pair_threshold,pair_frameY_right,
    show (Real.pi+d)-(Real.pi+w)=d-w by ring] at hWD
  rw [oriented_pair_threshold,pair_frameY_left,
    show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2+s-d by ring] at hDS
  cases wo <;> cases so
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,centralMargin,centralNormal,
    centerX,centerY,hw,hs,e1,e2,e3,e4] at hCW hCS
  all_goals dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  all_goals nlinarith only [hCW,hCS,hWD,hDS]

lemma south_relative_width (s d : ℝ) : angularWidth (Real.pi/2+s-d)=angularWidth (d-s) := by
  rw [show Real.pi/2+s-d=Real.pi/2-(d-s) by ring,angularWidth_half_pi_sub]

/-- Both wings along the sides of C: their forces have lengths
`2 cos (π/4 - d/2)` and `2 cos (d/2)`, which sum to at most `4 cos (π/8)`. -/
lemma doubleSecondaryGap_pos_side_side {w s d aw bw aS bS cx cy : ℝ}
    (hw : |w|≤2/5) (hs : |s|≤2/5) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap false false w s d aw bw aS bS cx cy := by
  have hWwork := west_cardinal_secondary_work (w := w) hW hd
  have hSwork := south_cardinal_secondary_work (s := s) hS hd
  have hWwidth := cardinal_width_triangle hw hd
  have hSwidth := cardinal_width_triangle hs hd
  have hlength := radial_length_sum_bound d
  have hwidth := high_diagonal_width_lower hd
  have hcenter : cx+cy≤0.226 := by linarith [hc.1.2,hc.2.2,c0_bounds.2]
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [south_relative_width]
  rw [angularWidth_eq (x := d) ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_pos]⟩]
    at hWwidth hSwidth
  nlinarith only [hWwork,hSwork,hWwidth,hSwidth,hlength,hwidth,hcenter]

/-- W on its own axis and S along the south side of C. -/
lemma doubleSecondaryGap_pos_own_side {v s d aw bw aS bS cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hs : |s|≤2/5) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap true false (-v) s d aw bw aS bS cx cy := by
  have hW' : ContainedChart aw |-bw| := by simpa only [abs_neg] using hW
  have hq : 1/2≤d+v ∧ d+v≤Real.pi-1/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hWcost := secondary_cost_affine_lower hW' hq
  have hSwork := south_cardinal_secondary_work (s := s) hS hd
  have hSwidth := cardinal_width_triangle hs hd
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show v∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hcentral := coarse_central_work hc hcos
    (show 0≤1-Real.sin v by linarith [Real.sin_le_one v]) le_rfl le_rfl
  have hwing := ownWingCost_lower hv
  have hdepth := south_mixed_depth_lower hd
  have hvwidth : angularWidth (-v)=(Real.cos v+Real.sin v)/2 := by
    simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin]
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [Real.cos_neg,Real.sin_neg,sub_neg_eq_add,hvwidth,south_relative_width]
  rw [angularWidth_eq (x := d) ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_pos]⟩] at hSwidth
  dsimp [ownWingCost,southMixedDepth] at hwing hdepth
  nlinarith only [hWcost,hSwork,hSwidth,hcentral,hwing,hdepth,trig_bracket_two_thirds.1,
    trig_bracket_two_thirds.2.2.1]

/-- W along the west side of C and S on its own axis. -/
lemma doubleSecondaryGap_pos_side_own {w s d aw bw aS bS cx cy : ℝ}
    (hw : |w|≤2/5) (hs : -5/8≤ s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hqs : 1/2≤Real.pi/2+s-d)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap false true w s d aw bw aS bS cx cy := by
  have hq : 1/2≤Real.pi/2+s-d ∧ Real.pi/2+s-d≤Real.pi-1/2 :=
    ⟨hqs,by linarith [hs.2,hd.1,Real.pi_gt_d2]⟩
  have hScost := secondary_cost_folded_lower hS hq
  have he : foldedSecondaryAngle (Real.pi/2+s-d)=Real.pi/2-|s-d| := by
    dsimp [foldedSecondaryAngle]
    congr 2
    ring
  rw [he] at hScost
  have hWwork := west_cardinal_secondary_work (w := w) hW hd
  have hWwidth := cardinal_width_triangle hw hd
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show s∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hcentral := coarse_central_work hc
    (show 0≤1-Real.sin s by linarith [Real.sin_le_one s]) hcos le_rfl le_rfl
  have hreserve := west_cardinal_own_south_reserve hs hd
  have hswidth : angularWidth s=(Real.cos s+|Real.sin s|)/2 := by
    rw [angularWidth,abs_of_nonneg hcos]
  rw [angularWidth_eq (x := d) ⟨by linarith [hd.1],by linarith [hd.2,Real.pi_pos]⟩] at hWwidth
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [hswidth]
  dsimp [westMixedConstant,ownWingPotential] at hreserve
  nlinarith only [hScost,hWwork,hWwidth,hcentral,hreserve]

/-- Both wings on their own axes: the two angles `d + v` and `π/2 + s - d` of
the wings with D sum to `π/2 + v + s`, so `d` drops out of their costs. -/
lemma doubleSecondaryGap_pos_own_own {v s d aw bw aS bS cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hs : -5/8≤ s ∧ s≤2/3)
    (hd : 1/2≤d ∧ d≤Real.pi/4) (hqs : 1/2≤Real.pi/2+s-d)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap true true (-v) s d aw bw aS bS cx cy := by
  have hW' : ContainedChart aw |-bw| := by simpa only [abs_neg] using hW
  have hqW : 1/2≤d+v ∧ d+v≤Real.pi-1/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hqS : 1/2≤Real.pi/2+s-d ∧ Real.pi/2+s-d≤Real.pi-1/2 :=
    ⟨hqs,by linarith [hs.2,hd.1,Real.pi_gt_d2]⟩
  have hcostW := secondary_cost_affine_lower hW' hqW
  have hcostS := secondary_cost_affine_lower hS hqS
  have htv := small_angle (show |v|≤2/3 by rw [abs_of_nonneg hv.1]; exact hv.2)
  have hts := small_angle (abs_le.mpr ⟨by linarith [hs.1],hs.2⟩)
  have hcosv : 0≤Real.cos v := by linarith [htv.1]
  have hcoss : 0≤Real.cos s := by linarith [hts.1]
  have hsinv := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hX : 0≤Real.cos v-Real.sin s := by linarith [(abs_le.mp hts.2).2,htv.1]
  have hY : 0≤Real.cos s-Real.sin v := by linarith [(abs_le.mp htv.2).2,hts.1]
  have hcentral := coarse_central_work hc hX hY le_rfl le_rfl
  have hvline := ownWingCost_lower hv
  have hvwidth : angularWidth (-v)=(Real.cos v+Real.sin v)/2 := by
    simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hcosv,
      abs_of_nonneg hsinv]
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [Real.cos_neg,Real.sin_neg,sub_neg_eq_add,hvwidth]
  dsimp [ownWingCost] at hvline
  by_cases hs0 : 0≤ s
  · have hsins := Real.sin_nonneg_of_nonneg_of_le_pi hs0
      (by linarith [hs.2,Real.pi_gt_d2])
    have hsline := ownWingCost_lower ⟨hs0,hs.2⟩
    have hconstant : 0<2-2*(73/100)-(13/40)*Real.pi+2*ownWingCost (2/3) := by
      dsimp [ownWingCost]
      linarith [Real.pi_lt_d4,trig_bracket_two_thirds.1,trig_bracket_two_thirds.2.2.1]
    rw [show angularWidth s=(Real.cos s+Real.sin s)/2 by
      rw [angularWidth,abs_of_nonneg hcoss,abs_of_nonneg hsins]]
    dsimp [ownWingCost] at hsline hconstant
    nlinarith only [hcostW,hcostS,hcentral,hvline,hsline,hconstant]
  · have hsins : Real.sin s≤0 := by
      have h := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-s by linarith)
        (by linarith [hs.1,Real.pi_gt_d2])
      rw [Real.sin_neg] at h
      linarith
    have hsum := one_le_abs_cos_add_abs_sin s
    rw [abs_of_nonneg hcoss,abs_of_nonpos hsins] at hsum
    have hsline : 0.387≤0.387*(Real.cos s-Real.sin s)-(13/20)*s := by
      linarith [lt_of_not_ge hs0]
    have hconstant : 0<2-2*(73/100)-(13/40)*Real.pi+ownWingCost (2/3)+0.387 := by
      dsimp [ownWingCost]
      linarith [Real.pi_lt_d2,trig_bracket_two_thirds.1,trig_bracket_two_thirds.2.2.1]
    rw [show angularWidth s=(Real.cos s-Real.sin s)/2 by
      rw [angularWidth,abs_of_nonneg hcoss,abs_of_nonpos hsins]; ring]
    dsimp [ownWingCost] at hconstant
    nlinarith only [hcostW,hcostS,hcentral,hvline,hsline,hconstant]

/-- W–D and D–S are not both separated along the secondary axis of D. -/
theorem not_both_diagonal_secondary {R : ℝ} (P : NormalizedPacking R)
    (hWD : SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center))
    (hDS : SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)) : False := by
  have hWphase : P.phase 2=Real.pi+P.deviation 2 := P.phase_from_deviation 2
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  have hd : 1/2≤P.diagonalAngle ∧ P.diagonalAngle≤Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  have hs : -5/8≤P.deviation 4 ∧ P.deviation 4≤2/3 :=
    ⟨P.deviation_windows.2.2.2.1.le,P.deviation_windows.2.2.2.2.le⟩
  have hqS : 1/2≤Real.pi/2+P.deviation 4-P.diagonalAngle := by
    have h := diagonalSouth_gap_gt_quarter P hDS
    rw [hDphase,hSphase] at h
    linarith [Real.pi_gt_three]
  have hCW : 0≤centralMargin (if P.ownAxis 2 then .own else .west)
      (Real.pi+P.deviation 2) (P.radial 2) (P.transverse 2) P.center.1 P.center.2 := by
    have hmc : matchingCardinal 2=.west := rfl
    cases h : P.ownAxis 2
    · simpa only [hWphase,hmc,h,Bool.false_eq_true,ite_false] using P.cardinal_separator 2 h
    · simpa only [hWphase,h,ite_true] using P.own_separator 2 h
  have hCS : 0≤centralMargin (if P.ownAxis 4 then .own else .south)
      (3*Real.pi/2+P.deviation 4) (P.radial 4) (P.transverse 4) P.center.1 P.center.2 := by
    have hmc : matchingCardinal 4=.south := rfl
    cases h : P.ownAxis 4
    · simpa only [hSphase,hmc,h,Bool.false_eq_true,ite_false] using P.cardinal_separator 4 h
    · simpa only [hSphase,h,ite_true] using P.own_separator 4 h
  have hnegative := doubleSecondaryGap_nonpositive (P.ownAxis 2) (P.ownAxis 4) hCW hCS
    (by simpa only [P.square_def,hWphase,hDphase] using hWD)
    (by simpa only [P.square_def,hDphase,hSphase] using hDS)
  have hv : P.ownAxis 2=true → 0≤-P.deviation 2 ∧ -P.deviation 2≤2/3 := fun hW => by
    constructor <;> linarith [P.deviation_windows.2.2.1.1,own_west_negative P hW]
  cases hW : P.ownAxis 2 <;> cases hS : P.ownAxis 4 <;> rw [hW,hS] at hnegative
  · exact not_lt_of_ge hnegative (doubleSecondaryGap_pos_side_side
      (P.cardinal_angle 2 hW).le (P.cardinal_angle 4 hS).le hd (P.contained 2) (P.contained 4) P.box)
  · exact not_lt_of_ge hnegative (doubleSecondaryGap_pos_side_own
      (P.cardinal_angle 2 hW).le hs hd hqS (P.contained 2) (P.contained 4) P.box)
  · have h := doubleSecondaryGap_pos_own_side (hv hW) (P.cardinal_angle 4 hS).le hd
      (P.contained 2) (P.contained 4) P.box
    rw [neg_neg] at h
    exact not_lt_of_ge hnegative h
  · have h := doubleSecondaryGap_pos_own_own (hv hW) hs hd hqS
      (P.contained 2) (P.contained 4) P.box
    rw [neg_neg] at h
    exact not_lt_of_ge hnegative h

/-! ### Missing wings -/

/-- The west wing is missing: W and D are separated along the secondary axis of
D, and D and S along that of S. -/
structure MissingWestWing {R : ℝ} (P : NormalizedPacking R) : Prop where
  from_diagonal : SAT.threshold (P.square 2) (P.square 3)≤
    dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)
  south_wing : SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)

/-- The south wing is missing: W and D are separated along the secondary axis
of W, and D and S along that of D. -/
structure MissingSouthWing {R : ℝ} (P : NormalizedPacking R) : Prop where
  west_wing : SAT.threshold (P.square 2) (P.square 3)≤
    dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)
  from_diagonal : SAT.threshold (P.square 3) (P.square 4)≤
    dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)

/-- If W and D are not separated along the secondary axis of W, the west wing
is missing. -/
lemma missing_west_of_failure {R : ℝ} (P : NormalizedPacking R)
    (hW : ¬ SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center)) :
    MissingWestWing P := by
  obtain ⟨k,hk,hchoice⟩ := westDiagonal_secondary P
  have hD : SAT.threshold (P.square 2) (P.square 3)≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center) := by
    rcases hchoice with rfl | rfl
    · exact False.elim (hW hk)
    · exact hk
  rcases south_secondary_choice P with h | h
  · exact False.elim (not_both_diagonal_secondary P hD h)
  · exact ⟨hD,h⟩

/-- If D and S are not separated along the secondary axis of S, the south wing
is missing. -/
lemma missing_south_of_failure {R : ℝ} (P : NormalizedPacking R)
    (hS : ¬ SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)) :
    MissingSouthWing P := by
  have hD : SAT.threshold (P.square 3) (P.square 4)≤
      dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center) := by
    rcases south_secondary_choice P with h | h
    · exact h
    · exact False.elim (hS h)
  obtain ⟨k,hk,hchoice⟩ := westDiagonal_secondary P
  rcases hchoice with rfl | rfl
  · exact ⟨hk,hD⟩
  · exact False.elim (not_both_diagonal_secondary P hk hD)

lemma MissingWestWing.phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.deviation 2<P.diagonalAngle-Real.pi/4 :=
  westDiagonal_wall P h.from_diagonal

lemma MissingSouthWing.phase_wall {R : ℝ} {P : NormalizedPacking R}
    (h : MissingSouthWing P) : P.diagonalAngle-Real.pi/4<P.deviation 4 :=
  diagonalSouth_wall P h.from_diagonal

end SquaresInCircles.Six
