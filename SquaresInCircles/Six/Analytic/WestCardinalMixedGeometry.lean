module
public import SquaresInCircles.Six.Analytic.WestCardinalMixedSupport

@[expose] public section

/-!
# Exclude the missing-west mixed case when both wings are cardinal

The five displayed inequalities are the actual CW, CD, CS, WD and DS
separators in their signed side frames. The common central coordinates are
retained until their nonnegative force is bounded. The W cap support uses its
proved slope condition; D and S use genuine far-vertex support. This closes
one central-bit case of MissingWestWing, not its three remaining bit cases.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCardinalMixed
open Normalization

/-- Five actual scalar separators contradict the positive reduced stress. -/
theorem scalar_separators_impossible {v d s aw bw ad bd aS bS cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart aS |bS|) (hcx : cx ≤ c0) (hcy : cy ≤ c0)
    (hv : 0 ≤ v ∧ v ≤ 2/5) (hd : 3/5 ≤ d ∧ d ≤ Real.pi/4)
    (hq : 1 ≤ d+v) (hs : d-Real.pi/4 ≤ s ∧ s ≤ 2/5)
    (hCW : 1/2+angularWidth v ≤ aw*Real.cos v+bw*Real.sin v+cx)
    (hCD : 1/2+angularWidth d ≤ ad+cx*Real.cos d+cy*Real.sin d)
    (hCS : 1/2+angularWidth s ≤ aS*Real.cos s-bS*Real.sin s+cy)
    (hWD : 1/2+angularWidth (d+v) ≤ aw*Real.sin (d+v)-bw*Real.cos (d+v)+bd)
    (hDS : 1/2+angularWidth (Real.pi/2+s-d) ≤
      ad*Real.sin (Real.pi/2+s-d)-bd*Real.cos (Real.pi/2+s-d)+bS) : False := by
  let r := Real.pi/2+s-d
  have hr : 0 ≤ r ∧ r ≤ Real.pi/2 := by
    dsimp [r]
    constructor <;> linarith [hs.1,hs.2,hd.1,Real.pi_pos]
  have hsabs : |s| ≤ 2/5 := by
    apply abs_le.mpr
    constructor <;> linarith [hs.1,hs.2,hd.1,Real.pi_lt_d2]
  have hc : 0 ≤ Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have ht := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hd.1])
    (by linarith [hd.2,Real.pi_pos])
  have hcx' : cx ≤ 113/1000 := by dsimp [c0] at hcx; linarith [rho0_upper]
  have hcy' : cy ≤ 113/1000 := by dsimp [c0] at hcy; linarith [rho0_upper]
  have hX := mul_nonneg (sub_nonneg.mpr hcx')
    (show 0 ≤ 9/40+(3/25)*Real.cos d by linarith)
  have hY := mul_nonneg (sub_nonneg.mpr hcy')
    (show 0 ≤ 1/4+(3/25)*Real.sin d by linarith)
  have hcenter : cx*(9/40+(3/25)*Real.cos d)+cy*(1/4+(3/25)*Real.sin d) ≤
      centralUpper d := by
    dsimp [centralUpper]
    nlinarith only [hX,hY]
  have hweighted : thresholdSum v d s ≤
      aw*wU v d+bw*wV v d+ad*dU r+bd*dV r+aS*sU s+bS*sV s+
        cx*(9/40+(3/25)*Real.cos d)+cy*(1/4+(3/25)*Real.sin d) := by
    dsimp [thresholdSum,wU,wV,dU,dV,sU,sV,r]
    linear_combination (9/40)*hCW+(3/25)*hCD+(1/4)*hCS+(9/40)*hWD+(9/50)*hDS
  have hw := west_center_support hW hv hd.2 hq
  have hd' := diagonal_center_support hD hr
  have hs' := south_center_support hS hsabs
  have hdefect : defect v d s ≤ 0 := by
    dsimp [defect]
    change thresholdSum v d s-centralUpper d-(1113/1000)*wU v d-
      ((1689/1000)*dRoot r-(dU r+dV r)/2)-
      ((1689/1000)*sRoot s-(sU s+sV s)/2) ≤ 0
    linarith only [hweighted,hcenter,hw,hd',hs']
  linarith [defect_positive hv hd hq hs]

end SquaresInCircles.Six.Analytic.WestCardinalMixed

namespace SquaresInCircles.Six.Analytic
open Normalization

/-- The actual mixed source combination (6,6) is impossible when W and S are
both cardinal. The E/N bits are unrestricted. -/
theorem missing_west_cardinal_cardinal_impossible {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false)
    (hmissing : MissingWestWing P) : False := by
  let v := -P.helperAngle 2
  let d := P.diagonalAngle
  let s := P.helperAngle 4
  have hw := abs_lt.mp (P.cardinal_angle 2 hW)
  have hs0 := abs_lt.mp (P.cardinal_angle 4 hS)
  have hwestnegative := hmissing.west_lt_neg_three_fourteenths
  have hv : 0 ≤ v ∧ v ≤ 2/5 := by
    dsimp [v]
    constructor <;> linarith
  have hd : 3/5 ≤ d ∧ d ≤ Real.pi/4 :=
    ⟨(hmissing.cardinal_diagonal_gt_three_fifths hW).le,P.diagonal_angle_range.2⟩
  have hs : d-Real.pi/4 ≤ s ∧ s ≤ 2/5 :=
    ⟨(hmissing.cardinal_wedge hW).2.le,hs0.2.le⟩
  have hWphase : P.phase 2=Real.pi-v := by
    rw [P.phase_from_deviation 2]
    dsimp [v]
    ring
  have hDphase : P.phase 3=Real.pi+d := by
    dsimp [d,NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hq : 1 ≤ d+v := by
    have h := hmissing.one_radian_gap
    rw [hWphase,hDphase] at h
    linarith
  have hCW : 1/2+angularWidth v ≤
      P.radial 2*Real.cos v+P.transverse 2*Real.sin v+P.center.1 := by
    have h := P.cardinal_separator 2 hW
    change 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2)
      P.center.1 P.center.2 at h
    rw [hWphase] at h
    simp only [centralMargin,centerX,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCD : 1/2+angularWidth d ≤
      P.radial 3+P.center.1*Real.cos d+P.center.2*Real.sin d := by
    have h := P.own_separator 3 P.diagonal_own
    rw [hDphase] at h
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hCS : 1/2+angularWidth s ≤
      P.radial 4*Real.cos s-P.transverse 4*Real.sin s+P.center.2 := by
    have h := P.cardinal_separator 4 hS
    change 0 ≤ centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4)
      P.center.1 P.center.2 at h
    rw [hSphase] at h
    simp only [centralMargin,centerY,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,one_mul,neg_one_mul,zero_add,add_zero,abs_neg] at h
    dsimp [angularWidth]
    nlinarith only [h]
  have hWD : 1/2+angularWidth (d+v) ≤
      P.radial 2*Real.sin (d+v)-P.transverse 2*Real.cos (d+v)+P.transverse 3 := by
    have h := hmissing.from_diagonal
    change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at h
    rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right,
      hWphase,hDphase] at h
    rw [show (Real.pi+d)-(Real.pi-v)=d+v by ring] at h
    linarith only [h]
  have hDS : 1/2+angularWidth (Real.pi/2+s-d) ≤
      P.radial 3*Real.sin (Real.pi/2+s-d)-P.transverse 3*Real.cos (Real.pi/2+s-d)+
        P.transverse 4 := by
    have h := hmissing.south_wing
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at h
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_right,
      hDphase,hSphase] at h
    rw [show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2+s-d by ring] at h
    linarith only [h]
  exact WestCardinalMixed.scalar_separators_impossible (P.contained 2) (P.contained 3)
    (P.contained 4) P.box.1.2 P.box.2.2 hv hd hq hs hCW hCD hCS hWD hDS

/-- In the both-cardinal bit case the west candidate inequality is automatic. -/
theorem DW_candidate_of_cardinal_wings {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=false) (hS : P.ownBits 4=false) :
    Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 2)) (sub (P.square 3).center (P.square 2).center) := by
  by_contra hnot
  exact missing_west_cardinal_cardinal_impossible P hW hS (missing_west_of_failure P hnot)

/-- A remaining missing-west configuration must use at least one OWN wing. -/
theorem MissingWestWing.some_own_wing {R : ℝ} {P : NormalizedPacking R}
    (h : MissingWestWing P) : P.ownBits 2=true ∨ P.ownBits 4=true := by
  cases hw : P.ownBits 2
  · cases hs : P.ownBits 4
    · exact False.elim (missing_west_cardinal_cardinal_impossible P hw hs h)
    · exact Or.inr hs
  · exact Or.inl hw

end SquaresInCircles.Six.Analytic
