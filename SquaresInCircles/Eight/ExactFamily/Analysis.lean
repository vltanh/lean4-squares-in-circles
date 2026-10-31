module

public import SquaresInCircles.Common.Analysis
public import SquaresInCircles.Eight.ExactFamily.Generated.LocalStationaryBounds
public import SquaresInCircles.Eight.ExactFamily.CriticalHessian

/-!
# Eight squares: the stationary zero

For each squared radius `q` in `[qMinus, Q0]` the defect `F(q, ·, ·)` of the chain, as a function
of the position `y` and the half-angle tangent `z` of the tilt, is strongly convex on the fixed
compact rectangle `poseBox`: circle curvatures and a shear of the position/tilt coordinates
bound the shifted Hessian, giving curvature `1/4` in both coordinates
(`familyYY_bounds`, `hessian_data`, `family_strong_convex`). Its minimum over the rectangle is attained
at an interior point (`minimum_interior`), where both partial derivatives vanish
(`minimizingPose_stationary`). Differentiating the circle equations in the squared radius bounds
`F_q` between `-4` and `-3` (`family_q_bound`). The minimum value therefore decreases in `q` with
slope between `3` and `4` (`minimum_radius_difference`), so it is continuous, and it is positive at `qMinus` and negative at
`Q0` (`minimum_endpoint_signs`). By the intermediate value theorem it vanishes at exactly one
`qStar` (`unique_minimum_zero`), so `F`, `F_y` and `F_z` vanish at `(qStar, sharpPose)`
(`sharpPose_value`, `sharpPose_stationary`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated

abbrev Pose := ℝ × ℝ
def poseBox : Set Pose := Icc (-(937/1000)) (-(179/200)) ×ˢ Icc (1/20) (81/1000)
def tiltBox : Set ℝ := Icc (1/20) (81/1000)
def radiusBox : Set ℝ := Icc (7831/2000) (9789/2500)
/-- A short decimal trial suffices for existence and interiority of the minimum. -/
def trial : Pose := (-0.92066,0.0619)

def familyValue (q : ℝ) (p : Pose) : ℝ := FFormula.eval ![q,p.1,p.2]
def familyY (q : ℝ) (p : Pose) : ℝ := FyFormula.eval ![q,p.1,p.2]
def familyZ (q : ℝ) (p : Pose) : ℝ := FzFormula.eval ![q,p.1,p.2]
def familyQ (q : ℝ) (p : Pose) : ℝ := FqFormula.eval ![q,p.1,p.2]
def familyYY (q : ℝ) (p : Pose) : ℝ := FyyFormula.eval ![q,p.1,p.2]
def familyYZ (q : ℝ) (p : Pose) : ℝ := FyzFormula.eval ![q,p.1,p.2]
def familyZZ (q : ℝ) (p : Pose) : ℝ := FzzFormula.eval ![q,p.1,p.2]
/-- The height coordinate of the last corner, before choosing a position root. -/
def familyHeight (q : ℝ) (p : Pose) : ℝ := (radicalCoordinates q p.1 p.2).h₂

theorem local_mem {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    localBox.Mem ![q,p.1,p.2] := by
  have hq' : (7831/2000:ℝ) ≤ q ∧ q ≤ 9789/2500 := hq
  have hy : -(937/1000:ℝ) ≤ p.1 ∧ p.1 ≤ -(179/200) := hp.1
  have hz : (1/20:ℝ) ≤ p.2 ∧ p.2 ≤ 81/1000 := hp.2
  intro i; fin_cases i
  · norm_num [localBox,QInterval.Mem]
    exact hq'
  · norm_num [localBox,QInterval.Mem]
    constructor <;> linarith [hy.1, hy.2]
  · norm_num [localBox,QInterval.Mem]
    exact hz

theorem trial_mem : trial ∈ poseBox := by
  norm_num [trial,poseBox]

theorem family_continuous : Continuous (fun x : ℝ × Pose => familyValue x.1 x.2) := by
  simp only [familyValue,F_eval]
  unfold scalarF
  simp only [FFormula, Formula.eval]
  push_cast
  fun_prop (disch := intro x; positivity)

theorem family_continuous_pose (q : ℝ) : Continuous (familyValue q) := by
  have h := family_continuous.comp (continuous_const.prodMk continuous_id :
    Continuous fun p : Pose => (q,p))
  rw [Function.comp_def] at h
  simpa using h

private theorem family_value_regular {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    FFormula.RegularAt ![q,p.1,p.2] := by
  have hy := hp.1
  have hq' : 3.9155 ≤ q ∧ q ≤ 3.9156 := by
    constructor <;> linarith only [hq.1,hq.2]
  have h₁ : 0 < q-p.1^2 := by nlinarith only [hq'.1,hy.1,hy.2]
  have h₂ : 0 < q-(p.1+2)^2 := by nlinarith only [hq'.1,hy.1,hy.2]
  have hx₂l : 1.6 ≤ Real.sqrt (q-(p.1+2)^2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hq'.1,hy.1,hy.2])
  have hx₂u : Real.sqrt (q-(p.1+2)^2) ≤ 1.7 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith only [hq'.2,hy.1,hy.2]⟩
  have h₃ : 0 < q-(Real.sqrt (q-(p.1+2)^2)-3)^2 := by
    nlinarith only [hq'.1,hx₂l,hx₂u]
  have hy₃l : 1 ≤ Real.sqrt (q-(Real.sqrt (q-(p.1+2)^2)-3)^2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hq'.1,hx₂l,hx₂u])
  have hy₃u : Real.sqrt (q-(Real.sqrt (q-(p.1+2)^2)-3)^2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by nlinarith only [hq'.2,sq_nonneg (Real.sqrt (q-(p.1+2)^2)-3)]⟩
  have h₄ : 0 < q-(Real.sqrt (q-(Real.sqrt (q-(p.1+2)^2)-3)^2)-2)^2 := by
    nlinarith only [hq'.1,hy₃l,hy₃u]
  have hden : 1+p.2^2 ≠ 0 := ne_of_gt (halfAngle_den_pos p.2)
  have hf : FFormula.RegularAt ![q,p.1,p.2] := by
    norm_num [FFormula,Formula.RegularAt,Formula.eval,← sub_eq_add_neg,h₁,h₂,h₃,h₄,hden]
  exact hf

theorem family_regular {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    FFormula.RegularAt ![q,p.1,p.2] ∧
    FyFormula.RegularAt ![q,p.1,p.2] ∧ FzFormula.RegularAt ![q,p.1,p.2] := by
  have hf := family_value_regular hq hp
  refine ⟨hf,?_,?_⟩
  · rw [← Fy_diff]
    with_reducible exact Formula.RegularAt.diff (a:=FFormula) (env:=![q,p.1,p.2]) hf 1
  · rw [← Fz_diff]
    with_reducible exact Formula.RegularAt.diff (a:=FFormula) (env:=![q,p.1,p.2]) hf 2


section GeometricDerivatives
open FiveCornerGeometry

/-- The symbolic defect is the geometric circle-chain defect in `u = -y`. -/
theorem familyValue_geometric (q y z : ℝ) : familyValue q (y,z) =
    defect q (halfAngleCos z) (halfAngleSin z) (-y) := by
  norm_num [familyValue,Generated.FFormula,Formula.eval,defect,firstComponent,secondComponent,
    lowerRight,topRight,topLeft,topHeight,lowerHeight,lowerLeft,upper,
    halfAngleCos,halfAngleSin,neg_sq,sub_neg_eq_add,add_comm (2:ℝ) y,sub_sq_comm]
  ring_nf

theorem family_partial_y {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun y => familyValue q (y,p.2)) (familyY q p) p.1 := by
  have h := Formula.hasDerivAt_partial FFormula 1 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fy_diff] at h
  have hfun : (fun t => FFormula.eval (Function.update ![q,p.1,p.2] 1 t)) =
      (fun y => familyValue q (y,p.2)) := by
    funext y
    simp only [familyValue]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

theorem family_partial_z {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyValue q (p.1,z)) (familyZ q p) p.2 := by
  have h := Formula.hasDerivAt_partial FFormula 2 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fz_diff] at h
  have hfun : (fun t => FFormula.eval (Function.update ![q,p.1,p.2] 2 t)) =
      (fun z => familyValue q (p.1,z)) := by
    funext z
    simp only [familyValue]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

theorem family_partial_q {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun r => familyValue r p) (familyQ q p) q := by
  have h := Formula.hasDerivAt_partial FFormula 0 ![q,p.1,p.2] (family_regular hq hp).1
  rw [Fq_diff] at h
  have hfun : (fun t => FFormula.eval (Function.update ![q,p.1,p.2] 0 t)) =
      (fun r => familyValue r p) := by
    funext r
    simp only [familyValue]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

/-- The symbolic position derivative is the geometric derivative in `u = -y`. -/
theorem familyY_geometric (q y z : ℝ) : familyY q (y,z) =
    -2*positionHalf q (halfAngleCos z) (halfAngleSin z) (-y) := by
  norm_num [familyY,FyFormula,FFormula,Formula.diff,Formula.plus,Formula.minus,Formula.times,
    Formula.power,Formula.reciprocal,Formula.quotient,Formula.eval,
    positionHalf,firstComponent,
    secondComponent,slopeRatio,
    lowerRight,topRight,topLeft,
    topHeight,lowerHeight,lowerLeft,
    upper,halfAngleCos,halfAngleSin,neg_sq,sub_neg_eq_add,
    add_comm (2:ℝ) y]
  ring_nf

/-- The symbolic tilt derivative is angular speed times the geometric tilt derivative. -/
theorem familyZ_geometric (q y z : ℝ) : familyZ q (y,z) = (2/(1+z^2))*
    tiltFirst q (halfAngleCos z) (halfAngleSin z) (-y) := by
  have hden := ne_of_gt (halfAngle_den_pos z)
  norm_num [familyZ,FzFormula,FFormula,Formula.diff,Formula.plus,Formula.minus,Formula.times,
    Formula.power,Formula.reciprocal,Formula.quotient,Formula.eval,
    tiltFirst,firstComponent,secondComponent,firstTilt,secondTilt,
    lowerRight,topRight,topLeft,topHeight,lowerHeight,lowerLeft,upper,
    halfAngleCos,halfAngleSin,neg_sq,sub_neg_eq_add,add_comm (2:ℝ) y]
  field_simp [hden]
  ring_nf

/-- The position derivative has derivative `F_yy`. -/
theorem family_partial_yy {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun y => familyY q (y,p.2)) (familyYY q p) p.1 := by
  have hyy := Formula.hasDerivAt_partial FyFormula 1 ![q,p.1,p.2] (family_regular hq hp).2.1
  rw [Fyy_diff] at hyy
  have hfun : (fun t => FyFormula.eval (Function.update ![q,p.1,p.2] 1 t)) =
      (fun y => familyY q (y,p.2)) := by
    funext y
    simp only [familyY]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at hyy
  exact hyy

/-- The tilt derivative of the position derivative is `F_yz`. -/
theorem family_partial_yz {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyY q (p.1,z)) (familyYZ q p) p.2 := by
  have h := Formula.hasDerivAt_partial FyFormula 2 ![q,p.1,p.2] (family_regular hq hp).2.1
  rw [Fyz_diff] at h
  have hfun : (fun t => FyFormula.eval (Function.update ![q,p.1,p.2] 2 t)) =
      (fun z => familyY q (p.1,z)) := by
    funext z
    simp only [familyY]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

/-- The tilt derivative has derivative `F_zz`. -/
theorem family_partial_zz {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyZ q (p.1,z)) (familyZZ q p) p.2 := by
  have h := Formula.hasDerivAt_partial FzFormula 2 ![q,p.1,p.2] (family_regular hq hp).2.2
  rw [Fzz_diff] at h
  have hfun : (fun t => FzFormula.eval (Function.update ![q,p.1,p.2] 2 t)) =
      (fun z => familyZ q (p.1,z)) := by
    funext z
    simp only [familyZ]
    congr 1
    ext i; fin_cases i <;> simp [Function.update]
  rw [hfun] at h
  exact h

/-- Differentiate the geometric position equation; uniqueness of derivatives identifies `F_yy`. -/
theorem familyYY_geometric {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    familyYY q p = positionSecond q
      (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
  have hyy := family_partial_yy hq hp
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  have hs := local_smoothDomain hq hy hp.2
  have hg := ((position_second_deriv
    (c:=halfAngleCos p.2) (s:=halfAngleSin p.2) hs).comp p.1 (hasDerivAt_id' p.1).neg).neg
  have hsame : (fun y => -(2*positionHalf q
      (halfAngleCos p.2) (halfAngleSin p.2) (-y))) = (fun y => familyY q (y,p.2)) := by
    funext y
    rw [familyY_geometric]
    ring
  change HasDerivAt (fun y => -(2*positionHalf q
    (halfAngleCos p.2) (halfAngleSin p.2) (-y))) _ p.1 at hg
  rw [hsame] at hg
  have h := hyy.unique hg
  change familyYY q p = -(_ * -1) at h
  linarith only [h]

/-- Changing from the tilt angle to its half-angle tangent gives the mixed derivative. -/
theorem familyYZ_geometric {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    familyYZ q p = -(2/(1+p.2^2))*mixedSecond q
      (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
  have h := family_partial_yz (q:=q) (p:=p) hq hp
  have hg := ((mixed_angle_deriv q (-p.1) (2*Real.arctan p.2)).comp p.2
    (halfAngle_deriv p.2)).neg
  change HasDerivAt (fun z => -(2*positionHalf q
    (Real.cos (2*Real.arctan z)) (Real.sin (2*Real.arctan z)) (-p.1))) _ p.2 at hg
  have hsame : (fun z => -(2*positionHalf q (Real.cos (2*Real.arctan z))
      (Real.sin (2*Real.arctan z)) (-p.1))) = (fun z => familyY q (p.1,z)) := by
    funext z
    rw [(halfAngle_frame z).1,(halfAngle_frame z).2,familyY_geometric]
    ring
  rw [hsame,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at hg
  have he := h.unique hg
  calc familyYZ q p = -(mixedSecond q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)*
      (2/(1+p.2^2))) := he
    _ = _ := by ring

/-- The second tilt derivative includes the acceleration of the half-angle chart. -/
theorem familyZZ_geometric {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    familyZZ q p = (2/(1+p.2^2))^2*tiltSecond q
      (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)-
      (4*p.2/(1+p.2^2)^2)*tiltFirst q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
  have h := family_partial_zz (q:=q) (p:=p) hq hp
  have hT := (defect_angle_second_deriv q (-p.1) (2*Real.arctan p.2)).comp p.2
    (halfAngle_deriv p.2)
  have hg := (halfAngle_speed_deriv p.2).fun_mul hT
  change HasDerivAt (fun z => (2/(1+z^2))*tiltFirst q
    (Real.cos (2*Real.arctan z)) (Real.sin (2*Real.arctan z)) (-p.1)) _ p.2 at hg
  have hsame : (fun z => (2/(1+z^2))*tiltFirst q (Real.cos (2*Real.arctan z))
      (Real.sin (2*Real.arctan z)) (-p.1)) = (fun z => familyZ q (p.1,z)) := by
    funext z
    rw [(halfAngle_frame z).1,(halfAngle_frame z).2,familyZ_geometric]
  rw [hsame,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at hg
  have he := h.unique hg
  simp only [Function.comp_apply,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at he
  calc familyZZ q p = (-4*p.2/(1+p.2^2)^2)*
      tiltFirst q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)+
      (2/(1+p.2^2))*(tiltSecond q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)*
        (2/(1+p.2^2))) := he
    _ = _ := by ring

/-- The circle-chain radius derivative agrees with the symbolic partial derivative. -/
theorem familyQ_geometric {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    familyQ q p = radiusSlope q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
  have h := family_partial_q (q:=q) (p:=p) hq hp
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  have hs := local_smoothDomain hq hy hp.2
  have hd := defect_radius_deriv (c:=halfAngleCos p.2) (s:=halfAngleSin p.2)
    hs.r_pos hs.U_pos hs.Y_pos hs.w_pos
  have hfun : (fun r => defect r (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)) =
      (fun r => familyValue r p) := by
    funext r
    rw [familyValue_geometric r p.1 p.2]
  rw [hfun] at hd
  exact h.unique hd

/-- The position curvature follows from the circle equations and their geometric derivatives. -/
theorem familyYY_bounds {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    6 ≤ familyYY q p ∧ familyYY q p ≤ 9 := by
  rw [familyYY_geometric hq hp]
  apply local_positionSecond_bounds hq _ hp.2
  constructor <;> linarith only [hp.1.1,hp.1.2]

/-- The sheared Hessian bounds make the mixed derivative negative throughout the rectangle. -/
theorem familyYZ_neg {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    familyYZ q p < 0 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  obtain ⟨ha,_,_,hb,_,_⟩ := local_hessian_bounds hq hy hp.2
  have hm : 0 < mixedSecond q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
    linarith only [ha,hb]
  rw [familyYZ_geometric hq hp]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) hm

theorem familyHeight_geometric (q y z : ℝ) :
    familyHeight q (y,z) = -secondComponent q (halfAngleCos z) (halfAngleSin z) (-y) := by
  obtain ⟨_,_,_,_,hv,hw⟩ := radical_coordinate_values q y z
  dsimp only [familyHeight]
  rw [secondComponent,hv,hw]
  dsimp only [Coordinates.h₂,Coordinates.c,Coordinates.s]
  simp only [show (radicalCoordinates q y z).z = z from rfl]
  ring

theorem familyHeight_tilt_geometric (q y z : ℝ) :
    (radicalCoordinates q y z).h₂tilt =
      -secondTilt q (halfAngleCos z) (halfAngleSin z) (-y) := by
  obtain ⟨_,_,_,_,hv,hw⟩ := radical_coordinate_values q y z
  rw [secondTilt,hv,hw]
  dsimp only [Coordinates.h₂tilt,Coordinates.c,Coordinates.s]
  simp only [show (radicalCoordinates q y z).z = z from rfl]
  ring

theorem familyHeight_partial_y {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun y => familyHeight q (y,p.2))
      (-positionb q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)) p.1 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  have hs := local_smoothDomain hq hy hp.2
  have hd := (components_position_deriv (c:=halfAngleCos p.2) (s:=halfAngleSin p.2)
    hs.r_pos hs.U_pos hs.Y_pos hs.w_pos).2
  have h := (hd.comp p.1 (hasDerivAt_id' p.1).neg).neg
  change HasDerivAt (fun y => -secondComponent q
    (halfAngleCos p.2) (halfAngleSin p.2) (-y)) _ p.1 at h
  have he : (fun y => -secondComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-y)) =
      (fun y => familyHeight q (y,p.2)) := by funext y; exact (familyHeight_geometric q y p.2).symm
  rw [he] at h
  exact h.congr_deriv (by dsimp only [positionb,positionB]; ring)

theorem familyHeight_partial_z (q : ℝ) (p : Pose) :
    HasDerivAt (fun z => familyHeight q (p.1,z))
      ((2/(1+p.2^2))*(radicalCoordinates q p.1 p.2).h₂tilt) p.2 := by
  have h := ((secondComponent_angle_deriv q (-p.1) (2*Real.arctan p.2)).comp p.2
    (halfAngle_deriv p.2)).neg
  change HasDerivAt (fun z => -secondComponent q (Real.cos (2*Real.arctan z))
    (Real.sin (2*Real.arctan z)) (-p.1)) _ p.2 at h
  have he : (fun z => -secondComponent q (Real.cos (2*Real.arctan z))
      (Real.sin (2*Real.arctan z)) (-p.1)) = (fun z => familyHeight q (p.1,z)) := by
    funext z
    rw [(halfAngle_frame z).1,(halfAngle_frame z).2]
    exact (familyHeight_geometric q p.1 z).symm
  rw [he,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at h
  exact h.congr_deriv (by rw [familyHeight_tilt_geometric q p.1 p.2]; ring)

theorem familyYZ_bounds {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    -13 ≤ familyYZ q p ∧ familyYZ q p ≤ 0 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  obtain ⟨ha,ha',_,hb,hb',_⟩ := local_hessian_bounds hq hy hp.2
  have hB : 0 ≤ mixedSecond q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ∧
      mixedSecond q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ≤ 6.31 := by
    constructor <;> linarith only [ha,ha',hb,hb']
  have hg : 0 ≤ (2/(1+p.2^2):ℝ) ∧ 2/(1+p.2^2) ≤ 2 := by
    constructor
    · positivity
    · rw [div_le_iff₀ (halfAngle_den_pos p.2)]
      nlinarith only [sq_nonneg p.2]
  have hprod := mul_le_mul hg.2 hB.2 hB.1 (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨?_,(familyYZ_neg hq hp).le⟩
  rw [familyYZ_geometric hq hp]
  nlinarith only [hprod]

theorem familyHeight_derivative_bounds {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    (-0.7 ≤ -positionb q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ∧
      -positionb q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ≤ 0) ∧
    1.8 ≤ (2/(1+p.2^2))*(radicalCoordinates q p.1 p.2).h₂tilt := by
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  let a := radicalCoordinates q p.1 p.2
  obtain ⟨_,_,hUl,hUu,hYl,hYu,hwl,hwu,_⟩ := radical_coordinate_bounds hq hy hp.2
  have hU : 1.6414 ≤ a.x₂ ∧ a.x₂ ≤ 1.6691 := by constructor <;> linarith only [hUl,hUu]
  have hY : 1.4387 ≤ a.y₃ ∧ a.y₃ ≤ 1.4643 := by constructor <;> linarith only [hYl,hYu]
  have hw : 1.8974 ≤ -a.x₄ ∧ -a.x₄ ≤ 1.9049 := by constructor <;> linarith only [hwl,hwu]
  have hf := Coordinates.frame_bounds_of_coordinates hY hw hp.2
  have ht : 1.063 ≤ 2+p.1 ∧ 2+p.1 ≤ 1.105 := by constructor <;> linarith only [hy]
  have hV : 1.3309 ≤ -a.x₃ ∧ -a.x₃ ≤ 1.3586 := by
    dsimp only [Coordinates.x₃]; constructor <;> linarith only [hU]
  have hp₀ := positive_quotient_bounds (prod ht hV) (prod hU hY) (by norm_num) (by norm_num)
  have hp' : 0 ≤ (2+p.1)*(-a.x₃)/(a.x₂*a.y₃) ∧
      (2+p.1)*(-a.x₃)/(a.x₂*a.y₃) ≤ 0.637 := by constructor <;> linarith only [hp₀]
  have hb := prod hp' hf.2.1
  obtain ⟨_,hU',hV',hY',hv',hw'⟩ := radical_coordinate_values q p.1 p.2
  have he : positionb q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) =
      ((2+p.1)*(-a.x₃)/(a.x₂*a.y₃))*(a.c+a.s*a.y₄/a.x₄) := by
    rw [positionb,slopeRatio,positionB,hV',hU',hY',hv',hw']
    dsimp only [a,Coordinates.c,Coordinates.s]
    simp only [show (radicalCoordinates q p.1 p.2).z = p.2 from rfl]
    ring
  have hg : (1.98:ℝ) ≤ 2/(1+p.2^2) := by
    rw [le_div_iff₀ (halfAngle_den_pos p.2)]
    have hz₂ : p.2^2 ≤ (0.081:ℝ)^2 := by nlinarith only [hp.2.1,hp.2.2]
    nlinarith only [hz₂]
  have hge := mul_le_mul hg hf.2.2.1 (by norm_num : (0:ℝ) ≤ 0.93)
    (by linarith only [hg] : 0 ≤ 2/(1+p.2^2))
  constructor
  · rw [he]
    constructor <;> linarith only [hb]
  · linarith only [hge]

/-- The mixed derivative moves a position root at speed at least `2/3` in the tilt. -/
theorem familyYZ_upper {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    familyYZ q p ≤ -6 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  obtain ⟨ha,_,_,hb,_,_⟩ := local_hessian_bounds hq hy hp.2
  have hm : 3.07 ≤ mixedSecond q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
    linarith only [ha,hb]
  have hg : (1.98:ℝ) ≤ 2/(1+p.2^2) := by
    rw [le_div_iff₀ (halfAngle_den_pos p.2)]
    have hz₂ : p.2^2 ≤ (0.081:ℝ)^2 := by nlinarith only [hp.2.1,hp.2.2]
    nlinarith only [hz₂]
  have hprod := mul_le_mul hg hm (by norm_num : (0:ℝ) ≤ 3.07)
    (by linarith only [hg] : 0 ≤ 2/(1+p.2^2))
  rw [familyYZ_geometric hq hp]
  nlinarith only [hprod]

end GeometricDerivatives

/-- At fixed position, the position derivative decreases as the tilt increases. -/
theorem familyY_antitone_z {q y : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) :
    AntitoneOn (fun z => familyY q (y,z)) (Icc (1/20) (81/1000)) := by
  apply antiOn_of_hasDeriv_nonpos (d:=fun z => familyYZ q (y,z))
  · intro z hz
    exact (family_partial_yz (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).continuousAt.continuousWithinAt
  · intro z hz
    exact family_partial_yz (q:=q) (p:=(y,z)) hq ⟨hy,⟨hz.1.le,hz.2.le⟩⟩
  · intro z hz
    exact (familyYZ_neg (q:=q) (p:=(y,z)) hq ⟨hy,⟨hz.1.le,hz.2.le⟩⟩).le


theorem familyY_tilt_slope {q y z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200)))
    (h₀ : z₀ ∈ tiltBox) (h₁ : z₁ ∈ tiltBox) (hz : z₀ ≤ z₁) :
    -13*(z₁-z₀) ≤ familyY q (y,z₁)-familyY q (y,z₀) :=
  slope_lower_bound (f:=fun z => familyY q (y,z))
    (fun z hz => family_partial_yz (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩)
    (fun z hz => (familyYZ_bounds (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).1) h₀ h₁ hz

theorem familyHeight_position_slope {q y₀ y₁ z : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox)
    (h₀ : y₀ ∈ Icc (-(937/1000)) (-(179/200)))
    (h₁ : y₁ ∈ Icc (-(937/1000)) (-(179/200))) (hy : y₀ ≤ y₁) :
    -0.7*(y₁-y₀) ≤ familyHeight q (y₁,z)-familyHeight q (y₀,z) :=
  slope_lower_bound (f:=fun y => familyHeight q (y,z))
    (fun y hy => familyHeight_partial_y (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩)
    (fun y hy => (familyHeight_derivative_bounds (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).1.1) h₀ h₁ hy

theorem familyHeight_tilt_slope {q y z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200)))
    (h₀ : z₀ ∈ tiltBox) (h₁ : z₁ ∈ tiltBox) (hz : z₀ ≤ z₁) :
    1.8*(z₁-z₀) ≤ familyHeight q (y,z₁)-familyHeight q (y,z₀) :=
  slope_lower_bound (f:=fun z => familyHeight q (y,z)) (fun z _ => familyHeight_partial_z q (y,z))
    (fun z hz => (familyHeight_derivative_bounds (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).2) h₀ h₁ hz


theorem familyYY_derivative {q y z : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) (hz : z ∈ tiltBox) :
    HasDerivAt (fun r => familyY q (r,z)) (familyYY q (y,z)) y :=
  family_partial_yy (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩

theorem familyY_continuous_y {q z : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox) :
    ContinuousOn (fun y => familyY q (y,z)) (Icc (-(937/1000)) (-(179/200))) := by
  intro y hy
  exact (familyYY_derivative hq hy hz).continuousAt.continuousWithinAt

theorem familyY_slope {q z a b : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox)
    (ha : a ∈ Icc (-(937/1000)) (-(179/200)))
    (hb : b ∈ Icc (-(937/1000)) (-(179/200))) (hab : a ≤ b) :
    6*(b-a) ≤ familyY q (b,z)-familyY q (a,z) := by
  exact slope_lower_bound (f:=fun y => familyY q (y,z))
    (fun y hy => familyYY_derivative hq hy hz)
    (fun y hy => (familyYY_bounds (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).1) ha hb hab

/-- Opposite signs bracket every position root, by strict monotonicity. -/
theorem position_root_between {q y z a b : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200)))
    (ha : a ∈ Icc (-(937/1000)) (-(179/200)))
    (hb : b ∈ Icc (-(937/1000)) (-(179/200)))
    (hr : familyY q (y,z)=0) (hl : familyY q (a,z)<0) (hu : 0<familyY q (b,z)) :
    a < y ∧ y < b := by
  constructor
  · by_contra! h
    have hs := familyY_slope hq hz hy ha h
    linarith only [hs,hr,hl,h]
  · by_contra! h
    have hs := familyY_slope hq hz hb hy h
    linarith only [hs,hr,hu,h]


/-- Increasing tilt moves the position root to the right, at speed at most `13/6`.
This secant argument only uses the position equation and the mean value theorem. -/
theorem root_position_motion {q y₀ y₁ z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (h₀ : (y₀,z₀) ∈ poseBox) (h₁ : (y₁,z₁) ∈ poseBox) (hz : z₀ ≤ z₁)
    (hr₀ : familyY q (y₀,z₀)=0) (hr₁ : familyY q (y₁,z₁)=0) :
    y₀ ≤ y₁ ∧ 6*(y₁-y₀) ≤ 13*(z₁-z₀) := by
  have htilt := familyY_antitone_z hq h₀.1 h₀.2 h₁.2 hz
  have hy : y₀ ≤ y₁ := by
    by_contra! h
    have hs := familyY_slope hq h₁.2 h₁.1 h₀.1 h.le
    linarith only [htilt,hr₀,hr₁,hs,h]
  have hs := familyY_slope hq h₁.2 h₀.1 h₁.1 hy
  have ht := familyY_tilt_slope hq h₀.1 h₀.2 h₁.2 hz
  exact ⟨hy,by linarith only [hs,ht,hr₀,hr₁]⟩

/-- A tilt increase moves the position root by at least two thirds as much. -/
theorem root_position_lower {q y₀ y₁ z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (h₀ : (y₀,z₀) ∈ poseBox) (h₁ : (y₁,z₁) ∈ poseBox) (hz : z₀ ≤ z₁)
    (hr₀ : familyY q (y₀,z₀)=0) (hr₁ : familyY q (y₁,z₁)=0) :
    6*(z₁-z₀) ≤ 9*(y₁-y₀) := by
  have hy := (root_position_motion hq h₀ h₁ hz hr₀ hr₁).1
  have hs := slope_lower_bound (f:=fun y => -familyY q (y,z₀))
    (m:= -9) (fun y hy => (family_partial_yy (q:=q) (p:=(y,z₀)) hq ⟨hy,h₀.2⟩).neg)
    (fun y hy => by linarith only [(familyYY_bounds (q:=q) (p:=(y,z₀)) hq ⟨hy,h₀.2⟩).2])
    h₀.1 h₁.1 hy
  have ht := slope_lower_bound (f:=fun z => -familyY q (y₁,z))
    (m:=6) (fun z hz => (family_partial_yz (q:=q) (p:=(y₁,z)) hq ⟨h₁.1,hz⟩).neg)
    (fun z hz => by linarith only [familyYZ_upper (q:=q) (p:=(y₁,z)) hq ⟨h₁.1,hz⟩])
    h₀.2 h₁.2 hz
  linarith only [hs,ht,hr₀,hr₁]

/-- Height increases along the position roots: tilt gains at least `1.8`, while
position motion costs at most `0.7 * (13/6)`, per unit of tilt. -/
theorem root_height_slope {q y₀ y₁ z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (h₀ : (y₀,z₀) ∈ poseBox) (h₁ : (y₁,z₁) ∈ poseBox) (hz : z₀ ≤ z₁)
    (hr₀ : familyY q (y₀,z₀)=0) (hr₁ : familyY q (y₁,z₁)=0) :
    (17/60)*(z₁-z₀) ≤ familyHeight q (y₁,z₁)-familyHeight q (y₀,z₀) := by
  obtain ⟨hy,hmove⟩ := root_position_motion hq h₀ h₁ hz hr₀ hr₁
  have hp := familyHeight_position_slope hq h₁.2 h₀.1 h₁.1 hy
  have ht := familyHeight_tilt_slope hq h₀.1 h₀.2 h₁.2 hz
  linarith only [hmove,hp,ht]



/-- Circle-radius sensitivities give the decrease of the defect in the squared radius. -/
theorem family_q_bound {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    -4 ≤ familyQ q p ∧ familyQ q p ≤ -3 := by
  rw [familyQ_geometric hq hp]
  apply FiveCornerGeometry.local_radiusSlope_bounds hq _ hp.2
  constructor <;> linarith only [hp.1.1,hp.1.2]

theorem hessian_data {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    6 ≤ familyYY q p ∧
      0 < (familyYY q p-1/4)*(familyZZ q p-1/4)-(familyYZ q p)^2 := by
  refine ⟨(familyYY_bounds hq hp).1,?_⟩
  rw [familyYY_geometric hq hp,familyYZ_geometric hq hp,familyZZ_geometric hq hp]
  apply FiveCornerGeometry.local_halfAngle_hessian_pos hq _ hp.2
  constructor <;> linarith only [hp.1.1,hp.1.2]

theorem quadratic_form_bound {A B C : ℝ} (hA : 6 ≤ A)
    (hdet : 0 < (A-1/4)*(C-1/4)-B^2) (u v : ℝ) :
    (u^2+v^2)/4 ≤ A*u^2+2*B*u*v+C*v^2 := by
  have h := sq_nonneg ((A-1/4)*u+B*v)
  have h' := mul_nonneg hdet.le (sq_nonneg v)
  have heq : (A-1/4)*(A*u^2+2*B*u*v+C*v^2-(u^2+v^2)/4) =
      ((A-1/4)*u+B*v)^2+((A-1/4)*(C-1/4)-B^2)*v^2 := by ring
  have hp : 0 < A-1/4 := by linarith
  nlinarith

def segment (a b : Pose) (t : ℝ) : Pose :=
  ((1-t)*a.1+t*b.1,(1-t)*a.2+t*b.2)

theorem segment_mem {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : segment a b t ∈ poseBox := by
  exact (convex_Icc _ _).prod (convex_Icc _ _) ha hb
    (by linarith [ht.2]) ht.1 (by ring)

theorem segment_deriv (q : ℝ) (a b : Pose) (t : ℝ) :
    ∀ i : Fin 3, HasDerivAt (fun s => ![q,(segment a b s).1,(segment a b s).2] i)
      (![0,b.1-a.1,b.2-a.2] i) t := by
  intro i; fin_cases i
  · simpa using hasDerivAt_const t q
  · convert (((hasDerivAt_id' t).const_sub 1).mul_const a.1).fun_add
      ((hasDerivAt_id' t).mul_const b.1) using 1 <;> simp [segment]
    ring
  · convert (((hasDerivAt_id' t).const_sub 1).mul_const a.2).fun_add
      ((hasDerivAt_id' t).mul_const b.2) using 1 <;> simp [segment]
    ring

theorem family_segment_first {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => familyValue q (segment a b s))
      (familyY q (segment a b t)*(b.1-a.1)+familyZ q (segment a b t)*(b.2-a.2)) t := by
  have h := Formula.hasDerivAt_curve FFormula (segment_deriv q a b t)
    (family_regular hq (segment_mem ha hb ht)).1
  rw [Formula.directional_eq_partials] at h
  simpa [Fin.sum_univ_succ,Fq_diff,Fy_diff,Fz_diff,familyValue,familyY,familyZ] using h

theorem family_segment_second {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt
      (fun s => familyY q (segment a b s)*(b.1-a.1)+
        familyZ q (segment a b s)*(b.2-a.2))
      (familyYY q (segment a b t)*(b.1-a.1)^2+
        2*familyYZ q (segment a b t)*(b.1-a.1)*(b.2-a.2)+
        familyZZ q (segment a b t)*(b.2-a.2)^2) t := by
  have hreg := family_regular hq (segment_mem ha hb ht)
  have hy := Formula.hasDerivAt_curve FyFormula (segment_deriv q a b t) hreg.2.1
  have hz := Formula.hasDerivAt_curve FzFormula (segment_deriv q a b t) hreg.2.2
  rw [Formula.directional_eq_partials] at hy hz
  have h := (hy.mul_const (b.1-a.1)).add (hz.mul_const (b.2-a.2))
  convert h using 1
  · rfl
  · simp [Fin.sum_univ_succ,Fyy_diff,Fyz_diff,Fzz_diff,mixed_partials,
      familyYY,familyYZ,familyZZ]
    ring

theorem family_strong_convex {q : ℝ} (hq : q ∈ radiusBox)
    {a b : Pose} (ha : a ∈ poseBox) (hb : b ∈ poseBox) :
    familyValue q a+familyY q a*(b.1-a.1)+familyZ q a*(b.2-a.2)+
      ((b.1-a.1)^2+(b.2-a.2)^2)/8 ≤ familyValue q b := by
  have hcurv := curvature_tangent (l:=0) (u:=1) (x:=1) (t:=0)
    (f:=fun s => familyValue q (segment a b s))
    (d:=fun s => familyY q (segment a b s)*(b.1-a.1)+
      familyZ q (segment a b s)*(b.2-a.2))
    (dd:=fun s => familyYY q (segment a b s)*(b.1-a.1)^2+
      2*familyYZ q (segment a b s)*(b.1-a.1)*(b.2-a.2)+
      familyZZ q (segment a b s)*(b.2-a.2)^2)
    (κ:=((b.1-a.1)^2+(b.2-a.2)^2)/4)
    (by norm_num) (by norm_num)
    (fun s hs => family_segment_first hq ha hb hs)
    (fun s hs => family_segment_second hq ha hb hs)
    (fun s hs => by
      obtain ⟨hA,hdet⟩ := hessian_data hq (segment_mem ha hb hs)
      exact quadratic_form_bound hA hdet _ _)
  have h0 : segment a b 0 = a := by simp [segment]
  have h1 : segment a b 1 = b := by simp [segment]
  simp only [h0,h1] at hcurv
  linarith

theorem compact_poseBox : IsCompact poseBox := isCompact_Icc.prod isCompact_Icc

theorem minimum_exists (q : ℝ) :
    ∃ p ∈ poseBox, ∀ r ∈ poseBox, familyValue q p ≤ familyValue q r := by
  obtain ⟨p,hp,hmin⟩ := compact_poseBox.exists_isMinOn ⟨trial,trial_mem⟩
    (family_continuous_pose q).continuousOn
  exact ⟨p,hp,hmin⟩

def minimizingPose (q : ℝ) : Pose := Classical.choose (minimum_exists q)
def minimumValue (q : ℝ) : ℝ := familyValue q (minimizingPose q)

theorem minimizingPose_mem (q : ℝ) : minimizingPose q ∈ poseBox :=
  (Classical.choose_spec (minimum_exists q)).1

theorem minimumValue_le (q : ℝ) {p : Pose} (hp : p ∈ poseBox) :
    minimumValue q ≤ familyValue q p :=
  (Classical.choose_spec (minimum_exists q)).2 p hp

theorem trial_gradients {q : ℝ} (hq : q ∈ radiusBox) :
    |familyY q trial| ≤ 1/5000 ∧ |familyZ q trial| ≤ 1/2500 := by
  have hq' : (7831/2000:ℝ) ≤ q ∧ q ≤ 9789/2500 := hq
  have hY := trialFy_bound ![q,trial.1,trial.2] (by
    intro i; fin_cases i <;> norm_num [trialFyBox,QInterval.Mem,trial]
    exact hq')
  have hZ := trialFz_bound ![q,trial.1,trial.2] (by
    intro i; fin_cases i <;> norm_num [trialFzBox,QInterval.Mem,trial]
    exact hq')
  change (-1/5000:ℝ) ≤ familyY q trial ∧ familyY q trial ≤ 1/5000 at hY
  change (-1/2500:ℝ) ≤ familyZ q trial ∧ familyZ q trial ≤ 1/2500 at hZ
  exact ⟨abs_le.mpr ⟨by linarith [hY.1],hY.2⟩,abs_le.mpr ⟨by linarith [hZ.1],hZ.2⟩⟩

theorem minimum_interior {q : ℝ} (hq : q ∈ radiusBox) :
    -(937/1000) < (minimizingPose q).1 ∧ (minimizingPose q).1 < -(179/200) ∧
    1/20 < (minimizingPose q).2 ∧ (minimizingPose q).2 < 81/1000 := by
  have hmin := minimumValue_le q trial_mem
  have hcurv := family_strong_convex hq trial_mem (minimizingPose_mem q)
  obtain ⟨hy,hz⟩ := trial_gradients hq
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hdist : ((minimizingPose q).1-trial.1)^2+
      ((minimizingPose q).2-trial.2)^2 < 1/10000 := by
    dsimp [minimumValue] at hmin
    nlinarith [sq_nonneg ((minimizingPose q).1-trial.1+8*familyY q trial),
      sq_nonneg ((minimizingPose q).2-trial.2+8*familyZ q trial)]
  have hyclose : |(minimizingPose q).1-trial.1| < 1/100 := by
    rw [abs_lt]; constructor <;> nlinarith [sq_nonneg ((minimizingPose q).2-trial.2)]
  have hzclose : |(minimizingPose q).2-trial.2| < 1/100 := by
    rw [abs_lt]; constructor <;> nlinarith [sq_nonneg ((minimizingPose q).1-trial.1)]
  have hyc := abs_lt.mp hyclose
  have hzc := abs_lt.mp hzclose
  norm_num [trial] at hyc hzc
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem minimizingPose_stationary {q : ℝ} (hq : q ∈ radiusBox) :
    familyY q (minimizingPose q)=0 ∧ familyZ q (minimizingPose q)=0 := by
  have hp := minimizingPose_mem q
  obtain ⟨hyL,hyU,hzL,hzU⟩ := minimum_interior hq
  have hymin : IsMinOn (fun y => familyValue q (y,(minimizingPose q).2))
      (Icc (-(937/1000)) (-(179/200))) (minimizingPose q).1 := by
    intro y hy
    exact minimumValue_le q ⟨hy,hp.2⟩
  have hzmin : IsMinOn (fun z => familyValue q ((minimizingPose q).1,z))
      (Icc (1/20) (81/1000)) (minimizingPose q).2 := by
    intro z hz
    exact minimumValue_le q ⟨hp.1,hz⟩
  exact ⟨(hymin.isLocalMin (Icc_mem_nhds hyL hyU)).hasDerivAt_eq_zero
      (family_partial_y hq hp),
    (hzmin.isLocalMin (Icc_mem_nhds hzL hzU)).hasDerivAt_eq_zero
      (family_partial_z hq hp)⟩

theorem family_radius_difference {q r : ℝ} (hq : q ∈ radiusBox) (hr : r ∈ radiusBox)
    (hqr : q ≤ r) {p : Pose} (hp : p ∈ poseBox) :
    -4*(r-q) ≤ familyValue r p-familyValue q p ∧
      familyValue r p-familyValue q p ≤ -3*(r-q) := by
  have hanti := antiOn_of_hasDeriv_nonpos (l:=7831/2000) (u:=9789/2500)
    (f:=fun x => familyValue x p+3*x) (d:=fun x => familyQ x p+3)
    (by exact ((family_continuous.comp (continuous_id.prodMk continuous_const)).add
      (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx => by
      convert (family_partial_q ⟨hx.1.le,hx.2.le⟩ hp).fun_add
        ((hasDerivAt_id' x).const_mul 3) using 1; ring)
    (fun x hx => by linarith [(family_q_bound ⟨hx.1.le,hx.2.le⟩ hp).2])
  have hmono := monoOn_of_hasDeriv_nonneg (l:=7831/2000) (u:=9789/2500)
    (f:=fun x => familyValue x p+4*x) (d:=fun x => familyQ x p+4)
    (by exact ((family_continuous.comp (continuous_id.prodMk continuous_const)).add
      (continuous_const.mul continuous_id)).continuousOn)
    (fun x hx => by
      convert (family_partial_q ⟨hx.1.le,hx.2.le⟩ hp).fun_add
        ((hasDerivAt_id' x).const_mul 4) using 1; ring)
    (fun x hx => by linarith [(family_q_bound ⟨hx.1.le,hx.2.le⟩ hp).1])
  have h₁ := hanti hq hr hqr
  have h₂ := hmono hq hr hqr
  dsimp only at h₁ h₂
  constructor <;> linarith

theorem minimum_radius_difference {q r : ℝ} (hq : q ∈ radiusBox) (hr : r ∈ radiusBox)
    (hqr : q ≤ r) :
    -4*(r-q) ≤ minimumValue r-minimumValue q ∧
      minimumValue r-minimumValue q ≤ -3*(r-q) := by
  have h₁ := family_radius_difference hq hr hqr (minimizingPose_mem q)
  have h₂ := family_radius_difference hq hr hqr (minimizingPose_mem r)
  have h₃ := minimumValue_le r (minimizingPose_mem q)
  have h₄ := minimumValue_le q (minimizingPose_mem r)
  dsimp [minimumValue] at *
  constructor <;> linarith

theorem minimum_continuous : ContinuousOn minimumValue radiusBox := by
  have hlip : LipschitzWith (4:NNReal) (fun q : radiusBox => minimumValue q) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    rcases le_total (q:ℝ) (r:ℝ) with h | h
    · have hh := minimum_radius_difference q.property r.property h
      simp only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat]
      rw [abs_of_nonpos (by linarith : (q:ℝ)-(r:ℝ) ≤ 0)]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · have hh := minimum_radius_difference r.property q.property h
      simp only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat]
      rw [abs_of_nonneg (by linarith : 0 ≤ (q:ℝ)-(r:ℝ))]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  exact continuousOn_iff_continuous_domRestrict.mpr hlip.continuous

/-- Completing the tangent paraboloid bounds the minimum using any trial pose. -/
theorem minimum_lower_at {q : ℝ} (hq : q ∈ radiusBox) {p : Pose} (hp : p ∈ poseBox) :
    familyValue q p-2*(familyY q p)^2-2*(familyZ q p)^2 ≤ minimumValue q := by
  have h := family_strong_convex hq hp (minimizingPose_mem q)
  dsimp [minimumValue]
  nlinarith [sq_nonneg ((minimizingPose q).1-p.1+4*familyY q p),
    sq_nonneg ((minimizingPose q).2-p.2+4*familyZ q p)]

theorem minimum_trial_lower {q : ℝ} (hq : q ∈ radiusBox) :
    familyValue q trial-2*(familyY q trial)^2-2*(familyZ q trial)^2 ≤ minimumValue q :=
  minimum_lower_at hq trial_mem

theorem minimum_endpoint_signs :
    0 < minimumValue (7831/2000) ∧ minimumValue (9789/2500) < 0 := by
  have hL := lowerTest_bound ![7831/2000,trial.1,trial.2]
    (by intro i; fin_cases i <;> norm_num [lowerTestBox,QInterval.Mem,trial])
  have hU := upperTest_bound ![9789/2500,trial.1,trial.2]
    (by intro i; fin_cases i <;> norm_num [upperTestBox,QInterval.Mem,trial])
  have hcurv := minimum_trial_lower (q:=7831/2000) (by norm_num [radiusBox])
  obtain ⟨hy,hz⟩ := trial_gradients (q:=7831/2000) (by norm_num [radiusBox])
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hupper := minimumValue_le (9789/2500) trial_mem
  change (1/8000:ℝ) ≤ familyValue (7831/2000) trial ∧ _ at hL
  change _ ∧ familyValue (9789/2500) trial ≤ (-1/5000) at hU
  constructor <;> nlinarith

theorem unique_minimum_zero : ∃! q : ℝ, q ∈ radiusBox ∧ minimumValue q=0 := by
  have hs := minimum_endpoint_signs
  have hcont : ContinuousOn (fun q => -minimumValue q) radiusBox := minimum_continuous.neg
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc (by norm_num : (7831/2000:ℝ) ≤ 9789/2500)
    hcont ⟨show -minimumValue (7831/2000) ≤ 0 by linarith [hs.1],
      show 0 ≤ -minimumValue (9789/2500) by linarith [hs.2]⟩
  dsimp only at hzero
  refine ⟨q,⟨hq,by linarith⟩,?_⟩
  intro r hr
  rcases lt_trichotomy r q with h | h | h
  · have hb := (minimum_radius_difference hr.1 hq h.le).2
    linarith [hr.2]
  · exact h
  · have hb := (minimum_radius_difference hq hr.1 h.le).2
    linarith [hr.2]

def qStar : ℝ := Classical.choose unique_minimum_zero
def sharpPose : Pose := minimizingPose qStar

theorem qStar_mem : qStar ∈ radiusBox := (Classical.choose_spec unique_minimum_zero).1.1
theorem minimum_qStar : minimumValue qStar=0 := (Classical.choose_spec unique_minimum_zero).1.2
theorem sharpPose_stationary : familyY qStar sharpPose=0 ∧ familyZ qStar sharpPose=0 :=
  minimizingPose_stationary qStar_mem
theorem sharpPose_value : familyValue qStar sharpPose=0 := minimum_qStar

end SquaresInCircles.Eight.ExactFamily
