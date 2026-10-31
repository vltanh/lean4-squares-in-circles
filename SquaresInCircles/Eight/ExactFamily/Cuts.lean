module

public import SquaresInCircles.Eight.ExactFamily.Analysis
public import SquaresInCircles.Eight.ExactFamily.Weights

/-!
# Eight squares: geometric cut estimates and owner reserves

The cut margins follow from circle derivatives, force balance and coarse coordinate bounds.
Seven reserves follow from contact proportions and a margin that increases along the position
roots. The last two share one unnormalized cut. It decreases with position, and tangent
parabolas at the midpoint tilt bound it throughout the pose rectangle.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.ExactFamily
open Arithmetic Generated

/-! ### The reserve margin along the position roots -/

namespace FiveCornerGeometry

/-- The HE factor of reserve 5 after the ED/HE force balance. -/
def cutMargin (q c s u : ℝ) : ℝ :=
  (1057/1000)*(positionB q c s u*(topLeft q u/topHeight q u))+secondTilt q c s u

/-- The slope of the margin in the position coordinate `y = -u`. -/
def cutMarginPosition (q c s u : ℝ) : ℝ :=
  (1057/1000)*(s*slopeRatio q u*q/lowerLeft q u^3*(topLeft q u/topHeight q u)+
    positionB q c s u*((2-u)/(topRight q u*topHeight q u)+
      topLeft q u*slopeRatio q u/topHeight q u^2))+
    slopeRatio q u*(c*(lowerHeight q u/lowerLeft q u)-s)

/-- The tilt-angle derivative of the margin at fixed position. -/
def cutMarginAngle (q c s u : ℝ) : ℝ :=
  (1057/1000)*(-s+c*lowerHeight q u/lowerLeft q u)*(topLeft q u/topHeight q u)-
    c*lowerHeight q u+s*(lowerLeft q u-1)

theorem margin_position_deriv {q c s u : ℝ} (h : SmoothDomain q u) :
    HasDerivAt (cutMargin q c s) (-cutMarginPosition q c s u) u := by
  obtain ⟨_,_,dV,dY,dv,dw⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  have hb := dV.fun_div dY (ne_of_gt h.Y_pos)
  have he := (dv.const_mul (-s)).fun_sub ((dw.sub_const 1).const_mul c)
  have hd := (((positionB_deriv (c:=c) (s:=s) h).fun_mul hb).const_mul (1057/1000)).add he
  change HasDerivAt (cutMargin q c s) _ u at hd
  apply hd.congr_deriv
  dsimp only [cutMarginPosition]
  field_simp [ne_of_gt h.U_pos,ne_of_gt h.Y_pos,ne_of_gt h.w_pos]
  ring

theorem margin_angle_deriv (q u t : ℝ) :
    HasDerivAt (fun a => cutMargin q (Real.cos a) (Real.sin a) u)
      (cutMarginAngle q (Real.cos t) (Real.sin t) u) t := by
  have h := (((positionB_angle_deriv q u t).mul_const
    (topLeft q u/topHeight q u)).const_mul (1057/1000)).add (secondTilt_angle_deriv q u t)
  change HasDerivAt (fun a => cutMargin q (Real.cos a) (Real.sin a) u) _ t at h
  exact h.congr_deriv (by dsimp only [cutMarginAngle,secondComponent]; ring)

/-- Coarse circle and frame bounds give a position slope above `0.91` and angle slope above `-0.3`. -/
theorem algebraic_margin_bounds {q u U V Y v w c s : ℝ}
    (hq : 3.9155 ≤ q ∧ q ≤ 3.9156) (hu : 0.895 ≤ u ∧ u ≤ 0.937)
    (hU : 1.6414 ≤ U ∧ U ≤ 1.6691) (hV : 1.3309 ≤ V ∧ V ≤ 1.3586)
    (hY : 1.4387 ≤ Y ∧ Y ≤ 1.4643) (hv : 0.5357 ≤ v ∧ v ≤ 0.5613)
    (hw : 1.8974 ≤ w ∧ w ≤ 1.9049) (hc : 0.986 ≤ c ∧ c ≤ 1)
    (hs : 0.099 ≤ s ∧ s ≤ 0.162)
    (hL : 1.019 ≤ c+s*v/w ∧ c+s*v/w ≤ 1.04) :
    let p := (2-u)*V/(U*Y)
    0.91 ≤ (1057/1000)*(s*p*q/w^3*(V/Y)+
      (c+s*v/w)*((2-u)/(U*Y)+V*p/Y^2))+p*(c*(v/w)-s) ∧
    -0.3 ≤ (1057/1000)*(-s+c*v/w)*(V/Y)-c*v+s*(w-1) := by
  dsimp only
  let p := (2-u)*V/(U*Y)
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  have ht : 1.063 ≤ 2-u ∧ 2-u ≤ 1.105 := by constructor <;> linarith only [hu]
  have hp₀ := positive_quotient_bounds (prod ht hV) (prod hU hY) (by norm_num) (by norm_num)
  have hp : 0.57 ≤ p ∧ p ≤ 0.637 := by constructor <;> linarith only [hp₀]
  have ha₀ := positive_quotient_bounds hv hw (by norm_num) (by norm_num)
  have ha : 0.28 ≤ v/w ∧ v/w ≤ 0.296 := by constructor <;> linarith only [ha₀]
  have hca := prod hc ha
  have hP := prod hp (show 0.114 ≤ c*(v/w)-s ∧ c*(v/w)-s ≤ 0.197 by
    constructor <;> linarith only [hca,hs])
  have h₁ := positive_quotient_bounds ht (prod hU hY) (by norm_num) (by norm_num)
  have h₂ := positive_quotient_bounds (prod hV hp) (prod hY hY) (by norm_num) (by norm_num)
  have hratio : 0.788 ≤ (2-u)/(U*Y)+V*p/Y^2 ∧
      (2-u)/(U*Y)+V*p/Y^2 ≤ 1 := by
    rw [pow_two]
    constructor <;> linarith only [h₁,h₂]
  have hb := prod hL hratio
  have hn : 0 ≤ s*p*q/w^3*(V/Y) := by
    have hsp : 0 ≤ s := by linarith only [hs]
    have hpp : 0 ≤ p := by linarith only [hp]
    have hqp : 0 ≤ q := by linarith only [hq.1,hq.2]
    have hwp : 0 ≤ w := by linarith only [hw]
    have hVp : 0 ≤ V := by linarith only [hV]
    have hYp : 0 ≤ Y := by linarith only [hY]
    positivity
  constructor
  · change 0.91 ≤ (1057/1000)*(s*p*q/w^3*(V/Y)+_)+p*_
    linarith only [hn,hb.1,hP.1]
  · let A := (1057/1000)*(V/Y)-(w-1)
    have hb₀ := positive_quotient_bounds hV hY (by norm_num) (by norm_num)
    have hA : 0.05 ≤ A ∧ A ≤ 0.11 := by constructor <;> dsimp only [A] <;> linarith only [hb₀,hw]
    have hsA := prod hs hA
    have hAm : 0 ≤ 1-A ∧ 1-A ≤ 0.95 := by constructor <;> linarith only [hA]
    have hterm := prod hca hAm
    have he : (1057/1000)*(-s+c*v/w)*(V/Y)-c*v+s*(w-1) =
        -s*A-c*(v/w)*(1-A) := by
      dsimp only [A]
      field_simp [show w ≠ 0 by linarith only [hw]]
      ring
    rw [he]
    linarith only [hsA.2,hterm.2]

/-- The circle-chain margin satisfies these slope bounds on the full pose rectangle. -/
theorem local_margin_bounds {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    0.91 ≤ cutMarginPosition q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ∧
    -0.3 ≤ cutMarginAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  let a := radicalCoordinates q p.1 p.2
  obtain ⟨_,_,hUl,hUu,hYl,hYu,hwl,hwu,_⟩ := radical_coordinate_bounds hq hy hp.2
  have hq' : 3.9155 ≤ q ∧ q ≤ 3.9156 := by constructor <;> linarith only [hq.1,hq.2]
  have hu : 0.895 ≤ -p.1 ∧ -p.1 ≤ 0.937 := by constructor <;> linarith only [hy]
  have hU : 1.6414 ≤ a.x₂ ∧ a.x₂ ≤ 1.6691 := by constructor <;> linarith only [hUl,hUu]
  have hV : 1.3309 ≤ -a.x₃ ∧ -a.x₃ ≤ 1.3586 := by
    dsimp only [Coordinates.x₃]; constructor <;> linarith only [hU]
  have hY : 1.4387 ≤ a.y₃ ∧ a.y₃ ≤ 1.4643 := by constructor <;> linarith only [hYl,hYu]
  have hv : 0.5357 ≤ -a.y₄ ∧ -a.y₄ ≤ 0.5613 := by
    dsimp only [Coordinates.y₄]; constructor <;> linarith only [hY]
  have hw : 1.8974 ≤ -a.x₄ ∧ -a.x₄ ≤ 1.9049 := by constructor <;> linarith only [hwl,hwu]
  obtain ⟨hc₀,hc₁,hs₀,hs₁⟩ := halfAngle_local_bounds hp.2
  have hf := Coordinates.frame_bounds_of_coordinates hY hw hp.2
  have hL : 1.019 ≤ a.c+a.s*(-a.y₄)/(-a.x₄) ∧ a.c+a.s*(-a.y₄)/(-a.x₄) ≤ 1.04 := by
    simpa only [mul_neg,neg_div_neg_eq] using hf.2.1
  have h := algebraic_margin_bounds hq' hu hU hV hY hv hw ⟨hc₀,hc₁⟩ ⟨hs₀,hs₁⟩ hL
  obtain ⟨_,hU',hV',hY',hv',hw'⟩ := radical_coordinate_values q p.1 p.2
  simp only [cutMarginPosition,cutMarginAngle,positionB,slopeRatio,hU',hV',hY',hv',hw']
  exact h

end FiveCornerGeometry

section CutMargin
open FiveCornerGeometry

/-- The factor of the HE contact in reserve 5 along the circle chain. -/
def familyMargin (q : ℝ) (p : Pose) : ℝ := cutMargin q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)

theorem familyMargin_coordinates (q y z : ℝ) : familyMargin q (y,z) =
    (1057/1000)*((radicalCoordinates q y z).c+(radicalCoordinates q y z).s*
      (radicalCoordinates q y z).y₄/(radicalCoordinates q y z).x₄)*
      (-(radicalCoordinates q y z).x₃)/(radicalCoordinates q y z).y₃-
      (radicalCoordinates q y z).h₂tilt := by
  obtain ⟨_,_,hV,hY,hv,hw⟩ := radical_coordinate_values q y z
  rw [familyMargin,cutMargin,positionB,secondTilt,hV,hY,hv,hw]
  dsimp only [Coordinates.h₂tilt,Coordinates.c,Coordinates.s]
  simp only [show (radicalCoordinates q y z).z = z from rfl]
  ring

theorem familyMargin_partial_y {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun y => familyMargin q (y,p.2))
      (cutMarginPosition q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)) p.1 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  have hd := (margin_position_deriv (c:=halfAngleCos p.2) (s:=halfAngleSin p.2)
    (local_smoothDomain hq hy hp.2)).comp p.1 (hasDerivAt_id' p.1).neg
  change HasDerivAt (fun y => familyMargin q (y,p.2)) _ p.1 at hd
  exact hd.congr_deriv (by ring)

theorem familyMargin_partial_z (q : ℝ) (p : Pose) :
    HasDerivAt (fun z => familyMargin q (p.1,z))
      ((2/(1+p.2^2))*cutMarginAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)) p.2 := by
  have hd := (margin_angle_deriv q (-p.1) (2*Real.arctan p.2)).comp p.2 (halfAngle_deriv p.2)
  change HasDerivAt (fun z => cutMargin q (Real.cos (2*Real.arctan z))
    (Real.sin (2*Real.arctan z)) (-p.1)) _ p.2 at hd
  have he : (fun z => cutMargin q (Real.cos (2*Real.arctan z))
      (Real.sin (2*Real.arctan z)) (-p.1)) = (fun z => familyMargin q (p.1,z)) := by
    funext z
    rw [(halfAngle_frame z).1,(halfAngle_frame z).2]
    rfl
  rw [he,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at hd
  exact hd.congr_deriv (by ring)

theorem familyMargin_z_bound {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    -0.6 ≤ (2/(1+p.2^2))*cutMarginAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) := by
  have hm := (local_margin_bounds hq hp).2
  have hg : 0 ≤ (2/(1+p.2^2):ℝ) ∧ 2/(1+p.2^2) ≤ 2 := by
    constructor
    · positivity
    · rw [div_le_iff₀ (halfAngle_den_pos p.2)]
      nlinarith only [sq_nonneg p.2]
  have h := mul_le_mul_of_nonneg_left hm hg.1
  linarith only [h,hg.2]

theorem familyMargin_position_slope {q y₀ y₁ z : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox)
    (h₀ : y₀ ∈ Icc (-(937/1000)) (-(179/200)))
    (h₁ : y₁ ∈ Icc (-(937/1000)) (-(179/200))) (hy : y₀ ≤ y₁) :
    0.91*(y₁-y₀) ≤ familyMargin q (y₁,z)-familyMargin q (y₀,z) :=
  slope_lower_bound (f:=fun y => familyMargin q (y,z))
    (fun y hy => familyMargin_partial_y (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩)
    (fun y hy => (local_margin_bounds (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).1) h₀ h₁ hy

theorem familyMargin_tilt_slope {q y z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200)))
    (h₀ : z₀ ∈ tiltBox) (h₁ : z₁ ∈ tiltBox) (hz : z₀ ≤ z₁) :
    -0.6*(z₁-z₀) ≤ familyMargin q (y,z₁)-familyMargin q (y,z₀) :=
  slope_lower_bound (f:=fun z => familyMargin q (y,z)) (fun z _ => familyMargin_partial_z q (y,z))
    (fun z hz => familyMargin_z_bound (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩) h₀ h₁ hz

end CutMargin

/-- The position gain `0.91 * (2/3)` exceeds the worst tilt loss `0.6`. -/
theorem root_margin_slope {q y₀ y₁ z₀ z₁ : ℝ} (hq : q ∈ radiusBox)
    (h₀ : (y₀,z₀) ∈ poseBox) (h₁ : (y₁,z₁) ∈ poseBox) (hz : z₀ ≤ z₁)
    (hr₀ : familyY q (y₀,z₀)=0) (hr₁ : familyY q (y₁,z₁)=0) :
    (1/150)*(z₁-z₀) ≤ familyMargin q (y₁,z₁)-familyMargin q (y₀,z₀) := by
  have hy := (root_position_motion hq h₀ h₁ hz hr₀ hr₁).1
  have hmove := root_position_lower hq h₀ h₁ hz hr₀ hr₁
  have hp := familyMargin_position_slope hq h₁.2 h₀.1 h₁.1 hy
  have ht := familyMargin_tilt_slope hq h₀.1 h₀.2 h₁.2 hz
  linarith only [hmove,hp,ht]
namespace FiveCornerGeometry

/-- The unnormalized cut shared by the last two owner reserves. -/
def rawCut (q c s u : ℝ) : ℝ :=
  secondComponent q c s u/firstComponent q c s u*
    (firstComponent q c s u+secondTilt q c s u)

/-- Its first tilt-angle derivative at fixed position. -/
def rawCutAngle (q c s u : ℝ) : ℝ :=
  let K := firstComponent q c s u; let H := secondComponent q c s u
  let e := secondTilt q c s u; let T := firstTilt q c s u
  e+(e^2+H*(1-H))/K-H*e*T/K^2

/-- Its second tilt-angle derivative at fixed position. -/
def rawCutAngle2 (q c s u : ℝ) : ℝ :=
  let K := firstComponent q c s u; let H := secondComponent q c s u
  let e := secondTilt q c s u; let T := firstTilt q c s u
  (1-H)+e*(3-4*H)/K-2*(e^2+H*(1-H))*T/K^2-
    H*e*(2-K)/K^2+2*H*e*T^2/K^3

/-- Its derivative in the position coordinate `y = -u`. -/
def rawCutPosition (q c s u : ℝ) : ℝ :=
  let K := firstComponent q c s u; let H := secondComponent q c s u
  let e := secondTilt q c s u; let p := slopeRatio q u
  let A := positionA q c s u; let L := positionB q c s u
  p*L*(1+e/K)+(H/K)*p*(c*lowerHeight q u/lowerLeft q u-s)+(H/K)*A*e/K

theorem rawCut_position_deriv {q c s u : ℝ} (h : SmoothDomain q u)
    (hK : firstComponent q c s u ≠ 0) :
    HasDerivAt (rawCut q c s) (-rawCutPosition q c s u) u := by
  obtain ⟨dK,dH⟩ := components_position_deriv (c:=c) (s:=s) h.r_pos h.U_pos h.Y_pos h.w_pos
  obtain ⟨_,_,_,_,dv,dw⟩ := radical_derivatives h.r_pos h.U_pos h.Y_pos h.w_pos
  have de := (dv.const_mul (-s)).fun_sub ((dw.sub_const 1).const_mul c)
  have hd := (dH.fun_div dK hK).fun_mul (dK.add de)
  change HasDerivAt (rawCut q c s) _ u at hd
  apply hd.congr_deriv
  dsimp only [rawCutPosition,positionA,positionB,Pi.add_apply,secondTilt]
  field_simp [hK,ne_of_gt h.w_pos]
  ring

theorem rawCut_angle_deriv {q u t : ℝ}
    (hK : firstComponent q (Real.cos t) (Real.sin t) u ≠ 0) :
    HasDerivAt (fun a => rawCut q (Real.cos a) (Real.sin a) u)
      (rawCutAngle q (Real.cos t) (Real.sin t) u) t := by
  have hd := ((secondComponent_angle_deriv q u t).fun_div
    (firstComponent_angle_deriv q u t) hK).fun_mul
      ((firstComponent_angle_deriv q u t).add (secondTilt_angle_deriv q u t))
  change HasDerivAt (fun a => rawCut q (Real.cos a) (Real.sin a) u) _ t at hd
  apply hd.congr_deriv
  dsimp only [rawCutAngle,Pi.add_apply]
  field_simp [hK]
  ring

theorem rawCut_angle_second_deriv {q u t : ℝ}
    (hK : firstComponent q (Real.cos t) (Real.sin t) u ≠ 0) :
    HasDerivAt (fun a => rawCutAngle q (Real.cos a) (Real.sin a) u)
      (rawCutAngle2 q (Real.cos t) (Real.sin t) u) t := by
  have dK := firstComponent_angle_deriv q u t
  have dH := secondComponent_angle_deriv q u t
  have de := secondTilt_angle_deriv q u t
  have dT := firstTilt_angle_deriv q u t
  have dP := dH.fun_mul de
  have dP' := (de.fun_pow 2).fun_add (dH.fun_mul (dH.const_sub 1))
  have hd := (de.fun_add (dP'.fun_div dK hK)).fun_sub
    ((dP.fun_mul dT).fun_div (dK.fun_pow 2) (pow_ne_zero 2 hK))
  change HasDerivAt (fun a => rawCutAngle q (Real.cos a) (Real.sin a) u) _ t at hd
  apply hd.congr_deriv
  dsimp only [rawCutAngle2]
  field_simp [hK]
  ring

/-- Bounds on the first two angle derivatives, using only short bounds on the four projections. -/
theorem rawCut_angle_bounds {K H e T : ℝ}
    (hK : 1.3 ≤ K ∧ K ≤ 1.5) (hH : 1 ≤ H ∧ H ≤ 1.5)
    (he : |e| ≤ 1) (hT : |T| ≤ 1.1) :
    |e+(e^2+H*(1-H))/K-H*e*T/K^2| ≤ 10/3 ∧
    |(1-H)+e*(3-4*H)/K-2*(e^2+H*(1-H))*T/K^2-
      H*e*(2-K)/K^2+2*H*e*T^2/K^3| ≤ 15/2 := by
  have hKp : 0 < K := by linarith only [hK]
  have hHa : |H| ≤ 1.5 := by rw [abs_of_nonneg (by linarith only [hH])]; exact hH.2
  have h1H : |1-H| ≤ 0.5 := abs_le.mpr ⟨by linarith only [hH],by linarith only [hH]⟩
  have h3H : |3-4*H| ≤ 3 := abs_le.mpr ⟨by linarith only [hH],by linarith only [hH]⟩
  have h2K : |2-K| ≤ 0.7 := abs_le.mpr ⟨by linarith only [hK],by linarith only [hK]⟩
  have prod {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x*y| ≤ a*b := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  have quo {x a b : ℝ} (hx : |x| ≤ a) (hb : 0 < b) (hkb : b ≤ K) :
      |x/K| ≤ a/b := by
    rw [abs_div,abs_of_pos hKp]
    exact div_le_div₀ ((abs_nonneg _).trans hx) hx hb hkb
  have hK2 : (1.3:ℝ)^2 ≤ K^2 := by nlinarith only [hK.1]
  have hK3 : (1.3:ℝ)^3 ≤ K^3 := by nlinarith only [hK.1,hK2]
  have quo2 {x a : ℝ} (hx : |x| ≤ a) : |x/K^2| ≤ a/(1.3^2) := by
    rw [abs_div,abs_of_pos (pow_pos hKp 2)]
    exact div_le_div₀ ((abs_nonneg _).trans hx) hx (by norm_num) hK2
  have quo3 {x a : ℝ} (hx : |x| ≤ a) : |x/K^3| ≤ a/(1.3^3) := by
    rw [abs_div,abs_of_pos (pow_pos hKp 3)]
    exact div_le_div₀ ((abs_nonneg _).trans hx) hx (by norm_num) hK3
  have hP := prod hHa he
  have hP' : |e^2+H*(1-H)| ≤ 7/4 := by
    have h := (abs_add_le (e^2) (H*(1-H))).trans (add_le_add (by simpa [pow_two] using prod he he) (prod hHa h1H))
    linarith only [h]
  have hP'' := prod he h3H
  have hD1 := (abs_sub (e+(e^2+H*(1-H))/K) (H*e*T/K^2)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  have hq1 := quo hP' (by norm_num : (0:ℝ)<1.3) hK.1
  have hq2 := quo2 (prod hP hT)
  have hD2 : |(1-H)+e*(3-4*H)/K-2*(e^2+H*(1-H))*T/K^2-
      H*e*(2-K)/K^2+2*H*e*T^2/K^3| ≤
      |1-H|+|e*(3-4*H)/K|+|2*(e^2+H*(1-H))*T/K^2|+
        |H*e*(2-K)/K^2|+|2*H*e*T^2/K^3| := by
    calc _ ≤ |(1-H)+e*(3-4*H)/K-2*(e^2+H*(1-H))*T/K^2-H*e*(2-K)/K^2|+
        |2*H*e*T^2/K^3| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hq3 := quo hP'' (by norm_num : (0:ℝ)<1.3) hK.1
  have hq4 := quo2 (prod (prod (show |(2:ℝ)| ≤ 2 by norm_num) hP') hT)
  have hq5 := quo2 (prod hP h2K)
  have hT2 : |T^2| ≤ (1.1:ℝ)^2 := by simpa only [pow_two] using prod hT hT
  have hq6 := quo3 (prod (prod (show |(2:ℝ)| ≤ 2 by norm_num) hP) hT2)
  constructor
  · linarith only [hD1,he,hq1,hq2]
  · have heq : 2*H*e*T^2 = 2*(H*e)*T^2 := by ring
    rw [heq] at hD2 ⊢
    linarith only [hD2,h1H,hq3,hq4,hq5,hq6]

/-- Cancellation in the cut makes it decrease with position on the full rectangle. -/
theorem algebraic_rawCut_position_nonpos {u r U V Y v w c s : ℝ}
    (hu : 0.895 ≤ u ∧ u ≤ 0.937) (hr : 1.7428 ≤ r ∧ r ≤ 1.7649)
    (hU : 1.6414 ≤ U ∧ U ≤ 1.6691) (hV : 1.3309 ≤ V ∧ V ≤ 1.3586)
    (hY : 1.4387 ≤ Y ∧ Y ≤ 1.4643) (hv : 0.5357 ≤ v ∧ v ≤ 0.5613)
    (hw : 1.8974 ≤ w ∧ w ≤ 1.9049) (hc : 0.986 ≤ c ∧ c ≤ 1)
    (hs : 0.099 ≤ s ∧ s ≤ 0.162)
    (hK : 1.3198 ≤ 2-c*(r-1)+s*u ∧ 2-c*(r-1)+s*u ≤ 1.4263)
    (hE : 0.93 ≤ c*(w-1)+s*v ∧ c*(w-1)+s*v ≤ 1)
    (hL : 1.019 ≤ c+s*v/w ∧ c+s*v/w ≤ 1.04) :
    let K := 2-c*(r-1)+s*u; let H := 1+c*v-s*(w-1); let E := c*(w-1)+s*v
    let p := (2-u)*V/(U*Y)
    p*(c+s*v/w)*(1-E/K)+(H/K)*p*(c*v/w-s)-(H/K)*(s+c*u/r)*E/K ≤ 0 := by
  dsimp only
  let K := 2-c*(r-1)+s*u
  let H := 1+c*v-s*(w-1)
  let E := c*(w-1)+s*v
  let p := (2-u)*V/(U*Y)
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  have ht : 1.063 ≤ 2-u ∧ 2-u ≤ 1.105 := by constructor <;> linarith only [hu]
  have hp₀ := positive_quotient_bounds (prod ht hV) (prod hU hY) (by norm_num) (by norm_num)
  have hp : 0 ≤ p ∧ p ≤ 0.637 := by constructor <;> linarith only [hp₀]
  have hW : 0.8974 ≤ w-1 ∧ w-1 ≤ 0.9049 := by constructor <;> linarith only [hw]
  have hcv := prod hc hv
  have hsw := prod hs hW
  have hH : 1.38 ≤ H ∧ H ≤ 1.473 := by constructor <;> dsimp only [H] <;> linarith only [hcv,hsw]
  have hε₀ := positive_quotient_bounds hH hK (by norm_num) (by norm_num)
  have hε : 0.96 ≤ H/K ∧ H/K ≤ 1.12 := by constructor <;> linarith only [hε₀]
  have hS : 1.6402 ≤ r+w-2 ∧ r+w-2 ≤ 1.6698 := by constructor <;> linarith only [hr,hw]
  have hD : 0.3337 ≤ u-v ∧ u-v ≤ 0.4013 := by constructor <;> linarith only [hu,hv]
  have hcS := prod hc hS
  have hsD := prod hs hD
  have hC : 0.3198 ≤ K-E ∧ K-E ≤ 0.448 := by
    constructor
    · linarith only [hK.1,hE.2]
    · have heq : K-E = 2-c*(r+w-2)+s*(u-v) := by dsimp only [K,E]; ring
      rw [heq]
      linarith only [hcS.1,hsD.2]
  have hR₀ := positive_quotient_bounds hC hK (by norm_num) (by norm_num)
  have hR : 0 ≤ (K-E)/K ∧ (K-E)/K ≤ 0.34 := by constructor <;> linarith only [hR₀]
  have ha₀ := positive_quotient_bounds hv hw (by norm_num) (by norm_num)
  have ha : 0.28 ≤ v/w ∧ v/w ≤ 0.296 := by constructor <;> linarith only [ha₀]
  have hca := prod hc ha
  have hT : 0 ≤ c*v/w-s ∧ c*v/w-s ≤ 0.197 := by
    constructor <;> simp only [mul_div_assoc] <;> linarith only [hca,hs]
  have hA₀ := positive_quotient_bounds (prod hc hu) hr (by norm_num) (by norm_num)
  have hA : 0.598 ≤ s+c*u/r ∧ s+c*u/r ≤ 0.7 := by constructor <;> linarith only [hA₀,hs]
  have hE₀ := positive_quotient_bounds hE hK (by norm_num) (by norm_num)
  have hER : 0.65 ≤ E/K ∧ E/K ≤ 1 := by constructor <;> linarith only [hE₀]
  have hB₀ := prod hp hL
  have hB : 0 ≤ p*(c+s*v/w) ∧ p*(c+s*v/w) ≤ 0.663 := by
    constructor <;> linarith only [hB₀]
  have hterm₁ := (prod hB hR).2
  have hterm₂ := (prod (prod hε hp) hT).2
  have hterm₃ := (prod (prod hε hA) hER).1
  have heq : 1-E/K = (K-E)/K := by field_simp [show K ≠ 0 by linarith only [hK.1]]
  change p*(c+s*v/w)*(1-E/K)+(H/K)*p*(c*v/w-s)-(H/K)*(s+c*u/r)*E/K ≤ 0
  rw [heq]
  simp only [div_eq_mul_inv,mul_assoc] at hterm₁ hterm₂ hterm₃ ⊢
  linarith only [hterm₁,hterm₂,hterm₃]

theorem rawCut_local_data {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    (1.3 ≤ firstComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ∧
      firstComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ≤ 1.5) ∧
    (1 ≤ secondComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ∧
      secondComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ≤ 1.5) ∧
    |secondTilt q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)| ≤ 1 ∧
    |firstTilt q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)| ≤ 1.1 ∧
    rawCutPosition q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) ≤ 0 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  let a := radicalCoordinates q p.1 p.2
  obtain ⟨hrl,hru,hUl,hUu,hYl,hYu,hwl,hwu,hhl,hhu,_⟩ := radical_coordinate_bounds hq hy hp.2
  have hu : 0.895 ≤ -p.1 ∧ -p.1 ≤ 0.937 := by constructor <;> linarith only [hy]
  have hr : 1.7428 ≤ a.x₁ ∧ a.x₁ ≤ 1.7649 := by constructor <;> linarith only [hrl,hru]
  have hU : 1.6414 ≤ a.x₂ ∧ a.x₂ ≤ 1.6691 := by constructor <;> linarith only [hUl,hUu]
  have hV : 1.3309 ≤ -a.x₃ ∧ -a.x₃ ≤ 1.3586 := by
    dsimp only [Coordinates.x₃]; constructor <;> linarith only [hU]
  have hY : 1.4387 ≤ a.y₃ ∧ a.y₃ ≤ 1.4643 := by constructor <;> linarith only [hYl,hYu]
  have hv : 0.5357 ≤ -a.y₄ ∧ -a.y₄ ≤ 0.5613 := by
    dsimp only [Coordinates.y₄]; constructor <;> linarith only [hY]
  have hw : 1.8974 ≤ -a.x₄ ∧ -a.x₄ ≤ 1.9049 := by constructor <;> linarith only [hwl,hwu]
  obtain ⟨hc₀,hc₁,hs₀,hs₁⟩ := halfAngle_local_bounds hp.2
  have hc : 0.986 ≤ a.c ∧ a.c ≤ 1 := ⟨hc₀,hc₁⟩
  have hs : 0.099 ≤ a.s ∧ a.s ≤ 0.162 := ⟨hs₀,hs₁⟩
  have hf := Coordinates.frame_bounds_of_coordinates hY hw hp.2
  have prod {x y l h l' h' : ℝ} (hx : l ≤ x ∧ x ≤ h) (hy : l' ≤ y ∧ y ≤ h')
      (hl : 0 ≤ l := by norm_num) (hl' : 0 ≤ l' := by norm_num) :=
    positive_product_bounds hx hy hl hl'
  have hK : 1.3198 ≤ 2-a.c*(a.x₁-1)+a.s*(-p.1) ∧
      2-a.c*(a.x₁-1)+a.s*(-p.1) ≤ 1.4263 := by
    have heq : 2-a.c*(a.x₁-1)+a.s*(-p.1) = -a.h₁ := by
      dsimp only [Coordinates.h₁]
      rw [show a.y = p.1 from rfl]
      ring
    rw [heq]
    constructor <;> linarith only [hhl,hhu]
  have hE : 0.93 ≤ a.c*(-a.x₄-1)+a.s*(-a.y₄) ∧
      a.c*(-a.x₄-1)+a.s*(-a.y₄) ≤ 1 := by
    have heq : a.h₂tilt = a.c*(-a.x₄-1)+a.s*(-a.y₄) := by dsimp only [Coordinates.h₂tilt]; ring
    rw [← heq]
    exact hf.2.2
  have hL : 1.019 ≤ a.c+a.s*(-a.y₄)/(-a.x₄) ∧ a.c+a.s*(-a.y₄)/(-a.x₄) ≤ 1.04 := by
    simpa only [mul_neg,neg_div_neg_eq] using hf.2.1
  have hW : 0.8974 ≤ -a.x₄-1 ∧ -a.x₄-1 ≤ 0.9049 := by constructor <;> linarith only [hw]
  have hcv := prod hc hv
  have hsw := prod hs hW
  have hH : 1 ≤ 1+a.c*(-a.y₄)-a.s*(-a.x₄-1) ∧
      1+a.c*(-a.y₄)-a.s*(-a.x₄-1) ≤ 1.5 := by constructor <;> linarith only [hcv,hsw]
  have hR : 0.7428 ≤ a.x₁-1 ∧ a.x₁-1 ≤ 0.7649 := by constructor <;> linarith only [hr]
  have hsR := prod hs hR
  have hcu := prod hc hu
  have hT : |a.s*(a.x₁-1)+a.c*(-p.1)| ≤ 1.1 := by
    rw [abs_of_nonneg (by linarith only [hsR.1,hcu.1])]
    linarith only [hsR.2,hcu.2]
  obtain ⟨hr',hU',hV',hY',hv',hw'⟩ := radical_coordinate_values q p.1 p.2
  have hK' : firstComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) =
      2-a.c*(a.x₁-1)+a.s*(-p.1) := by rw [firstComponent,hr']; rfl
  have hH' : secondComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) =
      1+a.c*(-a.y₄)-a.s*(-a.x₄-1) := by rw [secondComponent,hv',hw']; rfl
  have he' : secondTilt q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) =
      -(a.c*(-a.x₄-1)+a.s*(-a.y₄)) := by rw [secondTilt,hv',hw']; change -a.s*(-a.y₄)-a.c*(-a.x₄-1)=_; ring
  have hT' : firstTilt q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) =
      a.s*(a.x₁-1)+a.c*(-p.1) := by rw [firstTilt,hr']; rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hK']; constructor <;> linarith only [hK]
  · rw [hH']; exact hH
  · rw [he',abs_neg,abs_of_nonneg (by linarith only [hE])]; exact hE.2
  · rw [hT']; exact hT
  · have h := algebraic_rawCut_position_nonpos hu hr hU hV hY hv hw hc hs hK hE hL
    dsimp only [rawCutPosition,positionA,positionB,slopeRatio]
    rw [hK',hH',he',hr',hU',hV',hY',hv',hw']
    dsimp only [a,Coordinates.c,Coordinates.s] at h ⊢
    simp only [show (radicalCoordinates q p.1 p.2).z = p.2 from rfl] at h ⊢
    convert h using 1
    ring


end FiveCornerGeometry

section RawCut
open FiveCornerGeometry

def familyRawCut (q : ℝ) (p : Pose) : ℝ := rawCut q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)
def familyRawCutZ (q : ℝ) (p : Pose) : ℝ :=
  (2/(1+p.2^2))*rawCutAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)
def familyRawCutZZ (q : ℝ) (p : Pose) : ℝ :=
  (-(4*p.2)/(1+p.2^2)^2)*rawCutAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)+
    (2/(1+p.2^2))^2*rawCutAngle2 q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)

theorem familyRawCut_partial_y {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun y => familyRawCut q (y,p.2))
      (rawCutPosition q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)) p.1 := by
  have hy : -937/1000 ≤ p.1 ∧ p.1 ≤ -179/200 := by
    constructor <;> linarith only [hp.1.1,hp.1.2]
  have hK := ne_of_gt (show 0 < firstComponent q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1) by
    linarith only [(rawCut_local_data hq hp).1.1])
  have hd := (rawCut_position_deriv (c:=halfAngleCos p.2) (s:=halfAngleSin p.2)
    (local_smoothDomain hq hy hp.2) hK).comp p.1 (hasDerivAt_id' p.1).neg
  change HasDerivAt (fun y => familyRawCut q (y,p.2)) _ p.1 at hd
  exact hd.congr_deriv (by ring)

theorem familyRawCut_partial_z {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyRawCut q (p.1,z)) (familyRawCutZ q p) p.2 := by
  have hK : firstComponent q (Real.cos (2*Real.arctan p.2)) (Real.sin (2*Real.arctan p.2)) (-p.1) ≠ 0 := by
    rw [(halfAngle_frame p.2).1,(halfAngle_frame p.2).2]
    linarith only [(rawCut_local_data hq hp).1.1]
  have hd := (rawCut_angle_deriv hK).comp p.2 (halfAngle_deriv p.2)
  change HasDerivAt (fun z => rawCut q (Real.cos (2*Real.arctan z))
    (Real.sin (2*Real.arctan z)) (-p.1)) _ p.2 at hd
  have he : (fun z => rawCut q (Real.cos (2*Real.arctan z))
      (Real.sin (2*Real.arctan z)) (-p.1)) = (fun z => familyRawCut q (p.1,z)) := by
    funext z; rw [(halfAngle_frame z).1,(halfAngle_frame z).2]; rfl
  rw [he,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at hd
  exact hd.congr_deriv (by dsimp only [familyRawCutZ]; ring)

theorem familyRawCut_partial_zz {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    HasDerivAt (fun z => familyRawCutZ q (p.1,z)) (familyRawCutZZ q p) p.2 := by
  have hK : firstComponent q (Real.cos (2*Real.arctan p.2)) (Real.sin (2*Real.arctan p.2)) (-p.1) ≠ 0 := by
    rw [(halfAngle_frame p.2).1,(halfAngle_frame p.2).2]
    linarith only [(rawCut_local_data hq hp).1.1]
  have hdA := (rawCut_angle_second_deriv hK).comp p.2 (halfAngle_deriv p.2)
  have hd := (halfAngle_speed_deriv p.2).fun_mul hdA
  simp only [Function.comp_apply] at hd
  change HasDerivAt (fun z => (2/(1+z^2))*rawCutAngle q (Real.cos (2*Real.arctan z))
    (Real.sin (2*Real.arctan z)) (-p.1)) _ p.2 at hd
  have he : (fun z => (2/(1+z^2))*rawCutAngle q (Real.cos (2*Real.arctan z))
      (Real.sin (2*Real.arctan z)) (-p.1)) = (fun z => familyRawCutZ q (p.1,z)) := by
    funext z; rw [(halfAngle_frame z).1,(halfAngle_frame z).2]; rfl
  rw [he,(halfAngle_frame p.2).1,(halfAngle_frame p.2).2] at hd
  exact hd.congr_deriv (by dsimp only [familyRawCutZZ]; ring)

theorem familyRawCut_second_bound {q : ℝ} {p : Pose} (hq : q ∈ radiusBox) (hp : p ∈ poseBox) :
    |familyRawCutZZ q p| ≤ 32 := by
  obtain ⟨hK,hH,he,hT,_⟩ := rawCut_local_data hq hp
  have h := rawCut_angle_bounds hK hH he hT
  change |rawCutAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)| ≤ 10/3 ∧
    |rawCutAngle2 q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1)| ≤ 15/2 at h
  have hg : |(2/(1+p.2^2):ℝ)| ≤ 2 := by
    rw [abs_of_pos (by positivity),div_le_iff₀ (halfAngle_den_pos p.2)]
    nlinarith only [sq_nonneg p.2]
  have hg' : |(-(4*p.2)/(1+p.2^2)^2:ℝ)| ≤ 1/3 := by
    have hz : 0 ≤ p.2 := by linarith only [hp.2.1]
    rw [abs_div,abs_neg,abs_mul,abs_of_nonneg hz,abs_of_pos (pow_pos (halfAngle_den_pos p.2) 2)]
    norm_num only [show |(4:ℝ)| = 4 by norm_num]
    rw [div_le_iff₀ (pow_pos (halfAngle_den_pos p.2) 2)]
    have hden : 1 ≤ (1+p.2^2)^2 := by nlinarith only [sq_nonneg p.2,sq_nonneg (p.2^2)]
    linarith only [hden,hp.2.2]
  have prod {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x*y| ≤ a*b := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  have h₁ := prod hg' h.1
  have hg2 : |(2/(1+p.2^2):ℝ)^2| ≤ 4 := by
    calc _ = |(2/(1+p.2^2):ℝ)*(2/(1+p.2^2))| := by rw [pow_two]
      _ ≤ (2:ℝ)*2 := prod hg hg
      _ = 4 := by norm_num
  have h₂ := prod hg2 h.2
  have h₃ := abs_add_le (-(4*p.2)/(1+p.2^2)^2*rawCutAngle q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1))
    ((2/(1+p.2^2))^2*rawCutAngle2 q (halfAngleCos p.2) (halfAngleSin p.2) (-p.1))
  dsimp only [familyRawCutZZ]
  linarith only [h₁,h₂,h₃]

theorem familyRawCut_antitone_y {q z : ℝ} (hq : q ∈ radiusBox) (hz : z ∈ tiltBox) :
    AntitoneOn (fun y => familyRawCut q (y,z)) (Icc (-(937/1000)) (-(179/200))) := by
  apply antiOn_of_hasDeriv_nonpos (d:=fun y => rawCutPosition q (halfAngleCos z) (halfAngleSin z) (-y))
  · intro y hy
    exact (familyRawCut_partial_y (q:=q) (p:=(y,z)) hq ⟨hy,hz⟩).continuousAt.continuousWithinAt
  · intro y hy
    exact familyRawCut_partial_y (q:=q) (p:=(y,z)) hq ⟨⟨hy.1.le,hy.2.le⟩,hz⟩
  · intro y hy
    exact (rawCut_local_data (q:=q) (p:=(y,z)) hq ⟨⟨hy.1.le,hy.2.le⟩,hz⟩).2.2.2.2

/-- A single tangent parabola controls the cut throughout the tilt interval. -/
theorem familyRawCut_taylor {q y z : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) (hz : z ∈ tiltBox) :
    familyRawCut q (y,131/2000)+familyRawCutZ q (y,131/2000)*(z-131/2000)-20*(z-131/2000)^2 ≤
      familyRawCut q (y,z) ∧
    familyRawCut q (y,z) ≤ familyRawCut q (y,131/2000)+familyRawCutZ q (y,131/2000)*(z-131/2000)+
      20*(z-131/2000)^2 := by
  have hm : (131/2000:ℝ) ∈ Icc (1/20) (81/1000) := by norm_num
  have hlo := curvature_tangent (κ:= -40) (f:=fun t => familyRawCut q (y,t))
    (d:=fun t => familyRawCutZ q (y,t)) (dd:=fun t => familyRawCutZZ q (y,t)) hz hm
    (fun t ht => familyRawCut_partial_z (q:=q) (p:=(y,t)) hq ⟨hy,ht⟩)
    (fun t ht => familyRawCut_partial_zz (q:=q) (p:=(y,t)) hq ⟨hy,ht⟩)
    (fun t ht => by have h := (abs_le.mp (familyRawCut_second_bound (q:=q) (p:=(y,t)) hq ⟨hy,ht⟩)).1; linarith only [h])
  have hhi := curvature_tangent (κ:= -40) (f:=fun t => -familyRawCut q (y,t))
    (d:=fun t => -familyRawCutZ q (y,t)) (dd:=fun t => -familyRawCutZZ q (y,t)) hz hm
    (fun t ht => (familyRawCut_partial_z (q:=q) (p:=(y,t)) hq ⟨hy,ht⟩).neg)
    (fun t ht => (familyRawCut_partial_zz (q:=q) (p:=(y,t)) hq ⟨hy,ht⟩).neg)
    (fun t ht => by have h := (abs_le.mp (familyRawCut_second_bound (q:=q) (p:=(y,t)) hq ⟨hy,ht⟩)).2; linarith only [h])
  constructor <;> linarith only [hlo,hhi]

/-- Position monotonicity and two midpoint tangent parabolas bound the entire rectangle. -/
theorem familyRawCut_bounds_of_midpoint {q : ℝ} (hq : q ∈ radiusBox)
    (hl : 0.418 ≤ familyRawCut q (-(179/200),131/2000))
    (hdl : |familyRawCutZ q (-(179/200),131/2000)| ≤ 0.05)
    (hu : familyRawCut q (-(937/1000),131/2000) ≤ 0.428)
    (hdu : |familyRawCutZ q (-(937/1000),131/2000)| ≤ 0.15)
    {p : Pose} (hp : p ∈ poseBox) : 0.412 ≤ familyRawCut q p ∧ familyRawCut q p ≤ 0.44 := by
  have hd : |p.2-131/2000| ≤ 0.0155 := abs_le.mpr
    ⟨by linarith only [hp.2.1],by linarith only [hp.2.2]⟩
  have hd' := abs_le.mp hd
  have hd2 : (p.2-131/2000)^2 ≤ (0.0155:ℝ)^2 := by nlinarith only [hd'.1,hd'.2]
  have prod {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x*y| ≤ a*b := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)
  have hgl := (abs_le.mp (prod hdl hd)).1
  have hgu := (abs_le.mp (prod hdu hd)).2
  have hlp := (familyRawCut_taylor hq (y:= -(179/200)) (by norm_num) hp.2).1
  have hup := (familyRawCut_taylor hq (y:= -(937/1000)) (by norm_num) hp.2).2
  have hlow : 0.412 ≤ familyRawCut q (-(179/200),p.2) := by linarith only [hlp,hl,hgl,hd2]
  have hupp : familyRawCut q (-(937/1000),p.2) ≤ 0.44 := by linarith only [hup,hu,hgu,hd2]
  have ha := familyRawCut_antitone_y hq hp.2
  exact ⟨hlow.trans (ha hp.1 (by norm_num) hp.1.2),
    (ha (by norm_num) hp.1 hp.1.1).trans hupp⟩

theorem familyRawCut_coordinates (q y z : ℝ) : familyRawCut q (y,z) =
    -(radicalCoordinates q y z).rawEpsilon*
      ((radicalCoordinates q y z).h₁+(radicalCoordinates q y z).h₂tilt) := by
  obtain ⟨hr,_,_,_,_,_⟩ := radical_coordinate_values q y z
  have hK : firstComponent q (halfAngleCos z) (halfAngleSin z) (-y) = -(radicalCoordinates q y z).h₁ := by
    rw [firstComponent,hr]
    dsimp only [Coordinates.h₁,Coordinates.c,Coordinates.s]
    simp only [show (radicalCoordinates q y z).z = z from rfl,show (radicalCoordinates q y z).y = y from rfl]
    ring
  have hH : secondComponent q (halfAngleCos z) (halfAngleSin z) (-y) = -(radicalCoordinates q y z).h₂ := by
    have h := familyHeight_geometric q y z
    change (radicalCoordinates q y z).h₂ = -_ at h
    linarith only [h]
  have he : secondTilt q (halfAngleCos z) (halfAngleSin z) (-y) = -(radicalCoordinates q y z).h₂tilt := by
    linarith only [familyHeight_tilt_geometric q y z]
  rw [familyRawCut,rawCut,hK,hH,he,neg_div_neg_eq]
  dsimp only [Coordinates.rawEpsilon]
  ring
end RawCut

namespace Coordinates

/-- Two circle equations bound the height at the lower tilt. -/
theorem lower_tilt_height {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156)
    (hy : -0.937 ≤ d.y ∧ d.y ≤ -0.928)
    (hw : -1.9049 ≤ d.x₄ ∧ d.x₄ ≤ -1.8974) (hz : d.z = 1/20) :
    -29/20 ≤ d.h₂ ∧ d.h₂ ≤ -7/5 := by
  have hU : 1.6632 ≤ d.x₂ ∧ d.x₂ ≤ 1.6691 :=
    circle_coordinate_bounds hd.second_circle hd.x₂_pos.le (by norm_num)
      (by nlinarith only [hq.1,hy.1,hy.2]) (by nlinarith only [hq.2,hy.1,hy.2])
  have hY : 1.4589 ≤ d.y₃ ∧ d.y₃ ≤ 1.4644 :=
    circle_coordinate_bounds (q:=d.q) (x:=d.y₃) (y:=d.x₂-3)
      (by simpa only [x₃,add_comm] using hd.third_circle)
      hd.y₃_pos.le (by norm_num)
      (by nlinarith only [hq.1,hU.1,hU.2]) (by nlinarith only [hq.2,hU.1,hU.2])
  norm_num [h₂,c,s,y₄,hz,halfAngleCos,halfAngleSin]
  constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]

/-- The same two circle equations bound the height at the upper tilt. -/
theorem upper_tilt_height {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156)
    (hy : -0.908 ≤ d.y ∧ d.y ≤ -0.895)
    (hw : -1.9049 ≤ d.x₄ ∧ d.x₄ ≤ -1.8974) (hz : d.z = 81/1000) :
    -29/20 ≤ d.h₂ ∧ d.h₂ ≤ -7/5 := by
  have hU : 1.6414 ≤ d.x₂ ∧ d.x₂ ≤ 1.6502 :=
    circle_coordinate_bounds hd.second_circle hd.x₂_pos.le (by norm_num)
      (by nlinarith only [hq.1,hy.1,hy.2]) (by nlinarith only [hq.2,hy.1,hy.2])
  have hY : 1.4386 ≤ d.y₃ ∧ d.y₃ ≤ 1.4471 :=
    circle_coordinate_bounds (q:=d.q) (x:=d.y₃) (y:=d.x₂-3)
      (by simpa only [x₃,add_comm] using hd.third_circle)
      hd.y₃_pos.le (by norm_num)
      (by nlinarith only [hq.1,hU.1,hU.2]) (by nlinarith only [hq.2,hU.1,hU.2])
  norm_num [h₂,c,s,y₄,hz,halfAngleCos,halfAngleSin]
  constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]

/-- At the lower tilt, the coarse circle bounds already give a positive reserve margin. -/
theorem lower_tilt_margin {d : Coordinates}
    (hU : 1.6414 ≤ d.x₂ ∧ d.x₂ ≤ 1.6691)
    (hY : 1.4387 ≤ d.y₃ ∧ d.y₃ ≤ 1.4643)
    (hw : 1.8974 ≤ -d.x₄ ∧ -d.x₄ ≤ 1.9049) (hz : d.z = 1/20) :
    1/40 ≤ (1057/1000)*(d.c+d.s*d.y₄/d.x₄)*(-d.x₃)/d.y₃-d.h₂tilt := by
  have hv : 0.5357 ≤ -d.y₄ ∧ -d.y₄ ≤ 0.5613 := by
    dsimp only [y₄]; constructor <;> linarith only [hY.1,hY.2]
  have hV : 1.3309 ≤ -d.x₃ ∧ -d.x₃ ≤ 1.3586 := by
    dsimp only [x₃]; constructor <;> linarith only [hU.1,hU.2]
  have hr₀ := positive_quotient_bounds hv hw (by norm_num) (by norm_num)
  rw [neg_div_neg_eq] at hr₀
  have hR₀ := positive_quotient_bounds hV hY (by norm_num) (by norm_num)
  have hR : 0.9088 ≤ (-d.x₃)/d.y₃ := by linarith only [hR₀.1]
  have hc : d.c = 399/401 := by norm_num [c,hz,halfAngleCos]
  have hs : d.s = 40/401 := by norm_num [s,hz,halfAngleSin]
  have hL : 1.023 ≤ d.c+d.s*d.y₄/d.x₄ := by
    rw [hc,hs,mul_div_assoc]
    linarith only [hr₀.1]
  have hE : d.h₂tilt ≤ 0.9564 := by
    dsimp only [h₂tilt]
    rw [hc,hs]
    linarith only [hw.2,hv.2]
  have hp := mul_le_mul hL hR (by norm_num : (0:ℝ) ≤ 0.9088)
    (by linarith only [hL] : 0 ≤ d.c+d.s*d.y₄/d.x₄)
  have heq : (1057/1000:ℝ)*(d.c+d.s*d.y₄/d.x₄)*(-d.x₃)/d.y₃ =
      (1057/1000)*((d.c+d.s*d.y₄/d.x₄)*((-d.x₃)/d.y₃)) := by ring
  rw [heq]
  linarith only [hp,hE]


def edgeAlpha (d : Coordinates) : ℝ := d.lam 0
def edgeBeta (d : Coordinates) : ℝ := d.lam 1
def edgeDelta (d : Coordinates) : ℝ := d.lam 3
def edgeOmega (d : Coordinates) : ℝ := d.lam 4
def edgeEpsilon (d : Coordinates) : ℝ := d.lam 6
def cutY (d : Coordinates) : ℝ := d.x₁-d.x₂
def cutJ (d : Coordinates) : ℝ := d.edgeEpsilon*d.c/d.edgeBeta-d.y₃*d.x₄/d.x₃
def cutX (d : Coordinates) : ℝ := d.edgeBeta*(d.y+2+d.cutJ)
def cutK (d : Coordinates) : ℝ := d.edgeBeta*(d.y₃+d.cutJ)
def cutL (d : Coordinates) : ℝ := d.edgeEpsilon*d.s*d.y₄/d.x₄
def cutN (d : Coordinates) : ℝ := -d.edgeEpsilon*(d.h₁+d.h₂tilt)
def ownerReserve (d : Coordinates) : Fin 9 → ℝ :=
  ![d.cutX,d.edgeAlpha*(1-d.cutY)-d.cutX,d.cutK,d.edgeBeta-d.cutK,
    d.edgeBeta*(-917/1000-d.cutJ),d.edgeBeta*(1057/1000+d.cutJ),
    d.cutL,d.cutN-(392/1000)*d.edgeOmega,(485/1000)*d.edgeOmega-d.cutN]

theorem cut_identities {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) :
    d.cutK=d.edgeEpsilon*d.c+d.edgeDelta*(d.x₄-d.x₃) ∧
      d.cutL=d.edgeDelta-d.edgeEpsilon*d.c ∧
      d.edgeDelta*d.x₃= -d.edgeBeta*d.y₃ := by
  have hlast := d.last_force_residual hw
  rw [hy,neg_zero,zero_div] at hlast
  have hx₃ := ne_of_lt hw.x₃_neg
  have hx₄ := ne_of_lt hw.x₄_neg
  have hm := ne_of_gt hw.weightMass_pos
  have hbeta := ne_of_gt (hw.lam_pos 1)
  have hβ := ne_of_gt hw.rawBeta_pos
  constructor
  · dsimp [cutK,cutJ,edgeBeta,edgeDelta,edgeEpsilon,lam,rawLambda,
      rawDelta,rawMuD] at *
    field_simp [hx₃,hx₄,hm,hbeta,hβ]
    ring
  constructor
  · dsimp [cutL,edgeDelta,edgeEpsilon,lam,rawLambda]
    dsimp [rawMuE] at hlast
    field_simp [hx₄] at hlast
    field_simp [hm,hx₄]
    linarith only [hlast]
  · dsimp [edgeDelta,edgeBeta,lam,rawLambda,rawDelta,rawMuD]
    field_simp [hm,hx₃]

/-- The force ratio between TB and HE is the product of two circle-chain slopes. -/
theorem edgeBeta_force_balance {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) :
    d.edgeBeta = d.edgeEpsilon*((d.c+d.s*d.y₄/d.x₄)*(-d.x₃)/d.y₃) := by
  have hβ : d.rawBeta = d.rawDelta*(-d.x₃)/d.y₃ := by
    dsimp only [rawDelta,rawMuD]
    field_simp [ne_of_lt hw.x₃_neg,ne_of_gt hw.y₃_pos]
  change d.rawBeta/d.weightMass = d.rawEpsilon/d.weightMass*_
  rw [hβ,hw.delta_force_balance hy]
  ring

/-- The E force balance cancels the quotient in the cut `J`. -/
theorem cutJ_force_balance {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) :
    d.edgeBeta*d.cutJ = -d.edgeEpsilon*d.h₂tilt := by
  have hx₃ := ne_of_lt hw.x₃_neg
  have hx₄ := ne_of_lt hw.x₄_neg
  have hβ : d.edgeBeta ≠ 0 := ne_of_gt (hw.lam_pos 1)
  have hδ : d.edgeDelta = d.edgeEpsilon*(d.c+d.s*d.y₄/d.x₄) := by
    change d.rawDelta/d.weightMass = d.rawEpsilon/d.weightMass*(d.c+d.s*d.y₄/d.x₄)
    rw [hw.delta_force_balance hy]
    ring
  have hβY : d.edgeBeta*d.y₃ = -d.edgeDelta*d.x₃ := by
    have h := (cut_identities hw hy).2.2
    linarith only [h]
  calc d.edgeBeta*d.cutJ = d.edgeEpsilon*d.c-d.edgeBeta*d.y₃*d.x₄/d.x₃ := by
        dsimp only [cutJ]
        field_simp [hβ]
    _ = d.edgeEpsilon*d.c+d.edgeDelta*d.x₄ := by
        rw [hβY]
        field_simp [hx₃]
        ring
    _ = _ := by
        rw [hδ]
        dsimp only [h₂tilt]
        field_simp [hx₄]
        ring

/-- Force balance removes the quotient in `cutJ` from the two neighbouring cuts. -/
theorem cut_expansions {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) :
    d.cutX=d.edgeAlpha*d.x₂-d.edgeEpsilon*d.h₂tilt ∧
    d.cutK=d.edgeBeta*d.y₃-d.edgeEpsilon*d.h₂tilt := by
  have hJ := cutJ_force_balance hw hy
  have hα : d.edgeAlpha*d.x₂ = d.edgeBeta*(d.y+2) := by
    dsimp only [edgeAlpha,edgeBeta,lam,rawLambda,Matrix.cons_val,rawBeta]
    field_simp [ne_of_gt hw.weightMass_pos,ne_of_gt hw.y_add_two_pos]
  constructor
  · rw [cutX,mul_add,hJ,←hα]
    ring
  · rw [cutK,mul_add,hJ]
    ring

/-- Five owner reserves follow from the contact proportions and coarse coordinate bounds. -/
theorem geometric_owner_bounds {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) (hb : WeightBounds d) (hc : ContactBounds d) :
    1/80 ≤ d.ownerReserve 1 ∧ 1/80 ≤ d.ownerReserve 2 ∧
    1/80 ≤ d.ownerReserve 3 ∧ 1/80 ≤ d.ownerReserve 4 ∧ 1/80 ≤ d.ownerReserve 6 := by
  have hε : 2/3 ≤ d.edgeEpsilon := hc.epsilon_lower
  have hε₀ : 0 ≤ d.edgeEpsilon := (hw.lam_pos 6).le
  have hα : 0 ≤ d.edgeAlpha ∧ d.edgeAlpha ≤ 0.7*d.edgeEpsilon :=
    ⟨(hw.lam_pos 0).le,hc.alpha_le_epsilon⟩
  have hβ : 0.9*d.edgeEpsilon ≤ d.edgeBeta ∧ d.edgeBeta ≤ 0.99*d.edgeEpsilon :=
    ⟨hc.beta_lower,hc.beta_upper⟩
  obtain ⟨hvw,_,hE⟩ := hb.frame_bounds
  have hEl := mul_le_mul_of_nonneg_left hE.1 hε₀
  have hEu := mul_le_mul_of_nonneg_left hE.2 hε₀
  have hr : 0.7428 ≤ d.x₁-1 ∧ d.x₁-1 ≤ 0.7649 := by
    constructor <;> linarith only [hb.x₁]
  have hαr := positive_product_bounds hα hr (by norm_num) (by norm_num)
  have hβY := positive_product_bounds hβ hb.y₃ (by positivity) (by norm_num)
  have hYm : 0.4387 ≤ d.y₃-1 ∧ d.y₃-1 ≤ 0.4643 := by
    constructor <;> linarith only [hb.y₃]
  have hβYm := positive_product_bounds hβ hYm (by positivity) (by norm_num)
  have hs : 0.099 ≤ d.s ∧ d.s ≤ 0.162 :=
    ⟨(halfAngle_local_bounds hb.z).2.2.1,(halfAngle_local_bounds hb.z).2.2.2⟩
  have hsr := positive_product_bounds hs hvw (by norm_num) (by norm_num)
  have hL := mul_le_mul_of_nonneg_left hsr.1 hε₀
  obtain ⟨hX,hK⟩ := cut_expansions hw hy
  refine ⟨?_,?_,?_,?_,?_⟩
  · change 1/80 ≤ d.edgeAlpha*(1-d.cutY)-d.cutX
    rw [hX]
    have he : d.edgeAlpha*(1-d.cutY)-(d.edgeAlpha*d.x₂-d.edgeEpsilon*d.h₂tilt) =
        d.edgeEpsilon*d.h₂tilt-d.edgeAlpha*(d.x₁-1) := by dsimp only [cutY]; ring
    rw [he]
    linarith only [hEl,hαr.2,hε]
  · change 1/80 ≤ d.cutK
    rw [hK]
    linarith only [hβY.1,hEu,hε]
  · change 1/80 ≤ d.edgeBeta-d.cutK
    rw [hK]
    have he : d.edgeBeta-(d.edgeBeta*d.y₃-d.edgeEpsilon*d.h₂tilt) =
        d.edgeEpsilon*d.h₂tilt-d.edgeBeta*(d.y₃-1) := by ring
    rw [he]
    linarith only [hEl,hβYm.2,hε]
  · change 1/80 ≤ d.edgeBeta*(-917/1000-d.cutJ)
    have he : d.edgeBeta*(-917/1000-d.cutJ) =
        d.edgeEpsilon*d.h₂tilt-(917/1000)*d.edgeBeta := by
      linear_combination -(cutJ_force_balance hw hy)
    rw [he]
    linarith only [hEl,hβ.2,hε]
  · change 1/80 ≤ d.cutL
    have he : d.cutL = d.edgeEpsilon*(d.s*(d.y₄/d.x₄)) := by dsimp only [cutL]; ring
    rw [he]
    linarith only [hL,hε]

/-- The positive margin bounds reserve 5, and reserve 0 is larger. -/
theorem margin_owner_bounds {d : Coordinates} (hw : d.WeightDomain)
    (hy : d.positionDerivative=0) (hb : WeightBounds d) (hc : ContactBounds d)
    (hm : 1/40 ≤ (1057/1000)*(d.c+d.s*d.y₄/d.x₄)*(-d.x₃)/d.y₃-d.h₂tilt) :
    1/80 ≤ d.ownerReserve 0 ∧ 1/80 ≤ d.ownerReserve 5 := by
  have hβ := edgeBeta_force_balance hw hy
  have hJ := cutJ_force_balance hw hy
  have h₅ : d.ownerReserve 5 = d.edgeEpsilon*
      ((1057/1000)*(d.c+d.s*d.y₄/d.x₄)*(-d.x₃)/d.y₃-d.h₂tilt) := by
    change d.edgeBeta*(1057/1000+d.cutJ) = _
    linear_combination (1057/1000)*hβ+hJ
  have hε : (2/3:ℝ) ≤ d.edgeEpsilon := hc.epsilon_lower
  have hε₀ : 0 ≤ d.edgeEpsilon := (hw.lam_pos 6).le
  have hprod := mul_le_mul hε hm (by norm_num : (0:ℝ) ≤ 1/40) hε₀
  have hlo : 1/80 ≤ d.ownerReserve 5 := by rw [h₅]; linarith only [hprod]
  have hd := mul_nonneg (hw.lam_pos 1).le
    (show 0 ≤ d.y+2-1057/1000 by linarith only [hb.y.1])
  have horder : d.ownerReserve 5 ≤ d.ownerReserve 0 := by
    change d.edgeBeta*(1057/1000+d.cutJ) ≤ d.edgeBeta*(d.y+2+d.cutJ)
    change 0 ≤ d.edgeBeta*(d.y+2-1057/1000) at hd
    linarith only [hd]
  exact ⟨hlo.trans horder,hlo⟩

theorem omega_lower {d : Coordinates} (hw : d.WeightDomain) (hb : WeightBounds d) (hc : ContactBounds d) :
    3/5 ≤ d.edgeOmega := by
  have hratio := positive_quotient_bounds hb.h₁ hb.h₂ (by norm_num) (by norm_num)
  have hR : 0.9 ≤ (-d.h₁)/(-d.h₂) := by linarith only [hratio.1]
  have heq : d.edgeOmega = d.edgeEpsilon*((-d.h₁)/(-d.h₂)) := by
    simp only [edgeOmega,edgeEpsilon,lam,rawLambda,rawEpsilon,Matrix.cons_val]
    field_simp [ne_of_lt hw.h₁_neg,ne_of_lt hw.h₂_neg,ne_of_gt hw.weightMass_pos]
  have hp := mul_le_mul hc.epsilon_lower hR (by norm_num : (0:ℝ) ≤ 0.9) (hw.lam_pos 6).le
  rw [heq]
  change (2/3:ℝ)*0.9 ≤ d.edgeEpsilon*((-d.h₁)/(-d.h₂)) at hp
  linarith only [hp]

theorem cut_owner_bounds {d : Coordinates} (hw : d.WeightDomain) (hb : WeightBounds d) (hc : ContactBounds d)
    (hN : 0.412 ≤ -d.rawEpsilon*(d.h₁+d.h₂tilt) ∧ -d.rawEpsilon*(d.h₁+d.h₂tilt) ≤ 0.44) :
    3/250 ≤ d.ownerReserve 7 ∧ 3/250 ≤ d.ownerReserve 8 := by
  have hω := omega_lower hw hb hc
  have hω₀ : 0 ≤ d.edgeOmega := (hw.lam_pos 4).le
  have h₇ : 1/50 ≤ -d.rawEpsilon*(d.h₁+d.h₂tilt)-392/1000 := by linarith only [hN.1]
  have h₈ : 9/200 ≤ 485/1000-(-d.rawEpsilon*(d.h₁+d.h₂tilt)) := by linarith only [hN.2]
  have hp₇ := mul_le_mul hω h₇ (by norm_num : (0:ℝ) ≤ 1/50) hω₀
  have hp₈ := mul_le_mul hω h₈ (by norm_num : (0:ℝ) ≤ 9/200) hω₀
  have heq : d.cutN = d.edgeOmega*(-d.rawEpsilon*(d.h₁+d.h₂tilt)) := by
    simp only [cutN,edgeOmega,edgeEpsilon,lam,rawLambda,Matrix.cons_val]
    ring
  constructor
  · change 3/250 ≤ d.cutN-(392/1000)*d.edgeOmega
    rw [heq]
    linarith only [hp₇]
  · change 3/250 ≤ (485/1000)*d.edgeOmega-d.cutN
    rw [heq]
    linarith only [hp₈]

end Coordinates

/-- The coarse circle bounds give the reserve margin on the entire lower-tilt face. -/
theorem familyMargin_lower_tilt {q y : ℝ} (hq : q ∈ radiusBox)
    (hy : y ∈ Icc (-(937/1000)) (-(179/200))) :
    1/40 ≤ familyMargin q (y,1/20) := by
  have hz : (1/20:ℝ) ∈ tiltBox := by norm_num [tiltBox]
  obtain ⟨_,_,hUl,hUu,hYl,hYu,hwl,hwu,_⟩ := radical_coordinate_bounds (y:=y) hq
    ⟨by linarith only [hy.1],by linarith only [hy.2]⟩ hz
  rw [familyMargin_coordinates]
  apply Coordinates.lower_tilt_margin (d:=radicalCoordinates q y (1/20)) ?_ ?_ ?_ rfl
  · constructor <;> linarith only [hUl,hUu]
  · constructor <;> linarith only [hYl,hYu]
  · constructor <;> linarith only [hwl,hwu]

section MidpointCuts
open Coordinates FiveCornerGeometry

/-- Products and positive quotients bound the cut and its angle slope at the left position. -/
theorem left_projection_bounds {K H E T : ℝ}
    (hK : 1.3855 ≤ K ∧ K ≤ 1.3858) (hH : 1.4129 ≤ H ∧ H ≤ 1.4135)
    (hE : 0.9668 ≤ E ∧ E ≤ 0.9672) (hT : 1.0258 ≤ T ∧ T ≤ 1.026) :
    (H/K)*(K-E) ≤ 0.428 ∧
    |-E+(E^2-H*(H-1))/K+H*E*T/K^2| ≤ 3/40 := by
  have hC : 0 ≤ K-E ∧ K-E ≤ 0.419 := by constructor <;> linarith only [hK,hE]
  have hratio := positive_quotient_bounds hH hK (by norm_num) (by norm_num)
  have hN := positive_product_bounds hratio hC (by norm_num) (by norm_num)
  have hE2 := positive_product_bounds hE hE (by norm_num) (by norm_num)
  have hH1 : 0.4129 ≤ H-1 ∧ H-1 ≤ 0.4135 := by constructor <;> linarith only [hH]
  have hHH := positive_product_bounds hH hH1 (by norm_num) (by norm_num)
  have hP : 0.34 ≤ E^2-H*(H-1) ∧ E^2-H*(H-1) ≤ 0.36 := by
    rw [pow_two]; constructor <;> linarith only [hE2,hHH]
  have hPK := positive_quotient_bounds hP hK (by norm_num) (by norm_num)
  have hK2 := positive_product_bounds hK hK (by norm_num) (by norm_num)
  have hHET := positive_product_bounds
    (positive_product_bounds hH hE (by norm_num) (by norm_num)) hT (by norm_num) (by norm_num)
  have hQ := positive_quotient_bounds hHET hK2 (by norm_num) (by norm_num)
  constructor
  · linarith only [hN.2]
  · rw [abs_le]
    simp only [pow_two] at hPK ⊢
    constructor <;> linarith only [hE.1,hE.2,hPK.1,hPK.2,hQ.1,hQ.2]

/-- The same comparison bounds the cut and angle slope at the right position. -/
theorem right_projection_bounds {K H E T : ℝ}
    (hK : 1.3582 ≤ K ∧ K ≤ 1.3586) (hH : 1.4392 ≤ H ∧ H ≤ 1.4396)
    (hE : 0.9629 ≤ E ∧ E ≤ 0.9632) (hT : 0.987 ≤ T ∧ T ≤ 0.9872) :
    0.418 ≤ (H/K)*(K-E) ∧
    |-E+(E^2-H*(H-1))/K+H*E*T/K^2| ≤ 1/40 := by
  have hC : 0.395 ≤ K-E ∧ K-E ≤ 0.396 := by constructor <;> linarith only [hK,hE]
  have hratio := positive_quotient_bounds hH hK (by norm_num) (by norm_num)
  have hN := positive_product_bounds hratio hC (by norm_num) (by norm_num)
  have hE2 := positive_product_bounds hE hE (by norm_num) (by norm_num)
  have hH1 : 0.4392 ≤ H-1 ∧ H-1 ≤ 0.4396 := by constructor <;> linarith only [hH]
  have hHH := positive_product_bounds hH hH1 (by norm_num) (by norm_num)
  have hP : 0.29 ≤ E^2-H*(H-1) ∧ E^2-H*(H-1) ≤ 0.30 := by
    rw [pow_two]; constructor <;> linarith only [hE2,hHH]
  have hPK := positive_quotient_bounds hP hK (by norm_num) (by norm_num)
  have hK2 := positive_product_bounds hK hK (by norm_num) (by norm_num)
  have hHET := positive_product_bounds
    (positive_product_bounds hH hE (by norm_num) (by norm_num)) hT (by norm_num) (by norm_num)
  have hQ := positive_quotient_bounds hHET hK2 (by norm_num) (by norm_num)
  constructor
  · linarith only [hN.1]
  · rw [abs_le]
    simp only [pow_two] at hPK ⊢
    constructor <;> linarith only [hE.1,hE.2,hPK.1,hPK.2,hQ.1,hQ.2]

/-- The cut and its angle derivative in circle coordinates. -/
theorem coordinate_cut_values {d : Coordinates} (hd : d.IsChain) :
    rawCut d.q d.c d.s (-d.y) = (-d.h₂)/(-d.h₁)*((-d.h₁)-d.h₂tilt) ∧
    rawCutAngle d.q d.c d.s (-d.y) =
      (let K := -d.h₁; let H := -d.h₂; let E := d.h₂tilt;
      let T := d.s*(d.x₁-1)-d.c*d.y;
      -E+(E^2-H*(H-1))/K+H*E*T/K^2) := by
  obtain ⟨hr,_,_,_,hv,hw⟩ := coordinate_values hd
  have hK : firstComponent d.q d.c d.s (-d.y) = -d.h₁ := by
    rw [firstComponent,hr]; dsimp only [h₁]; ring
  have hH : secondComponent d.q d.c d.s (-d.y) = -d.h₂ := by
    rw [secondComponent,hv,hw]; dsimp only [h₂]; ring
  have he : secondTilt d.q d.c d.s (-d.y) = -d.h₂tilt := by
    rw [secondTilt,hv,hw]; dsimp only [h₂tilt]; ring
  have hT : firstTilt d.q d.c d.s (-d.y) = d.s*(d.x₁-1)-d.c*d.y := by
    rw [firstTilt,hr]; ring
  constructor
  · rw [rawCut,hK,hH,he]; ring
  · dsimp only [rawCutAngle]
    rw [hK,hH,he,hT]
    ring

namespace Coordinates

/-- The midpoint cut is bounded above on the left position face. -/
theorem left_midpoint_cut {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156) (hy : d.y = -937/1000) (hz : d.z = 131/2000) :
    rawCut d.q d.c d.s (-d.y) ≤ 0.428 ∧ |rawCutAngle d.q d.c d.s (-d.y)| ≤ 3/40 := by
  obtain ⟨hr,_,hY,hw⟩ := left_circle_bounds hd hq hy
  have hc : d.c = 3982839/4017161 := by norm_num [c,hz,halfAngleCos]
  have hs : d.s = 524000/4017161 := by norm_num [s,hz,halfAngleSin]
  rw [(coordinate_cut_values hd).1,(coordinate_cut_values hd).2]
  apply left_projection_bounds
  · dsimp only [h₁]; rw [hc,hs,hy]
    constructor <;> linarith only [hr.1,hr.2]
  · dsimp only [h₂,y₄]; rw [hc,hs]
    constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]
  · dsimp only [h₂tilt,y₄]; rw [hc,hs]
    constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]
  · rw [hc,hs,hy]
    constructor <;> linarith only [hr.1,hr.2]

/-- The midpoint cut is bounded below on the right position face. -/
theorem right_midpoint_cut {d : Coordinates} (hd : d.IsChain)
    (hq : 3.9155 ≤ d.q ∧ d.q ≤ 3.9156) (hy : d.y = -179/200) (hz : d.z = 131/2000) :
    0.418 ≤ rawCut d.q d.c d.s (-d.y) ∧ |rawCutAngle d.q d.c d.s (-d.y)| ≤ 1/40 := by
  obtain ⟨hr,_,hY,hw⟩ := right_circle_bounds hd hq hy
  have hc : d.c = 3982839/4017161 := by norm_num [c,hz,halfAngleCos]
  have hs : d.s = 524000/4017161 := by norm_num [s,hz,halfAngleSin]
  rw [(coordinate_cut_values hd).1,(coordinate_cut_values hd).2]
  apply right_projection_bounds
  · dsimp only [h₁]; rw [hc,hs,hy]
    constructor <;> linarith only [hr.1,hr.2]
  · dsimp only [h₂,y₄]; rw [hc,hs]
    constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]
  · dsimp only [h₂tilt,y₄]; rw [hc,hs]
    constructor <;> linarith only [hY.1,hY.2,hw.1,hw.2]
  · rw [hc,hs,hy]
    constructor <;> linarith only [hr.1,hr.2]

end Coordinates

end MidpointCuts

end SquaresInCircles.Eight.ExactFamily
