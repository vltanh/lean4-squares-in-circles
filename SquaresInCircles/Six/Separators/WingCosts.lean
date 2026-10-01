import SquaresInCircles.Six.Separators.Profiles

/-!
# Six squares: the cost of a wing separated along the secondary axis of D

Bounds for the terms of a square W or S in a double separation at D, where W–D
and D–S are both separated along the secondary axis of D. A square with equal
weights on its own axis and on the secondary axis of D, at phase gap `q`, has
the force `(1 + sin q, cos q)`; its cost
`(|cos q| + |sin q|)/2 - (1 + sin q) a - (cos q) b` exceeds
`-91/125 - (13/20) q` for `1/2 ≤ q ≤ π/2`: by the far-vertex support, with the
length `√(2 + 2 sin q)` below its tangent at `49/16`, for `q ≤ 1`, and by the
cap support and a Taylor expansion at `13/10` beyond. Beyond `π/2` the
reflection `q ↦ π - q` folds the angle back. A square separated from C along the
matching side of C has a force of length `2 cos (π/4 - d/2)` for W or
`2 cos (d/2)` for S, whatever its angle, and the widths of its two edges satisfy
a triangle inequality. For the mixed cases, two reserves in `d` (and in the
angle of S) follow from Taylor bounds and concavity.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- `|sin h - h| ≤ h²/12` for `|h| ≤ 1/2`. -/
lemma sine_error_on_half {h : ℝ} (hh : |h|≤1/2) :
    -(h^2)/12≤Real.sin h-h ∧ Real.sin h-h≤h^2/12 := by
  have hp := mul_le_mul_of_nonneg_left hh (sq_nonneg |h|)
  have hc : |h|^3/6≤h^2/12 := by rw [← sq_abs]; nlinarith only [hp]
  have he := abs_le.mp ((Real.abs_sub_sin_le h).trans hc)
  constructor <;> linarith [he.1,he.2]

/-- The cost bound in the cap case, plus `91/125 + (13/20) q`. -/
def secondaryCapLine (q : ℝ) : ℝ :=
  91/125-1113/1000+(13/20)*q+Real.cos q/2-(613/1000)*Real.sin q

private def tangentA : ℝ := Real.cos (13/10)/2-(613/1000)*Real.sin (13/10)
private def tangentB : ℝ := -Real.sin (13/10)/2-(613/1000)*Real.cos (13/10)

private lemma secondary_tangent_constants :
    tangentA≤-9/20 ∧ -33/50≤tangentB ∧ tangentB≤0 ∧
      |13/20+tangentB|≤1/200 ∧ 1/500≤ secondaryCapLine (13/10) := by
  have hcl := cos_lower_six (x := (13:ℝ)/10) (by norm_num)
  have hcu := cos_upper_four (x := (13:ℝ)/10) (by norm_num)
  have hsl := sin_lower_seven (x := (13:ℝ)/10) (by norm_num)
  have hsu := sin_upper_five (x := (13:ℝ)/10) (by norm_num)
  norm_num at hcl hcu hsl hsu
  dsimp [tangentA,tangentB,secondaryCapLine]
  refine ⟨?_,?_,?_,?_,?_⟩
  · linarith
  · linarith
  · linarith
  · apply abs_le.mpr
    constructor <;> linarith
  · linarith

lemma secondary_cap_line_expansion (h : ℝ) :
    secondaryCapLine (13/10+h)=secondaryCapLine (13/10)+(13/20+tangentB)*h+
      tangentA*(Real.cos h-1)+tangentB*(Real.sin h-h) := by
  dsimp [secondaryCapLine,tangentA,tangentB]
  rw [Real.cos_add,Real.sin_add]
  ring

/-- The cap case: `secondaryCapLine` is positive on `[1, π/2]`. -/
theorem secondary_cap_line_positive {q : ℝ} (hq : 1≤q ∧ q≤Real.pi/2) :
    0< secondaryCapLine q := by
  let h := q-13/10
  have hh : |h|≤1/2 := by
    apply abs_le.mpr
    dsimp [h]
    constructor <;> linarith [hq.1,hq.2,Real.pi_lt_d2]
  obtain ⟨hA,hBl,hBu,hBlin,hbase⟩ := secondary_tangent_constants
  have hA0 : tangentA≤0 := by linarith
  have hc := cos_le_one_sub_fifth_sq
    (hh.trans (by linarith [Real.pi_gt_d2] : (1:ℝ)/2≤Real.pi))
  have hcm := mul_le_mul_of_nonpos_left hc hA0
  have hAreserve := mul_nonneg (show 0≤-tangentA-9/20 by linarith)
    (show 0≤h^2/5 by positivity)
  have hAsq : (9/100)*h^2≤tangentA*(Real.cos h-1) := by
    nlinarith only [hcm,hAreserve]
  have hs := sine_error_on_half hh
  have hBm := mul_le_mul_of_nonpos_left hs.2 hBu
  have hBreserve := mul_nonneg (show 0≤tangentB+33/50 by linarith)
    (show 0≤h^2/12 by positivity)
  have hBsq : -(11/200)*h^2≤tangentB*(Real.sin h-h) := by
    nlinarith only [hBm,hBreserve]
  have hlinabs := mul_le_mul_of_nonneg_right hBlin (abs_nonneg h)
  rw [← abs_mul] at hlinabs
  have hlin : -(1/200)*|h|≤(13/20+tangentB)*h := by
    nlinarith only [hlinabs,neg_le_abs ((13/20+tangentB)*h)]
  have hid : secondaryCapLine q=secondaryCapLine (13/10)+(13/20+tangentB)*h+
      tangentA*(Real.cos h-1)+tangentB*(Real.sin h-h) := by
    have he : q=13/10+h := by dsimp [h]; ring
    rw [he,secondary_cap_line_expansion]
  have hsquare := sq_nonneg (14*|h|-1)
  have hsqabs := sq_abs h
  nlinarith only [hid,hbase,hAsq,hBsq,hlin,hsquare,hsqabs]

/-- The vertex case: with the tangent at `49/16` of the length `√(2 + 2 sin q)`,
the cost bound plus `91/125 + (13/20) q` is a linear function plus a first
harmonic with nonnegative coefficients, positive at `q = 1/2` and `q = 1`. -/
private lemma secondary_vertex_positive {q : ℝ} (hq : 1/2≤q ∧ q≤1) :
    0<91/125+(13/20)*q+1/2+Real.cos q+Real.sin q-
      (1689/1000)*((2+2*Real.sin q+(7/4)^2)/(2*(7/4))) := by
  have hl := trig_bracket (l := 1/2) (u := 1/2) (x := 1/2) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  have hu := trig_bracket (l := 1) (u := 1) (x := 1) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at hl hu
  have h := trig_concave_gt (α := 13/20) (A := 1-(1689/1000)*(4/7)) (B := 1)
    (m := (1689/1000)*(81/56)-91/125-1/2) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) hq (by linarith) (by linarith)
  ring_nf at h ⊢
  linarith

private lemma secondary_cap_slope {q : ℝ} (hq : 1≤q ∧ q≤Real.pi/2) :
    (rho0+1/2)*Real.cos q≤(1+Real.sin q)/2 := by
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(1:ℝ) by linarith [Real.pi_pos]) hq.2 hq.1
  have hs1 := Real.sin_ge_sub_cube (x := (1:ℝ)) (by norm_num)
  norm_num at hs1
  have hslo : 5/6≤Real.sin q := by linarith
  have hc0 := Real.cos_nonneg_of_mem_Icc
    (show q∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  have hsq := mul_nonneg (sub_nonneg.mpr hslo)
    (show 0≤Real.sin q+5/6 by linarith)
  have hchi : Real.cos q≤5/9 := by nlinarith [Real.sin_sq_add_cos_sq q]
  have hm := mul_le_mul (show rho0+1/2≤1613/1000 by linarith [rho0_bounds.2])
    hchi hc0 (by norm_num : (0:ℝ)≤1613/1000)
  nlinarith

/-- The cost `(|cos q| + |sin q|)/2 - (1 + sin q) a - (cos q) b` of a square with
equal weights on its own axis and on the secondary axis of D, at phase gap
`q ∈ [1/2, π/2]`, exceeds `-91/125 - (13/20) q`. -/
lemma secondary_cost_first_quadrant {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2≤q ∧ q≤Real.pi/2) :
    -91/125-(13/20)*q<angularWidth q-((1+Real.sin q)*a+Real.cos q*b) := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show q∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_pos])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi (x := q)
    (by linarith [hq.1]) (by linarith [hq.2,Real.pi_pos])
  have hc' : ContainedChart a |-b| := by simpa only [abs_neg] using hc
  rw [angularWidth,abs_of_nonneg hcos,abs_of_nonneg hsin]
  by_cases hsmall : q≤1
  · have hL := sq_le_tangent_sq (y := 2+2*Real.sin q) (show (0:ℝ)<7/4 by norm_num)
    have hp := vertex_linear_upper hc' (U := 1+Real.sin q) (V := Real.cos q)
      (L := (2+2*Real.sin q+(7/4)^2)/(2*(7/4))) hcos
      (div_nonneg (by linarith [Real.neg_one_le_sin q]) (by norm_num))
      (by nlinarith [Real.sin_sq_add_cos_sq q])
    have hpositive := secondary_vertex_positive ⟨hq.1,hsmall⟩
    nlinarith only [hp,hpositive]
  · have hp := cap_linear_upper hc' (U := 1+Real.sin q) (V := Real.cos q)
      (by linarith) hcos (secondary_cap_slope ⟨(lt_of_not_ge hsmall).le,hq.2⟩)
    have hpositive := secondary_cap_line_positive ⟨(lt_of_not_ge hsmall).le,hq.2⟩
    dsimp [secondaryCapLine] at hpositive
    nlinarith only [hp,hpositive]

/-- The angle `q` folded into `[0, π/2]`: `q` itself up to `π/2`, then `π - q`. -/
def foldedSecondaryAngle (q : ℝ) : ℝ := Real.pi/2-|q-Real.pi/2|

lemma foldedSecondaryAngle_le (q : ℝ) : foldedSecondaryAngle q≤q := by
  dsimp [foldedSecondaryAngle]
  linarith [neg_abs_le (q-Real.pi/2)]

/-- The cost bound on `[1/2, π - 1/2]`, with the folded angle. -/
lemma secondary_cost_folded_lower {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2≤q ∧ q≤Real.pi-1/2) :
    -91/125-(13/20)*foldedSecondaryAngle q<
      angularWidth q-((1+Real.sin q)*a+Real.cos q*b) := by
  by_cases hhalf : q≤Real.pi/2
  · have hh := secondary_cost_first_quadrant hc ⟨hq.1,hhalf⟩
    have he : foldedSecondaryAngle q=q := by
      rw [foldedSecondaryAngle,abs_of_nonpos (by linarith)]
      ring
    simpa only [he] using hh
  · have hc' : ContainedChart a |-b| := by simpa only [abs_neg] using hc
    have hh := secondary_cost_first_quadrant hc'
      (q := Real.pi-q) ⟨by linarith [hq.2],by linarith⟩
    have he : foldedSecondaryAngle q=Real.pi-q := by
      rw [foldedSecondaryAngle,abs_of_nonneg (by linarith)]
      ring
    simp only [angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at hh ⊢
    rw [he]
    nlinarith only [hh]

/-- The affine bound `-91/125 - (13/20) q` on `[1/2, π - 1/2]`. -/
lemma secondary_cost_affine_lower {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2≤q ∧ q≤Real.pi-1/2) :
    -91/125-(13/20)*q<angularWidth q-((1+Real.sin q)*a+Real.cos q*b) := by
  linarith [secondary_cost_folded_lower hc hq,foldedSecondaryAngle_le q]

/-- The terms of an own wing S in the gap with W on the west side of C. -/
def ownWingPotential (s : ℝ) : ℝ :=
  (387/1000)*Real.cos s+|Real.sin s|/2+(113/1000)*Real.sin s

/-- `ownWingPotential s` for `s ≥ 0`. -/
def positiveWing (s : ℝ) : ℝ := (387/1000)*Real.cos s+(613/1000)*Real.sin s

lemma ownWingPotential_nonnegative_angle {s : ℝ} (hs : 0≤ s ∧ s≤Real.pi/4) :
    ownWingPotential s=positiveWing s := by
  have ht := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_pos])
  rw [ownWingPotential,abs_of_nonneg ht,positiveWing]
  ring

lemma ownWingPotential_negative_lower {s : ℝ} (hs : -5/8≤ s ∧ s≤0) :
    387/1000≤ownWingPotential s := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show s∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have ht := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤-s by linarith [hs.2]) (by linarith [hs.1,Real.pi_gt_d2])
  rw [Real.sin_neg] at ht
  have hw := one_le_abs_cos_add_abs_sin s
  rw [abs_of_nonneg hc,abs_of_nonpos (by linarith)] at hw
  rw [ownWingPotential,abs_of_nonpos (by linarith)]
  linarith

lemma positiveWing_minus_antitone :
    AntitoneOn (fun x : ℝ => positiveWing x-(13/20)*x) (Set.Icc 0 (Real.pi/4)) := by
  apply antiOn_of_hasDeriv_nonpos (by dsimp [positiveWing]; fun_prop)
  · intro x _
    exact (((Real.hasDerivAt_cos x).const_mul (387/1000)).fun_add
      ((Real.hasDerivAt_sin x).const_mul (613/1000))).fun_sub
      ((hasDerivAt_id' x).const_mul (13/20))
  · intro x hx
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le
      (by linarith [hx.2,Real.pi_pos])
    linarith [Real.cos_le_one x]

lemma positiveWing_plus_monotone :
    MonotoneOn (fun x : ℝ => positiveWing x+(13/20)*x) (Set.Icc 0 (Real.pi/4)) := by
  apply monoOn_of_hasDeriv_nonneg (by dsimp [positiveWing]; fun_prop)
  · intro x _
    exact (((Real.hasDerivAt_cos x).const_mul (387/1000)).fun_add
      ((Real.hasDerivAt_sin x).const_mul (613/1000))).fun_add
      ((hasDerivAt_id' x).const_mul (13/20))
  · intro x hx
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    linarith [Real.sin_le_one x]

/-- `G s + (13/20) |s - d|` is at least `G d`, for `0 ≤ d ≤ π/4`. -/
lemma own_wing_penalty_lower {s d : ℝ}
    (hs : -5/8≤ s ∧ s≤2/3) (hd : 0≤d ∧ d≤Real.pi/4) :
    positiveWing d≤ownWingPotential s+(13/20)*|s-d| := by
  by_cases hs0 : 0≤ s
  · have hspi : s≤Real.pi/4 := by linarith [hs.2,Real.pi_gt_d2]
    rw [ownWingPotential_nonnegative_angle ⟨hs0,hspi⟩]
    rcases le_total s d with hsd | hds
    · have hh := positiveWing_minus_antitone ⟨hs0,hspi⟩ hd hsd
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh := positiveWing_plus_monotone hd ⟨hs0,hspi⟩ hds
      rw [abs_of_nonneg (by linarith)]
      linarith
  · have hh := positiveWing_minus_antitone
      (show (0:ℝ)∈Set.Icc 0 (Real.pi/4) by constructor <;> linarith [Real.pi_pos]) hd hd.1
    have hp := ownWingPotential_negative_lower ⟨hs.1,(lt_of_not_ge hs0).le⟩
    norm_num [positiveWing] at hh
    rw [abs_of_nonpos (by linarith [hd.1]),positiveWing]
    linarith [lt_of_not_ge hs0]

/-- For `d ≥ 2/3`, `G s + (13/20) |s - d|` is at least its value at
`s = 2/3`. -/
lemma own_wing_penalty_endpoint {s d : ℝ}
    (hs : -5/8≤ s ∧ s≤2/3) (hd : 2/3≤d) :
    positiveWing (2/3)+(13/20)*(d-2/3)≤ownWingPotential s+(13/20)*|s-d| := by
  have hb := own_wing_penalty_lower hs
    (d := (2:ℝ)/3) ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
  rw [abs_of_nonpos (by linarith [hs.2])] at hb
  rw [abs_of_nonpos (by linarith [hs.2])]
  linarith

/-- The terms of the gap in the angle `x` of an own wing. -/
def ownWingCost (x : ℝ) : ℝ :=
  (387/1000)*Real.cos x+(613/1000)*Real.sin x-(13/20)*x

/-- `ownWingCost` exceeds `249/1000` on `[0, 2/3]`, by concavity. -/
lemma ownWingCost_lower {x : ℝ} (hx : 0≤x ∧ x≤2/3) : 249/1000<ownWingCost x := by
  have hconc := (harmonic_concave (A := 387/1000) (B := 613/1000) (l := 0) (u := 2/3)
    fun t ht => harmonic_nonneg (by norm_num) (by norm_num)
      ⟨ht.1,by linarith [ht.2,Real.pi_gt_d2]⟩).add (affine_concave (-(13/20)) 0 0 (2/3))
  have h := concave_gt_of_endpoints hconc hx (c := 249/1000) (by norm_num [harmonic])
    (by simp only [Pi.add_apply,harmonic]
        linarith [trig_bracket_two_thirds.1,trig_bracket_two_thirds.2.2.1])
  simp only [Pi.add_apply,harmonic] at h
  dsimp [ownWingCost]
  linarith

/-- For `|x| ≤ 2/5` and `1/2 ≤ d ≤ π/4`, the widths of the two edges of a wing on
a side of C satisfy `1/2 + aw(d) ≤ aw(x) + aw(d - x)`. -/
lemma cardinal_width_triangle {x d : ℝ}
    (hx : |x|≤2/5) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    1/2+angularWidth d≤angularWidth x+angularWidth (d-x) := by
  have hx' := abs_le.mp hx
  have hdtr := cos_sin_nonneg
    (show 0≤d ∧ d≤Real.pi/2 by constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hytr := cos_sin_nonneg
    (show 0≤d-x ∧ d-x≤Real.pi/2 by
      constructor <;> linarith [hx'.1,hx'.2,hd.1,hd.2,Real.pi_gt_d2])
  by_cases hx0 : 0≤x
  · have hxtr := cos_sin_nonneg
      (show 0≤x ∧ x≤Real.pi/2 by exact ⟨hx0,by linarith [hx'.2,Real.pi_gt_d2]⟩)
    have hwidth := one_le_abs_cos_add_abs_sin x
    rw [abs_of_nonneg hxtr.1,abs_of_nonneg hxtr.2] at hwidth
    have hp := mul_nonneg (show 0≤Real.cos x+Real.sin x-1 by linarith)
      (sub_nonneg.mpr (Real.cos_le_one (d-x)))
    have hq := mul_nonneg
      (show 0≤1-Real.cos x+Real.sin x by linarith [Real.cos_le_one x]) hytr.2
    have hc : Real.cos d=Real.cos x*Real.cos (d-x)-Real.sin x*Real.sin (d-x) := by
      rw [← Real.cos_add]
      congr 1
      ring
    have hs : Real.sin d=Real.sin x*Real.cos (d-x)+Real.cos x*Real.sin (d-x) := by
      rw [← Real.sin_add]
      congr 1
      ring
    rw [angularWidth,angularWidth,angularWidth,
      abs_of_nonneg hdtr.1,abs_of_nonneg hdtr.2,
      abs_of_nonneg hxtr.1,abs_of_nonneg hxtr.2,
      abs_of_nonneg hytr.1,abs_of_nonneg hytr.2]
    nlinarith only [hp,hq,hc,hs]
  · let v := -x
    have hv : 0≤v ∧ v≤2/5 := by dsimp [v]; constructor <;> linarith
    have hvtr := cos_sin_nonneg
      (show 0≤v ∧ v≤Real.pi/2 by exact ⟨hv.1,by linarith [hv.2,Real.pi_gt_d2]⟩)
    have horder : Real.sin d≤Real.cos d :=
      (east_quadrant_trig (by linarith [hd.1]) hd.2).2.2
    have hsum : Real.cos d+Real.sin d≤3/2 := by
      nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.cos d-Real.sin d)]
    have hp := mul_nonneg (sub_nonneg.mpr horder) hvtr.2
    have hq := mul_nonneg (show 0≤3/2-Real.cos d-Real.sin d by linarith)
      (sub_nonneg.mpr (Real.cos_le_one v))
    have hsq := mul_nonneg (sub_nonneg.mpr hv.2) (show 0≤2/5+v by linarith [hv.1])
    have hcoef : 0≤1-(5/4)*v-v^2/6 := by nlinarith [hv.2]
    have hpoly := mul_nonneg hv.1 hcoef
    have hsv := Real.sin_ge_sub_cube hv.1
    have hcv := Real.one_sub_sq_div_two_le_cos (x := v)
    have hreserve : 0≤Real.sin v-(5/2)*(1-Real.cos v) := by
      nlinarith only [hpoly,hsv,hcv]
    have hreverse : 1+Real.cos d+Real.sin d≤
        Real.cos v+Real.sin v+Real.cos (d+v)+Real.sin (d+v) := by
      rw [Real.cos_add,Real.sin_add]
      nlinarith only [hp,hq,hreserve]
    have he : x=-v := by dsimp [v]; ring
    rw [he,angularWidth,angularWidth,angularWidth,
      Real.cos_neg,Real.sin_neg,abs_neg,
      abs_of_nonneg hdtr.1,abs_of_nonneg hdtr.2,
      abs_of_nonneg hvtr.1,abs_of_nonneg hvtr.2]
    have hcos : 0≤Real.cos (d-(-v)) := by simpa only [he] using hytr.1
    have hsin : 0≤Real.sin (d-(-v)) := by simpa only [he] using hytr.2
    rw [abs_of_nonneg hcos,abs_of_nonneg hsin]
    simpa only [sub_neg_eq_add] using (by linarith [hreverse] :
      1/2+(Real.cos d+Real.sin d)/2≤
        (Real.cos v+Real.sin v)/2+(Real.cos (d+v)+Real.sin (d+v))/2)

/-- The lengths `2 cos (π/4 - d/2)` and `2 cos (d/2)` of the forces on W and S on
the sides of C. -/
def westRadialLength (d : ℝ) : ℝ := 2*Real.cos (Real.pi/4-d/2)
def southRadialLength (d : ℝ) : ℝ := 2*Real.cos (d/2)

lemma west_radial_length {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    Real.sqrt (2+2*Real.sin d)=westRadialLength d := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show Real.pi/4-d/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have h := Real.cos_two_mul (Real.pi/4-d/2)
  rw [show 2*(Real.pi/4-d/2)=Real.pi/2-d by ring,Real.cos_pi_div_two_sub] at h
  have he : 2+2*Real.sin d=(2*Real.cos (Real.pi/4-d/2))^2 := by nlinarith
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma south_radial_length {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    Real.sqrt (2+2*Real.cos d)=southRadialLength d := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have h := Real.cos_two_mul (d/2)
  rw [show 2*(d/2)=d by ring] at h
  have he : 2+2*Real.cos d=(2*Real.cos (d/2))^2 := by nlinarith
  rw [he,Real.sqrt_sq (by positivity)]
  rfl

lemma west_cardinal_secondary_norm (w d : ℝ) :
    (Real.cos w+Real.sin (d-w))^2+(-Real.sin w-Real.cos (d-w))^2=2+2*Real.sin d := by
  have hsum : Real.sin w*Real.cos (d-w)+Real.cos w*Real.sin (d-w)=Real.sin d := by
    rw [← Real.sin_add]
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq w,Real.sin_sq_add_cos_sq (d-w)]

lemma south_cardinal_secondary_norm (s d : ℝ) :
    (Real.cos s+Real.cos (d-s))^2+(-Real.sin s+Real.sin (d-s))^2=2+2*Real.cos d := by
  have hsum : Real.cos s*Real.cos (d-s)-Real.sin s*Real.sin (d-s)=Real.cos d := by
    rw [← Real.cos_add]
    congr 1
    ring
  nlinarith [Real.sin_sq_add_cos_sq s,Real.sin_sq_add_cos_sq (d-s)]

/-- The work of the force on W on the west side of C is at most `1113/1000` times
its length. -/
lemma west_cardinal_secondary_work {a b w d : ℝ}
    (hc : ContainedChart a |b|) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    (Real.cos w+Real.sin (d-w))*a+(-Real.sin w-Real.cos (d-w))*b≤
      (1113/1000)*westRadialLength d := by
  have h := chart_radial_work hc (Real.cos w+Real.sin (d-w),-Real.sin w-Real.cos (d-w))
  dsimp [dot,vectorLength,normSq] at h
  rw [west_cardinal_secondary_norm,west_radial_length hd] at h
  exact h

/-- The work of the force on S on the south side of C is at most `1113/1000`
times its length. -/
lemma south_cardinal_secondary_work {a b s d : ℝ}
    (hc : ContainedChart a |b|) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    (Real.cos s+Real.sin (Real.pi/2+s-d))*a+
      (-Real.sin s+Real.cos (Real.pi/2+s-d))*b≤(1113/1000)*southRadialLength d := by
  have h := chart_radial_work hc (Real.cos s+Real.cos (d-s),-Real.sin s+Real.sin (d-s))
  dsimp [dot,vectorLength,normSq] at h
  rw [south_cardinal_secondary_norm,south_radial_length hd] at h
  have he : Real.pi/2+s-d=Real.pi/2-(d-s) := by ring
  simpa only [he,Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub] using h

lemma eighth_cos_upper : Real.cos (Real.pi/8)≤231/250 := by
  have hhalf := Real.cos_two_mul (Real.pi/8)
  rw [show 2*(Real.pi/8)=Real.pi/4 by ring,Real.cos_pi_div_four] at hhalf
  have hroot : Real.sqrt (2:ℝ)/2≤7072/10000 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0<Real.cos (Real.pi/8)+231/250 by linarith)
  nlinarith

/-- The two lengths sum to `4 cos (π/8) cos (π/8 - d/2) ≤ 4 cos (π/8)`. -/
lemma radial_length_sum_bound (d : ℝ) :
    westRadialLength d+southRadialLength d≤4*(231/250) := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show Real.pi/8∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
  have hproduct := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi/8-d/2)) hcos
  have hsum : Real.cos (Real.pi/4-d/2)+Real.cos (d/2)=
      2*Real.cos (Real.pi/8)*Real.cos (Real.pi/8-d/2) := by
    have hA : Real.cos (Real.pi/4-d/2)=Real.cos (Real.pi/8+(Real.pi/8-d/2)) := by
      congr 1; ring
    have hB : Real.cos (d/2)=Real.cos (Real.pi/8-(Real.pi/8-d/2)) := by congr 1; ring
    rw [hA,hB,Real.cos_add (Real.pi/8),Real.cos_sub (Real.pi/8) (Real.pi/8-d/2)]
    ring
  dsimp [westRadialLength,southRadialLength]
  nlinarith only [hproduct,hsum,eighth_cos_upper]

lemma high_diagonal_width_lower {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    27/20≤Real.cos d+Real.sin d := by
  have hm := cos_add_sin_mono (x := (1:ℝ)/2) (by norm_num) hd.1 hd.2
  linarith [trig_bracket_half.1,trig_bracket_half.2.2.1]

/-- The terms in `d` of the gap with W on its own axis and S on the south side of
C. -/
def southMixedDepth (d : ℝ) : ℝ :=
  (Real.cos d+Real.sin d)/2-(1113/1000)*southRadialLength d-(13/20)*d

/-! With W on the west side of C and S on its own axis the reserve is
`westMixedConstant + (cos d + sin d)/2 - (1113/1000) westRadialLength d` plus the
terms of S. It is at least `westMixedBase d` for `d ≤ 2/3`, and beyond `2/3` it
grows with `westMixedDepth d`. -/

def westMixedConstant : ℝ := 5/2-113/1000-91/125-(13/40)*Real.pi

def westMixedBase (d : ℝ) : ℝ :=
  westMixedConstant+(887/1000)*Real.cos d+(1113/1000)*Real.sin d-
    (1113/1000)*westRadialLength d

def westMixedDepth (d : ℝ) : ℝ :=
  (Real.cos d+Real.sin d)/2-(1113/1000)*westRadialLength d+(13/20)*d

/-- `southMixedDepth d > -19/10` on `[1/2, π/4]`, by Taylor bounds. -/
lemma south_mixed_depth_lower {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    -(19/10)< southMixedDepth d := by
  have hd0 : 0≤d := by linarith [hd.1]
  have hd1 : d≤4/5 := by linarith [hd.2,Real.pi_lt_d2]
  have hc := Real.one_sub_sq_div_two_le_cos (x := d)
  have hs := Real.sin_ge_sub_cube hd0
  have hu := cos_upper_four (x := d/2) (by linarith)
  have hsq := mul_nonneg (sub_nonneg.mpr hd1) (show 0≤4/5+d by linarith)
  have hd2 : d^2≤16/25 := by nlinarith
  have hcube := mul_le_mul hd1 hd2 (sq_nonneg d) (by norm_num : (0:ℝ)≤4/5)
  have hfour := mul_nonneg (sub_nonneg.mpr hd2) (show 0≤16/25+d^2 by positivity)
  have hd3 : d^3≤64/125 := by nlinarith only [hcube]
  have hd4 : d^4≤256/625 := by nlinarith only [hfour]
  have hpoly : -(19/10)< -863/500-(3/20)*d+(113/4000)*d^2-d^3/12-(371/64000)*d^4 := by
    nlinarith [sq_nonneg d]
  dsimp [southMixedDepth,southRadialLength]
  nlinarith only [hc,hs,hu,hpoly]

/-- `westMixedBase` is positive on `[1/2, 2/3]`: with the length
`√(2 + 2 sin d)` below its tangent at `49/16` it is a first harmonic with
nonnegative coefficients, positive at both ends. -/
lemma west_mixed_base_positive {d : ℝ} (hd : 1/2≤d ∧ d≤2/3) : 0<westMixedBase d := by
  have hL : westRadialLength d≤(2+2*Real.sin d+(7/4)^2)/(2*(7/4)) := by
    rw [← west_radial_length ⟨hd.1,by linarith [hd.2,Real.pi_gt_three]⟩]
    exact sqrt_le_tangent (by norm_num) (by linarith [Real.neg_one_le_sin d])
  obtain ⟨hc5,-,hs5,-⟩ := trig_bracket_half
  obtain ⟨hc6,-,hs6,-⟩ := trig_bracket_two_thirds
  have h := harmonic_pos_of_endpoints (K := westMixedConstant-(1113/1000)*(81/56))
    (A := 887/1000) (B := (1113/1000)*(3/7)) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [Real.pi_gt_three]) hd
    (by dsimp [westMixedConstant]; linarith [Real.pi_lt_d4])
    (by dsimp [westMixedConstant]; linarith [Real.pi_lt_d4])
  dsimp [westMixedBase]
  ring_nf at h hL ⊢
  linarith

lemma west_mixed_depth_monotone :
    MonotoneOn westMixedDepth (Set.Icc (2/3) (Real.pi/4)) := by
  let f' : ℝ→ℝ := fun d => (Real.cos d-Real.sin d)/2-
    (1113/1000)*Real.sin (Real.pi/4-d/2)+13/20
  have hu (d : ℝ) : HasDerivAt (fun x : ℝ => Real.pi/4-x/2) (-1/2) d :=
    (((hasDerivAt_id' d).div_const 2).const_sub (Real.pi/4)).congr_deriv (by norm_num)
  have hD (d : ℝ) : HasDerivAt westMixedDepth (f' d) d := by
    convert ((((Real.hasDerivAt_cos d).fun_add (Real.hasDerivAt_sin d)).div_const 2).fun_sub
      (((Real.hasDerivAt_cos (Real.pi/4-d/2)).comp d (hu d)).const_mul (1113/500))).fun_add
      ((hasDerivAt_id d).const_mul (13/20)) using 1
    · funext y; dsimp [westMixedDepth,westRadialLength]; ring
    · dsimp [f']; ring
  apply monoOn_of_hasDeriv_nonneg (d := f')
    (fun x _ => (hD x).continuousAt.continuousWithinAt)
  · intro d _
    exact hD d
  · intro d hd
    have hc := (east_quadrant_trig (by linarith [hd.1]) hd.2.le).2.2
    have hu0 : 0≤Real.pi/4-d/2 := by linarith [hd.2,Real.pi_pos]
    have hs := Real.sin_le hu0
    have hu1 : Real.pi/4-d/2≤1/2 := by linarith [hd.1,Real.pi_lt_d2]
    dsimp [f']
    linarith

/-- The reserve for W separated from C along the west side of C and S along its
own axis, for every angle `s` of S in `[-5/8, 2/3]`. -/
theorem west_cardinal_own_south_reserve {s d : ℝ}
    (hs : -5/8≤ s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    0<westMixedConstant+(Real.cos d+Real.sin d)/2-
      (1113/1000)*westRadialLength d+ownWingPotential s+(13/20)*|s-d| := by
  by_cases hsmall : d≤2/3
  · have hwing := own_wing_penalty_lower hs ⟨by linarith [hd.1],hd.2⟩
    have hp := west_mixed_base_positive ⟨hd.1,hsmall⟩
    dsimp [westMixedBase,positiveWing] at hp hwing
    linarith
  · have hwing := own_wing_penalty_endpoint hs (le_of_not_ge hsmall)
    have hdepth := west_mixed_depth_monotone
      (show (2:ℝ)/3∈Set.Icc (2/3) (Real.pi/4) by
        constructor <;> linarith [Real.pi_gt_d2])
      ⟨le_of_not_ge hsmall,hd.2⟩ (le_of_not_ge hsmall)
    have hp := west_mixed_base_positive (d := 2/3) ⟨by norm_num,le_rfl⟩
    dsimp [westMixedBase,positiveWing,westMixedDepth] at hp hwing hdepth
    linarith

end SquaresInCircles.Six
