module

public import SquaresInCircles.Seven.Pair.LabelSegments
public import SquaresInCircles.Seven.Pair.Contacts

/-!
# Seven squares: the forward axis, negative target sign

A positive source with any active label, and a negative source with an axial
label. For an axial target at small turns the support of the target is least at
the transition state, where the tie line meets the circle, and at large turns
Cauchy–Schwarz on the disk bounds it. For a side target at small turns the disk
alone suffices, by completing the square about the side state; at larger turns
the target exceeds its value at the transition state, where the force along the
tangent of the disk is nonnegative. The sum vanishes only at an axial source and
a side target.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Seven
open Boundary

/-- A lower bound of the forward support sum when the second sign is negative,
in the turn `e` and the signed first label `r`. -/
def rawTarget (A v e r : ℝ) : ℝ :=
  1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2

lemma forward_negative_target_lower {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u) :
    rawTarget A v (sgn.coe*label a u+label A v-Real.pi/6)
      (sgn.coe*label a u) ≤ pairSupport a u A v sgn .negative 1 gap := by
  let e := sgn.coe*label a u+label A v-Real.pi/6
  have hc : 0 ≤ Real.cos e := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    apply Real.cos_nonneg_of_mem_Icc
    cases sgn <;> dsimp [e,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  have hsource' : (4/5)*(sgn.coe*label a u) ≤ sgn.coe*u := by
    rcases hsource with rfl | he
    · have hh := h.label_le_axial
      dsimp [TransverseSign.coe,axial] at *
      linarith
    · rw [he]
      dsimp [axial]
      cases sgn <;> norm_num [TransverseSign.coe]
  have hangle : 3*Real.pi/2-gap-sgn.coe*label a u-label A v=Real.pi-e := by
    dsimp [e,gap]
    ring
  rw [pairSupport_one,show TransverseSign.negative.coe = -1 from rfl]
  simp only [neg_one_mul,← sub_eq_add_neg]
  rw [hangle]
  simp only [support,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg,abs_of_nonneg hc]
  change rawTarget A v e (sgn.coe*label a u) ≤ _
  dsimp [rawTarget]
  linarith

/-- On `[0, π/6]`, `0 ≤ sin z ≤ 1/2` and `cos z > 5/6`. -/
private lemma small_turn_bounds {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    0 ≤ Real.sin z ∧ Real.sin z ≤ 1/2 ∧ 5/6 < Real.cos z := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) hz.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos]) hz.2
  rw [Real.sin_pi_div_six] at hs
  rw [Real.cos_pi_div_six] at hc
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos]),hs,
    by linarith [sqrt_three_bounds.1]⟩

/-- Below `π/6` the force `(cos z, 1 - sin z)` is a combination with nonnegative
coefficients of the normal `(9, 11)` of the tie line and the normal `(X0, Y0)` of the
circle at the transition state, so on the axial states the form is largest there. The
margin left is convex in `z`, so it lies above its tangent at `0`. -/
private lemma axial_small_turn {A v z : ℝ} (h : Admissible A v) (hA : label A v=axial v)
    (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-(A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  obtain ⟨hs0,hs1,hc⟩ := small_turn_bounds hz
  have ht := transition_bounds
  have hcirc := transition_circle
  have hline := transition_line
  have htie := axial_tie_line h hA
  have hp := h.phi_le
  dsimp [a0,u0] at ht hline
  dsimp [phi,targetSq] at hp hcirc
  -- the form is largest at the transition state
  have hP := mul_nonneg (show 0 ≤ 11*Real.cos z-9*(1-Real.sin z) by linarith)
    (show 0 ≤ X0^2+Y0^2-X0*(A+1/2)-Y0*(v+1/2) by
      linarith [sq_nonneg (A+1/2-X0),sq_nonneg (v+1/2-Y0)])
  have hQ := mul_nonneg (show 0 ≤ X0*(1-Real.sin z)-Y0*Real.cos z by
      linarith [mul_le_mul_of_nonneg_left hs1 (show 0 ≤ X0 by linarith),
        mul_le_mul_of_nonneg_left (Real.cos_le_one z) (show 0 ≤ Y0 by linarith)])
    (show 0 ≤ 9*X0+11*Y0-9*(A+1/2)-11*(v+1/2) by linarith)
  have hmax := nonneg_of_mul_nonneg_right (show 0 ≤ (11*X0-9*Y0)*
      ((X0-(A+1/2))*Real.cos z+(Y0-(v+1/2))*(1-Real.sin z)) by linear_combination hP+hQ)
    (by linarith)
  -- the margin at the transition state lies above its tangent at `0`
  have hM := curvature_tangent (l := 0) (u := Real.pi/6) (t := 0) (κ := 0)
    (f := fun y => -(X0-1)*Real.cos y+Y0*Real.sin y-(4/5)*y)
    (d := fun y => (X0-1)*Real.sin y+Y0*Real.cos y-4/5)
    (dd := fun y => (X0-1)*Real.cos y-Y0*Real.sin y)
    hz ⟨le_rfl,by linarith [Real.pi_pos]⟩
    (fun y _ => ((((Real.hasDerivAt_cos y).const_mul (-(X0-1))).add
      ((Real.hasDerivAt_sin y).const_mul Y0)).sub
      ((hasDerivAt_id' y).const_mul (4/5))).congr_deriv (by ring))
    (fun y _ => ((((Real.hasDerivAt_sin y).const_mul (X0-1)).add
      ((Real.hasDerivAt_cos y).const_mul Y0)).sub_const (4/5)).congr_deriv (by ring))
    (fun y hy => by
      obtain ⟨-,hy1,hy2⟩ := small_turn_bounds hy
      linarith [mul_le_mul_of_nonneg_left hy2.le (show 0 ≤ X0-1 by linarith),
        mul_le_mul_of_nonneg_left hy1 (show 0 ≤ Y0 by linarith)])
  simp only [Real.cos_zero,Real.sin_zero] at hM
  have hz53 := mul_le_mul_of_nonneg_left (show z ≤ 0.53 by linarith [Real.pi_lt_d2])
    (show 0 ≤ 4/5-Y0 by linarith)
  linarith [Real.pi_gt_d4]

/-- Above `π/6` the force `(cos z, 1 - sin z)` has length `√2 (cos(z/2) - sin(z/2))`; the
bound it gives is concave in `z` and positive at `π/6` and `π/2`. -/
private lemma axial_large_turn {A v z : ℝ} (h : Admissible A v)
    (hz : Real.pi/6 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-(A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  have hhalf (y : ℝ) (hy : 0 ≤ y ∧ y ≤ Real.pi/2) :
      0 ≤ Real.cos (y/2)-Real.sin (y/2) ∧ 1 ≤ Real.cos (y/2)+Real.sin (y/2) := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := y/2) (by linarith)
      (by linarith [Real.pi_pos])
    have hc := Real.cos_nonneg_of_mem_Icc (x := y/2) ⟨by linarith [Real.pi_pos],by linarith⟩
    have hsc := sin_le_cos_of_small (x := y/2) ⟨by linarith,by linarith⟩
    refine ⟨by linarith,?_⟩
    nlinarith [Real.sin_sq_add_cos_sq (y/2),Real.sin_le_one (y/2),Real.cos_le_one (y/2)]
  have hnorm (y : ℝ) : Real.cos y^2+(1-Real.sin y)^2=2*(Real.cos (y/2)-Real.sin (y/2))^2 := by
    have hs : Real.sin y=2*Real.sin (y/2)*Real.cos (y/2) := by rw [← Real.sin_two_mul]; ring_nf
    linarith [Real.sin_sq_add_cos_sq y,Real.sin_sq_add_cos_sq (y/2)]
  have hh := hhalf z ⟨by linarith [Real.pi_pos],hz.2⟩
  have hcs := dot_ge (p := -Real.cos z) (r := -(1-Real.sin z))
    (c := (51/20)*(Real.cos (z/2)-Real.sin (z/2))) h.phi_le (by linarith)
    (by simp only [targetSq,neg_sq]; linarith [hnorm z,sq_nonneg (Real.cos (z/2)-Real.sin (z/2))])
  have hG := positive_of_second_nonpos (l := Real.pi/6) (u := Real.pi/2)
    (f := fun y => 1+2*Real.pi/15-(4/5)*y+Real.cos y-(51/20)*(Real.cos (y/2)-Real.sin (y/2)))
    (d := fun y => -4/5-Real.sin y+(51/40)*(Real.sin (y/2)+Real.cos (y/2)))
    (dd := fun y => -Real.cos y+(51/80)*(Real.cos (y/2)-Real.sin (y/2)))
    hz
    (fun y _ => by
      have hy := (hasDerivAt_id' y).div_const 2
      exact ((((hasDerivAt_const y (1+2*Real.pi/15)).sub
        ((hasDerivAt_id' y).const_mul (4/5))).add (Real.hasDerivAt_cos y)).sub
        ((hy.cos.sub hy.sin).const_mul (51/20))).congr_deriv (by ring))
    (fun y _ => by
      have hy := (hasDerivAt_id' y).div_const 2
      exact (((hasDerivAt_const y (-4/5)).sub (Real.hasDerivAt_sin y)).add
        ((hy.sin.add hy.cos).const_mul (51/40))).congr_deriv (by ring))
    (fun y hy => by
      have hh := hhalf y ⟨by linarith [hy.1,Real.pi_pos],hy.2⟩
      have hc : Real.cos y=2*Real.cos (y/2)^2-1 := by rw [← Real.cos_two_mul]; ring_nf
      linarith [mul_nonneg hh.1 (show 0 ≤ Real.cos (y/2)+Real.sin (y/2)-51/80 by linarith),
        Real.sin_sq_add_cos_sq (y/2)])
    (by
      have hn := hnorm (Real.pi/6)
      have hh := (hhalf (Real.pi/6) ⟨by positivity,by linarith [Real.pi_pos]⟩).1
      rw [Real.cos_pi_div_six,Real.sin_pi_div_six] at hn
      have h7 : Real.cos (Real.pi/6/2)-Real.sin (Real.pi/6/2) < 5/7 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
      rw [Real.cos_pi_div_six]
      linarith [sqrt_three_bounds.1])
    (by
      rw [show Real.pi/2/2=Real.pi/4 by ring,Real.cos_pi_div_two,Real.cos_pi_div_four,
        Real.sin_pi_div_four]
      linarith [pi_lt_22_over_7])
  linarith

/-- An axial target at a turn `-z` with `0 ≤ z ≤ π/2`. Below `π/6` the form is
largest at the transition state, where the tie line `9A + 11v ≤ 2π + 7` of the axial
label meets the circle. -/
lemma axial_target_support {A v z : ℝ} (h : Admissible A v) (hA : label A v=axial v)
    (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-(A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  rcases le_total z (Real.pi/6) with hs | hs
  · exact axial_small_turn h hA ⟨hz.1,hs⟩
  · exact axial_large_turn h ⟨hs,hz.2⟩

lemma side_transition_trade {A v : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) :
    (12/25)*(v-u0) ≤ a0-A := by
  have hb := side_state_transition_bounds h hT
  have he := transition_circle
  have hc := transition_bounds
  have hp := h.phi_le
  have ht : X0*(A-a0)+Y0*(v-u0) ≤ 0 := by
    dsimp [phi,a0,u0] at hp ⊢
    linarith [sq_nonneg (A+1/2-X0),sq_nonneg (v+1/2-Y0)]
  have hratio : (12/25)*X0 < Y0 := by
    dsimp [a0,u0] at hc
    linarith
  have hm := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hratio.le)
  have hXpos : 0 < X0 := by dsimp [a0] at hc; linarith
  by_contra hn
  have hbad := mul_pos
    (show 0 < (12/25)*(v-u0)-(a0-A) by linarith) hXpos
  linarith

def sideTarget (A v e : ℝ) : ℝ :=
  (4/5)*e+(2/15)*remainder A v+(A-1/2)*(1-Real.cos e)
    -v*Real.sin e+|Real.sin e|/2

lemma sideTarget_positive_angle {A v e : ℝ} (h : Admissible A v)
    (he : 0 ≤ e ∧ e ≤ Real.pi/3) :
    (21/40)*e+(2/15)*remainder A v ≤ sideTarget A v e := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Real.pi_pos])
  have hs1 := Real.sin_le he.1
  have hc := mul_nonneg (show 0 ≤ A-1/2 by linarith [h.half_le])
    (sub_nonneg.mpr (Real.cos_le_one e))
  have hv := mul_nonneg (show 0 ≤ 31/40-v by linarith [h.u_lt]) hs0
  have hrem := mul_nonneg (show (0:ℝ) ≤ 11/40 by norm_num) (sub_nonneg.mpr hs1)
  dsimp [sideTarget]
  rw [abs_of_nonneg hs0]
  linarith

/-- The force along the tangent of the disk at the transition state increases on `[0, 1]`
and is positive at `1/10`. -/
private lemma tangent_force_pos {z : ℝ} (hz : 1/10 ≤ z ∧ z ≤ 1) :
    0 < (12/25)*(Real.cos z-3/5)+Real.sin z-4/15 := by
  have hm := monoOn_of_hasDeriv_nonneg (l := 0) (u := 1)
    (f := fun y => (12/25)*(Real.cos y-3/5)+Real.sin y-4/15)
    (d := fun y => Real.cos y-(12/25)*Real.sin y) (by fun_prop)
    (fun y _ => (((((Real.hasDerivAt_cos y).sub_const (3/5)).const_mul (12/25)).add
      (Real.hasDerivAt_sin y)).sub_const (4/15)).congr_deriv (by ring))
    (fun y hy => by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := y),Real.sin_le_one y,hy.1,hy.2])
  have hK := hm (show (1/10:ℝ) ∈ Set.Icc 0 1 by norm_num) ⟨by linarith,hz.2⟩ hz.1
  have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 1/10 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/10:ℝ))
  linarith

/-- A side target at a turn `-z` with `0 < z < 1`. Below `1/10` the disk alone suffices,
by completing the square about the side state. Above, where the force along the tangent
at the transition state is positive, the target exceeds its value there. -/
lemma sideTarget_negative_pos {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1) :
    0 < sideTarget A v (-z) := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,Real.pi_gt_d2])
  have hexp (a u : ℝ) : sideTarget a u (-z) =
      Real.cos z-2/15-(4/5)*z+(3/5-Real.cos z)*(a+1/2)+(Real.sin z-4/15)*(u+1/2) := by
    dsimp [sideTarget,remainder]
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs0]
    ring
  rw [hexp]
  by_cases hz10 : z < 1/10
  · -- the disk alone: complete the square about the side state
    have hid : Real.cos z-2/15-(4/5)*z+(3/5-Real.cos z)*(A+1/2)+(Real.sin z-4/15)*(v+1/2) =
        Real.sin z-(4/5)*z-(13/4)*(1-Real.cos z)+(2/15)*(targetSq-phi A v)+
        (2/15)*((A-1+(15/4)*(1-Real.cos z))^2+(v-1/2+(15/4)*Real.sin z)^2) := by
      dsimp [phi,targetSq]
      linear_combination (-15/8)*Real.sin_sq_add_cos_sq z
    rw [hid]
    linarith [h.phi_le,sq_nonneg (A-1+(15/4)*(1-Real.cos z)),
      sq_nonneg (v-1/2+(15/4)*Real.sin z),Real.sin_ge_sub_cube hz.1.le,
      Real.one_sub_sq_div_two_le_cos (x := z),mul_pos hz.1 (show 0 < 1/5-2*z by linarith),
      mul_nonneg (sq_nonneg z) (show 0 ≤ 3/8-z/6 by linarith)]
  have hb := side_state_transition_bounds h hT
  have hc := transition_coarse
  by_cases hcos : 3/5 ≤ Real.cos z
  · -- at least the value at the transition state, positive as `z ≥ 1/10`
    have hK := tangent_force_pos ⟨le_of_not_gt hz10,hz.2.le⟩
    have ht := side_transition_trade h hT
    have h1 := mul_nonneg (sub_nonneg.mpr hcos) (show 0 ≤ a0-A-(12/25)*(v-u0) by linarith)
    have h2 := mul_nonneg hK.le (sub_nonneg.mpr hb.1)
    have hpA := mul_nonneg (show 0 ≤ a0-1/2-3/5 by linarith)
      (sub_nonneg.mpr (Real.cos_le_one z))
    have hpU := mul_nonneg (show 0 ≤ u0+1/2-(4/5-1/100) by linarith) hs0
    have hz3 : z^3 ≤ z^2 := by nlinarith [mul_nonneg (sq_nonneg z) (show 0 ≤ 1-z by linarith)]
    have hz4 : z^4 ≤ z^2 := by
      nlinarith [mul_nonneg (sq_nonneg z) (show 0 ≤ 1-z^2 by nlinarith)]
    have hpos := mul_pos hz.1 (show 0 < z/8-1/100 by linarith)
    have hW : 0 ≤ 4-3*a0-2*u0 := transition_admissible.remainder_nonneg
    linarith [Real.sin_ge_sub_cube hz.1.le,Real.sin_le hz.1.le,cos_upper_four hz.1.le]
  · -- both coefficients are positive
    have hc0 : (1:ℝ)/2 < Real.cos z := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := z)]
    have hsin : 4/5 < Real.sin z := by
      nlinarith [Real.sin_sq_add_cos_sq z]
    have h1 := mul_nonneg (show 0 ≤ 3/5-Real.cos z by linarith)
      (show 0 ≤ A-1/2 by linarith [h.half_le])
    have h2 := mul_nonneg (show 0 ≤ v-29/100 by linarith [hb.1,hc.2.2.1])
      (show 0 ≤ Real.sin z-4/15 by linarith)
    linarith

lemma negative_target_axial_pos {A v e r : ℝ}
    (h : Admissible A v) (hA : label A v=axial v)
    (he : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3)
    (hr : e=r+label A v-Real.pi/6) : 0 < rawTarget A v e r := by
  have hv : v ≤ Real.pi/5 := by
    have hh := h.label_le_quarter
    rw [hA] at hh
    dsimp [axial] at hh
    linarith
  have hidentity : rawTarget A v e r =
      1/2+2*Real.pi/15+(4/5)*e-(A-1/2)*Real.cos e-
      v*(1+Real.sin e)+|Real.sin e|/2 := by
    rw [hA] at hr
    dsimp [rawTarget,axial] at *
    linarith
  rw [hidentity]
  by_cases he0 : 0 ≤ e
  · have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he0
      (by linarith [he.2,Real.pi_pos])
    have hsin := Real.sin_le he0
    have hc := mul_nonneg (show 0 ≤ A-1/2 by linarith [h.half_le])
      (sub_nonneg.mpr (Real.cos_le_one e))
    have hp := mul_nonneg (show 0 ≤ 13/20-v by linarith [pi_lt_22_over_7]) hs0
    have hm := mul_nonneg (show (0:ℝ) ≤ 3/20 by norm_num) (sub_nonneg.mpr hsin)
    rw [abs_of_nonneg hs0]
    have hsum := axial_sum_lt h hA
    linarith
  · have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ -e by linarith)
      (by linarith [he.1,Real.pi_pos])
    have hp := axial_target_support h hA ⟨show 0 ≤ -e by linarith,by linarith [he.1]⟩
    simp only [Real.cos_neg,Real.sin_neg] at hp hs0
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The forward axis with target sign `-1`: zero only at an axial source and a
side target. -/
theorem fixed_gap_forward_negative_target {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u)
    (htarget : ActiveLabel A v) : PairProperty a u A v sgn .negative 1 := by
  let r := sgn.coe*label a u
  let e := r+label A v-Real.pi/6
  have hlow := forward_negative_target_lower sgn h h' hsource
  change rawTarget A v e r ≤ _ at hlow
  have h0 := h.label_nonneg
  have h1 := h.label_le_quarter
  have he : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3 := by
    have h2 := h'.label_nonneg
    have h3 := h'.label_le_quarter
    cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  rcases htarget with hA | hT
  · exact .of_pos ((negative_target_axial_pos h' hA he rfl).trans_le hlow)
  have hid : rawTarget A v e r=sideTarget A v e := by
    have hr : e=r+label A v-Real.pi/6 := rfl
    rw [hT,side_identity_radial] at hr
    dsimp [rawTarget,sideTarget]
    linear_combination (-4/5)*hr
  rw [hid] at hlow
  by_cases he0 : 0 ≤ e
  · have hp := sideTarget_positive_angle h' ⟨he0,he.2⟩
    have hW := h'.remainder_nonneg
    refine ⟨by linarith,fun hz => ?_⟩
    have hc := remainder_zero h' (by linarith)
    have ht : label a u=0 := by
      have he' : e=0 := by linarith
      dsimp [e,r] at he'
      rw [hc.1,hc.2,side_label] at he'
      cases sgn <;> dsimp [TransverseSign.coe] at he' <;> linarith
    exact Or.inr (Or.inr ⟨rfl,axial_of_transverse_zero h (h.label_zero_iff.mp ht),hc⟩)
  · have hs := side_selected_label_gt h' hT
    have hp := sideTarget_negative_pos h' hT (z := -e) ⟨by linarith,by
      cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> linarith [pi_lt_22_over_7]⟩
    rw [neg_neg] at hp
    exact .of_pos (hp.trans_le hlow)

end SquaresInCircles.Seven
