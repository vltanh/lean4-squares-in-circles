module
public import SquaresInCircles.Six.Analytic.CapChart
public import SquaresInCircles.Six.Analytic.SouthMarker

@[expose] public section

/-!
# Exact formulas for the east, north and south primary quadrants

Only the three geometrically distinguished primary quadrants are used; the
west quadrant is handled by the universal pi/4 marker displacement. These
identities retain all signs of b and of the local angle.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma octant_trig {t : ℝ} (ht : |t| ≤ Real.pi/4) :
    (7/10 ≤ Real.cos t ∧ Real.cos t ≤ 1) ∧
    |Real.sin t| ≤ Real.cos t ∧ 1 ≤ Real.cos t+|Real.sin t| := by
  have hc := octant_cos_lower (abs_nonneg t) ht
  rw [Real.cos_abs] at hc
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ |t| by linarith [abs_nonneg t,Real.pi_pos])
    (show Real.pi/4 ≤ Real.pi/2 by linarith [Real.pi_pos]) ht
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg t)
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) ht
  rw [sin_abs_angle (by linarith [Real.pi_pos]),Real.sin_pi_div_four] at hs
  rw [Real.cos_pi_div_four,Real.cos_abs] at hcos
  have hwidth := one_le_abs_cos_add_abs_sin t
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith)] at hwidth
  exact ⟨⟨hc,Real.cos_le_one t⟩,hs.trans hcos,hwidth⟩

lemma signed_sine_product {x k t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ k) :
    x*Real.sin t ≤ k*|Real.sin t| ∧ -(x*Real.sin t) ≤ k*|Real.sin t| := by
  have hp := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin t)) hx0
  have hn := mul_le_mul_of_nonneg_left (neg_le_abs (Real.sin t)) hx0
  have hk := mul_le_mul_of_nonneg_right hx1 (abs_nonneg (Real.sin t))
  constructor <;> nlinarith only [hp,hn,hk]

@[simp] lemma width_north (t : ℝ) : angularWidth (Real.pi/2+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg,add_comm]

@[simp] lemma width_south (t : ℝ) : angularWidth (-Real.pi/2+t)=angularWidth t := by
  rw [show -Real.pi/2+t=t-Real.pi/2 by ring]
  simp [angularWidth,Real.cos_sub,Real.sin_sub,abs_neg,add_comm]

lemma north_own (t a b x y : ℝ) :
    centralMargin .own (Real.pi/2+t) a b x y =
      a-1/2+x*Real.sin t-y*Real.cos t-angularWidth t := by
  simp [centralMargin,centralNormal,Real.cos_add,Real.sin_add]
  ring
lemma north_secPlus (t a b x y : ℝ) :
    centralMargin .secPlus (Real.pi/2+t) a b x y =
      b-1/2+x*Real.cos t+y*Real.sin t-angularWidth t := by
  simp [centralMargin,centralTransverse,Real.cos_add,Real.sin_add]
  ring
lemma north_secMinus (t a b x y : ℝ) :
    centralMargin .secMinus (Real.pi/2+t) a b x y =
      -x*Real.cos t-y*Real.sin t-1/2-angularWidth t-b := by
  simp [centralMargin,centralTransverse,Real.cos_add,Real.sin_add]
  ring
lemma north_north (t a b x y : ℝ) :
    centralMargin .north (Real.pi/2+t) a b x y =
      a*Real.cos t-b*Real.sin t-angularWidth t-y-1/2 := by
  simp [centralMargin,centerY,Real.cos_add,Real.sin_add]
  ring
lemma north_south (t a b x y : ℝ) :
    centralMargin .south (Real.pi/2+t) a b x y =
      y-1/2-a*Real.cos t+b*Real.sin t-angularWidth t := by
  simp [centralMargin,centerY,Real.cos_add,Real.sin_add]
  ring

lemma south_own (t a b x y : ℝ) :
    centralMargin .own (-Real.pi/2+t) a b x y =
      a-1/2-x*Real.sin t+y*Real.cos t-angularWidth t := by
  rw [show -Real.pi/2+t=t-Real.pi/2 by ring]
  simp [centralMargin,centralNormal,angularWidth,Real.cos_sub,Real.sin_sub,abs_neg]
  ring
lemma south_secPlus (t a b x y : ℝ) :
    centralMargin .secPlus (-Real.pi/2+t) a b x y =
      b-1/2-x*Real.cos t-y*Real.sin t-angularWidth t := by
  rw [show -Real.pi/2+t=t-Real.pi/2 by ring]
  simp [centralMargin,centralTransverse,angularWidth,Real.cos_sub,Real.sin_sub,abs_neg]
  ring
lemma south_secMinus (t a b x y : ℝ) :
    centralMargin .secMinus (-Real.pi/2+t) a b x y =
      x*Real.cos t+y*Real.sin t-1/2-angularWidth t-b := by
  rw [show -Real.pi/2+t=t-Real.pi/2 by ring]
  simp [centralMargin,centralTransverse,angularWidth,Real.cos_sub,Real.sin_sub,abs_neg]
  ring
lemma south_north (t a b x y : ℝ) :
    centralMargin .north (-Real.pi/2+t) a b x y =
      -a*Real.cos t+b*Real.sin t-angularWidth t-y-1/2 := by
  rw [show -Real.pi/2+t=t-Real.pi/2 by ring]
  simp [centralMargin,centerY,angularWidth,Real.cos_sub,Real.sin_sub,abs_neg]
  ring
lemma south_south (t a b x y : ℝ) :
    centralMargin .south (-Real.pi/2+t) a b x y =
      y-1/2+a*Real.cos t-b*Real.sin t-angularWidth t := by
  rw [show -Real.pi/2+t=t-Real.pi/2 by ring]
  simp [centralMargin,centerY,angularWidth,Real.cos_sub,Real.sin_sub,abs_neg]
  ring

lemma primary_projection_nonneg {a b t : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) : 0 ≤ a*Real.cos t-b*Real.sin t := by
  have hc := octant_trig ht
  have hcos : 0 ≤ Real.cos t := by linarith [hc.1.1]
  have hp : b*Real.sin t ≤ |b|*|Real.sin t| := by
    simpa only [abs_mul] using le_abs_self (b*Real.sin t)
  have hprod := mul_le_mul h.u_le hc.2.1 (abs_nonneg _) (by linarith [h.half_le] : 0 ≤ a)
  nlinarith only [hp,hprod]

end SquaresInCircles.Six.Analytic
