import SquaresInCircles.Six.Analytic.PinCircle

/-!
# A whole-sector two-pin covering theorem

For two radius-9/10 pins separated by pi/3, the primary direction between them
is covered by one pin. The key far-corner obstruction is the uniform bound
F >= 29/10 > Q0. Its displayed identity is a sum of a square and nonnegative
terms on the first-quadrant unit circle. This replaces the separate numerical
normal-coordinate checks in the W/D two-pin argument.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma sixty_pin_corner {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : c^2+s^2=1) :
    (29:ℝ)/10 ≤ (1+(9/10)*c)^2+
      (1-(9/10)*((Real.sqrt 3/2)*c-(1/2)*s))^2 := by
  have hr0 := Real.sqrt_nonneg (3:ℝ)
  have hr := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hr1 : Real.sqrt 3 ≤ 7/4 := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
  have hsum : 1 ≤ c+s := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h) (show 0 < 1+c+s by linarith)
    nlinarith [mul_nonneg hc hs]
  have hsq := sq_nonneg ((4/5)*c-(9/20)*s)
  have hA := mul_nonneg (show 0 ≤ 63/40-(9/10)*Real.sqrt 3 by linarith) hc
  have hB := mul_nonneg
    (show 0 ≤ 18/25-(81/200)*Real.sqrt 3 by linarith) (mul_nonneg hc hs)
  have hC := mul_nonneg (show (0:ℝ) ≤ 9/40 by norm_num) (sub_nonneg.mpr hsum)
  have hD := div_nonneg
    (mul_nonneg (show 0 ≤ 1-s by linarith) (show 0 ≤ 41+311*s by linarith))
    (show (0:ℝ) ≤ 400 by norm_num)
  have hid :
      (1+(9/10)*c)^2+(1-(9/10)*((Real.sqrt 3/2)*c-(1/2)*s))^2-29/10 =
      ((4/5)*c-(9/20)*s)^2+
        (63/40-(9/10)*Real.sqrt 3)*c+
        (18/25-(81/200)*Real.sqrt 3)*c*s+
        (9/40)*(c+s-1)+(1-s)*(41+311*s)/400 := by
    linear_combination (81/400)*c^2*hr+(311/400)*hu
  nlinarith only [hid,hsq,hA,hB,hC,hD]

lemma sixty_sine_complement {z v : ℝ} (h : z+v=Real.pi/3) :
    Real.sin z=(Real.sqrt 3/2)*Real.cos v-(1/2)*Real.sin v := by
  rw [show z=Real.pi/3-v by linarith,Real.sin_sub,
    Real.sin_pi_div_three,Real.cos_pi_div_three]

lemma sixty_sine_sum {z v : ℝ} (h : z+v=Real.pi/3) :
    Real.sin z+Real.sin v ≤ 1 := by
  have hid : Real.sin z+Real.sin v=Real.cos (v-Real.pi/6) := by
    rw [sixty_sine_complement h,Real.cos_sub,Real.cos_pi_div_six,Real.sin_pi_div_six]
    ring
  rw [hid]
  exact Real.cos_le_one _

lemma pin_normal_from_other_transverse {a b z v : ℝ} (h : ContainedChart a |b|)
    (hv : 0 ≤ v ∧ v ≤ Real.pi/2) (hangle : z+v=Real.pi/3)
    (hb : 1/2-(9/10)*Real.sin z ≤ b) :
    |(9/10)*Real.cos v-a| < 1/2 := by
  have hc : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hv.1,Real.pi_pos],hv.2⟩
  have hs : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_pos])
  have hf := sixty_pin_corner hc hs (by nlinarith [Real.sin_sq_add_cos_sq v])
  rw [← sixty_sine_complement hangle] at hf
  have hQ : Q0 < (29:ℝ)/10 := by norm_num [Q0]
  have hV0 : 0 ≤ 1-(9/10)*Real.sin z := by linarith [Real.sin_le_one z]
  have hB : 1-(9/10)*Real.sin z ≤ |b|+1/2 := by linarith [le_abs_self b]
  have hBs := mul_nonneg (sub_nonneg.mpr hB)
    (show 0 ≤ |b|+1/2+(1-(9/10)*Real.sin z) by linarith [abs_nonneg b])
  apply abs_lt.mpr
  constructor
  · by_contra! hn
    have hA : 1+(9/10)*Real.cos v ≤ a+1/2 := by linarith
    have hAs := mul_nonneg (sub_nonneg.mpr hA)
      (show 0 ≤ a+1/2+(1+(9/10)*Real.cos v) by linarith [h.half_le])
    nlinarith [h.containment]
  · linarith [Real.cos_le_one v,h.half_le]

private lemma two_pin_left_near {a b z v : ℝ} (h : ContainedChart a |b|)
    (hb : |b| < 1/2) (hz : 0 ≤ z) (hv : 0 ≤ v)
    (hangle : z+v=Real.pi/3) (hnear : z ≤ v) :
    localPin a b (-z) ∨ localPin a b v := by
  have hz1 : z ≤ Real.pi/6 := by linarith
  have hv1 : v ≤ Real.pi/2 := by linarith [Real.pi_pos]
  have hsz := Real.sin_nonneg_of_nonneg_of_le_pi hz (by linarith [Real.pi_pos])
  have hsv := Real.sin_nonneg_of_nonneg_of_le_pi hv (by linarith [Real.pi_pos])
  have hbb := abs_lt.mp hb
  by_cases hleft : b < 1/2-(9/10)*Real.sin z
  · left
    refine ⟨?_,?_⟩
    · apply pin_normal h
      rw [abs_neg,abs_of_nonneg hz]
      linarith [Real.pi_lt_d2]
    · rw [Real.sin_neg]
      apply abs_lt.mpr
      constructor <;> linarith
  · right
    have hbhi : 1/2-(9/10)*Real.sin z ≤ b := le_of_not_gt hleft
    refine ⟨pin_normal_from_other_transverse h ⟨hv,hv1⟩ hangle hbhi,?_⟩
    have hsum := sixty_sine_sum hangle
    apply abs_lt.mpr
    constructor <;> linarith

/-- Any primary direction between the two pins is covered. The only split is
which of the two pins is angularly nearer; the statement covers the full sector. -/
theorem two_pin_cover {a b z v : ℝ} (h : ContainedChart a |b|)
    (hb : |b| < 1/2) (hz : 0 ≤ z) (hv : 0 ≤ v) (hangle : z+v=Real.pi/3) :
    localPin a b (-z) ∨ localPin a b v := by
  rcases le_total z v with hnear | hnear
  · exact two_pin_left_near h hb hz hv hangle hnear
  · have hneg : ContainedChart a |-b| := by simpa only [abs_neg] using h
    have hbn : |-b| < 1/2 := by simpa only [abs_neg] using hb
    have hh := two_pin_left_near hneg hbn hv hz (by linarith) hnear
    rcases hh with hright | hleft
    · exact Or.inr ((localPin_reflect a b v).mp hright)
    · apply Or.inl
      apply (localPin_reflect a b (-z)).mp
      simpa only [neg_neg] using hleft

end SquaresInCircles.Six.Analytic
