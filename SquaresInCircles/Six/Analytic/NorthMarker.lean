import SquaresInCircles.Six.Analytic.CoreProfiles
import SquaresInCircles.Six.Analytic.BasicExclusions

/-!
# North markers when the centre of C is high

Let the centre `(x, y)` of C satisfy `c0 < y ≤ x ≤ 1/2`. A contained square
with phase `π/2 + t`, `|t| ≤ π/4`, that is separated from C along its own axis
has `t ≥ 0`, and its marker is at least `π/2`. The own margin gives
`a ≥ 1/2 + (rho0 - 1/2) cos t`, and then `u ≤ (4/5) t`, since otherwise the
far corner would be at squared distance more than `Q0` from the disk centre:
the excess has a positive linear term in `t` that dominates its only negative
quadratic term on `0 ≤ t ≤ 4/5`. So the label is at most `t`. A contained
square with `a ≥ 1` also has `u < 3/10`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma north_large_transverse {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (ha : 1/2+(rho0-1/2)*Real.cos t ≤ a) : u ≤ (4/5)*t := by
  let k : ℝ := rho0-1/2
  have hk0 : 0 ≤ k := by dsimp [k]; linarith [rho0_lower]
  have hk1 : k ≤ 613/1000 := by dsimp [k]; linarith [rho0_upper]
  have hksq := mul_nonneg (sub_nonneg.mpr hk1)
    (show 0 ≤ 613/1000+k by linarith)
  have hk : k+k^2 ≤ 1 := by nlinarith
  have ht : t ≤ 4/5 := by linarith [ht1,Real.pi_lt_d2]
  have ht2 := pow_le_pow_left₀ ht0 ht 2
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := t)) hk0
  let A : ℝ := 1+k-k*t^2/2
  let B : ℝ := 1/2+(4/5)*t
  have hA : A ≤ a+1/2 := by dsimp [A,k] at *; linarith
  have hA0 : 0 ≤ A := by
    have hp := mul_nonneg hk0 (show 0 ≤ 1-t^2/2 by nlinarith)
    dsimp [A]
    nlinarith only [hp]
  have hB0 : 0 < B := by dsimp [B]; linarith
  have hid : (1+k)^2+1/4=Q0 := by dsimp [k]; nlinarith [rho0_identity]
  have hcoef := mul_nonneg (show 0 ≤ 1-k-k^2 by linarith) (sq_nonneg t)
  have htail := mul_nonneg (sq_nonneg k) (pow_nonneg ht0 4)
  have htq := mul_nonneg ht0 (show 0 ≤ 4/5-t by linarith)
  have hbase : Q0 ≤ A^2+B^2 := by
    dsimp [A,B]
    nlinarith only [hid,hcoef,htail,htq,ht0]
  by_contra! hfail
  have hB : B < u+1/2 := by dsimp [B]; linarith
  have hAsq := mul_nonneg (sub_nonneg.mpr hA)
    (show 0 ≤ a+1/2+A by linarith [h.half_le])
  have hBsq := mul_pos (sub_pos.mpr hB)
    (show 0 < u+1/2+B by linarith [h.u_nonneg])
  nlinarith [h.containment]

lemma north_large_label {a u t : ℝ} (h : ContainedChart a u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/4)
    (ha : 1/2+(rho0-1/2)*Real.cos t ≤ a) : Seven.label a u ≤ t := by
  have hu := north_large_transverse h ht0 ht1 ha
  have hl := h.seven_admissible.label_le_axial
  dsimp [Seven.axial] at hl
  linarith

lemma north_own_negative_impossible {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (ht0 : t ≤ 0)
    (hy : c0 < y) (hxy : y ≤ x)
    (hm : 0 ≤ centralMargin .own (Real.pi/2+t) a b x y) : False := by
  have hc := octant_trig ht
  have hs : Real.sin t ≤ 0 := by
    have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ -t by linarith)
      (by have hh := abs_le.mp ht; linarith [hh.1,Real.pi_pos])
    rw [Real.sin_neg] at hh
    linarith
  have hprod := mul_le_mul_of_nonpos_right hxy hs
  have hy0 : 0 ≤ y+1/2 := by linarith [c0_pos]
  have hwidth := mul_le_mul_of_nonneg_left hc.2.2 hy0
  rw [abs_of_nonpos hs] at hwidth
  rw [north_own] at hm
  dsimp [angularWidth] at hm
  rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1]),abs_of_nonpos hs] at hm
  dsimp [c0] at hy
  nlinarith [h.a_le_rho0]

lemma north_own_large_marker {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hy : c0 < y) (hxy : y ≤ x) (hx : x ≤ 1/2)
    (hm : 0 ≤ centralMargin .own (Real.pi/2+t) a b x y) :
    0 ≤ t+signedLabel a b := by
  have ht0 : 0 ≤ t := by
    by_contra! hneg
    exact north_own_negative_impossible h ht hneg.le hy hxy hm
  have hc := octant_trig ht
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht0
    (by have hh := abs_le.mp ht; linarith [hh.2,Real.pi_pos])
  have hxc := mul_nonneg (show 0 ≤ 1/2-x by linarith) hs
  have hyc := mul_le_mul_of_nonneg_right hy.le
    (show 0 ≤ Real.cos t by linarith [hc.1.1])
  have ha : 1/2+(rho0-1/2)*Real.cos t ≤ a := by
    rw [north_own] at hm
    dsimp [angularWidth,c0] at hm hyc
    rw [abs_of_nonneg (show 0 ≤ Real.cos t by linarith [hc.1.1]),abs_of_nonneg hs] at hm
    nlinarith
  have hlabel := north_large_label h ht0 ((le_abs_self t).trans ht) ha
  by_cases hb : b < 0
  · rw [signedLabel_of_neg hb]
    linarith
  · rw [signedLabel_of_nonneg (le_of_not_gt hb)]
    linarith [h.seven_admissible.label_nonneg]

lemma transverse_lt_three_tenths {a u : ℝ} (h : ContainedChart a u) (ha : 1 ≤ a) : u < 3/10 := by
  by_contra! hu
  have hp := mul_nonneg (show 0 ≤ a-1 by linarith)
    (show 0 ≤ a+2 by linarith)
  have hq := mul_nonneg (show 0 ≤ u-3/10 by linarith)
    (show 0 ≤ u+13/10 by linarith)
  have hh := h.containment
  norm_num [Q0] at hh
  nlinarith

end SquaresInCircles.Six.Analytic
