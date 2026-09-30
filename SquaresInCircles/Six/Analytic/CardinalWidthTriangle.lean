module
public import SquaresInCircles.Six.Analytic.HighDiagonalProfile
public import SquaresInCircles.Six.Normalization.OwnEastExclusion

@[expose] public section

/-!
# Cardinal width terms contain a whole diagonal width

For |x|<=2/5 and 1/2<=d<=pi/4,
  width(x)+width(d-x) >= 1/2+width(d).
For x>=0 this follows from an explicit product decomposition. For x<0 the
reverse-angle case is bounded by sin(v)-(5/2)(1-cos(v)), which is nonnegative
throughout [0,2/5] by one Taylor polynomial. These are the two sign cases,
not a subdivision of the helper rectangle.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma first_quadrant_trig {x : ℝ} (hx : 0≤x ∧ x≤Real.pi/2) :
    0≤Real.cos x ∧ 0≤Real.sin x :=
  ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])⟩

lemma cardinal_width_triangle {x d : ℝ}
    (hx : |x|≤2/5) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    1/2+angularWidth d≤angularWidth x+angularWidth (d-x) := by
  have hx' := abs_le.mp hx
  have hdtr := first_quadrant_trig
    (show 0≤d ∧ d≤Real.pi/2 by constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hytr := first_quadrant_trig
    (show 0≤d-x ∧ d-x≤Real.pi/2 by
      constructor <;> linarith [hx'.1,hx'.2,hd.1,hd.2,Real.pi_gt_d2])
  by_cases hx0 : 0≤x
  · have hxtr := first_quadrant_trig
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
    have hvtr := first_quadrant_trig
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

end SquaresInCircles.Six.Analytic
