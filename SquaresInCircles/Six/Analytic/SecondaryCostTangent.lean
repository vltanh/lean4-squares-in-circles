import SquaresInCircles.Six.Analytic.HalfAngleControl
import SquaresInCircles.Six.Normalization.CapBounds

/-!
# A uniform affine lower bound for the equal-weight secondary cap cost

The cap cost is -rho + cos(q)/2 -(rho-1/2) sin(q). Replace rho by the
proved upper bound 1113/1000. Around q0=13/10 its trigonometric addition
formula, the whole-interval sine error, and the cosine quadratic give
  F(q) >= 1/500 + 7 h^2/200 - |h|/200 > 0,
where h=q-q0. The last inequality is the displayed square (14|h|-1)^2.
The point q0 is a Taylor center, not a sampled or subdivided proof domain.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma sine_error_on_half {h : ℝ} (hh : |h|≤1/2) :
    -(h^2)/12≤Real.sin h-h ∧ Real.sin h-h≤h^2/12 := by
  have hu : 0≤|h| := abs_nonneg h
  have hl := Real.sin_ge_sub_cube hu
  have hr := Real.sin_le hu
  have hp := mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg |h|)
  rw [sq_abs] at hp
  by_cases h0 : 0≤h
  · rw [abs_of_nonneg h0] at hl hr hp
    constructor <;> nlinarith only [hl,hr,hp]
  · have hn : h<0 := lt_of_not_ge h0
    rw [abs_of_neg hn,Real.sin_neg] at hl hr
    rw [abs_of_neg hn] at hp
    constructor <;> nlinarith only [hl,hr,hp]

def secondaryCapLine (q : ℝ) : ℝ :=
  91/125-1113/1000+(13/20)*q+Real.cos q/2-(613/1000)*Real.sin q

private def tangentA : ℝ := Real.cos (13/10)/2-(613/1000)*Real.sin (13/10)
private def tangentB : ℝ := -Real.sin (13/10)/2-(613/1000)*Real.cos (13/10)

private lemma secondary_tangent_constants :
    tangentA≤-9/20 ∧ -33/50≤tangentB ∧ tangentB≤0 ∧
      |13/20+tangentB|≤1/200 ∧ 1/500≤ secondaryCapLine (13/10) := by
  have hcl := Seven.cos_lower_six (x := (13:ℝ)/10) (by norm_num)
  have hcu := Seven.cos_upper_four (x := (13:ℝ)/10) (by norm_num)
  have hsl := Seven.sin_lower_seven (x := (13:ℝ)/10) (by norm_num)
  have hsu := Seven.sin_upper_five (x := (13:ℝ)/10) (by norm_num)
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

/-- A completed-square certificate for the entire cap-side interval. -/
theorem secondary_cap_line_positive {q : ℝ} (hq : 1≤q ∧ q≤Real.pi/2) :
    0< secondaryCapLine q := by
  let h := q-13/10
  have hh : |h|≤1/2 := by
    apply abs_le.mpr
    dsimp [h]
    constructor <;> linarith [hq.1,hq.2,Real.pi_lt_d2]
  obtain ⟨hA,hBl,hBu,hBlin,hbase⟩ := secondary_tangent_constants
  have hA0 : tangentA≤0 := by linarith
  have hc := Normalization.cos_le_one_sub_fifth_sq
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

end SquaresInCircles.Six.Analytic
