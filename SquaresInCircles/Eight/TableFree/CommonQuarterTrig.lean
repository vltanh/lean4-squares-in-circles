module

public import SquaresInCircles.Eight.TableFree.CommonQuarterState

/-!
# Whole-angle trigonometric reserves for common quarter-word supports

All inequalities hold on complete closed frame intervals. The only fixed
substitutions are the two geometric endpoints `1/10` and `7/10`.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CommonQuarter

open Arithmetic

theorem tenth_trig :
    9983/100000<Real.sin (1/10:ℝ) ∧ Real.sin (1/10:ℝ)<999/10000 ∧
      199/200≤Real.cos (1/10:ℝ) := by
  have hs := sin_lower_seven (show (0:ℝ)≤1/10 by norm_num)
  have hu := sin_upper_five (show (0:ℝ)≤1/10 by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (1/10:ℝ))
  refine ⟨?_,?_,?_⟩
  · have h : (9983/100000:ℝ)<1/10-(1/10)^3/6+(1/10)^5/120-(1/10)^7/5040 := by norm_num
    linarith
  · have h : (1/10:ℝ)-(1/10)^3/6+(1/10)^5/120<999/10000 := by norm_num
    linarith
  · have h : (199/200:ℝ)=1-(1/10)^2/2 := by norm_num
    linarith

theorem cap_trig :
    3221/5000<Real.sin (7/10:ℝ) ∧ Real.sin (7/10:ℝ)<16106/25000 ∧
      19121/25000<Real.cos (7/10:ℝ) ∧ Real.cos (7/10:ℝ)<191211/250000 := by
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  have hu := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hcu := cos_le_cos8 (show (0:ℝ)≤7/10 by norm_num)
  norm_num [cos8] at hs hu hc hcu
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem sin_mono {x y : ℝ} (hx : x∈Icc 0 (7/10))
    (hy : y∈Icc 0 (7/10)) (hxy : x≤y) : Real.sin x≤Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos]) (by linarith [hy.2,Real.pi_gt_three]) hxy

theorem cos_anti {x y : ℝ} (hx : x∈Icc 0 (7/10))
    (hy : y∈Icc 0 (7/10)) (hxy : x≤y) : Real.cos y≤Real.cos x :=
  Real.cos_le_cos_of_nonneg_of_le_pi hx.1
    (by linarith [hy.2,Real.pi_gt_three]) hxy

/-- Uniform signs, rational bounds and the full first-quadrant width. -/
theorem positive_trig {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    19121/25000<Real.cos x ∧ Real.cos x≤1 ∧
      0≤Real.sin x ∧ Real.sin x<16106/25000 ∧
      Real.sin x≤x ∧ 1≤Real.sin x+Real.cos x := by
  have hc := (cap_trig.2.2.1).trans_le
    (cos_anti hx ⟨by norm_num,le_rfl⟩ hx.2)
  have hs0 : 0≤Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hs := (sin_mono hx ⟨by norm_num,le_rfl⟩ hx.2).trans_lt cap_trig.2.1
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_pos (by linarith : 0<Real.cos x),abs_of_nonneg hs0] at hw
  exact ⟨hc,Real.cos_le_one x,hs0,hs,Real.sin_le hx.1,by linarith⟩

theorem positive_taylor_reserves {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (9/10)*x≤Real.sin x ∧ (47/100)*x^2≤1-Real.cos x ∧
      1-Real.cos x≤x^2/2 := by
  have hs := Real.sin_ge_sub_cube hx.1
  have hc := cos_upper_four hx.1
  have hl := Real.one_sub_sq_div_two_le_cos (x := x)
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := mul_le_mul_of_nonneg_right hx2 hx.1
  have hx4 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
  exact ⟨by linarith [hx.1],by linarith [sq_nonneg x],by linarith⟩

theorem signed_cos {x : ℝ} (hx : |x|≤7/10) :
    19121/25000<Real.cos x ∧ Real.cos x≤1 := by
  by_cases hp : 0≤x
  · exact ⟨(positive_trig ⟨hp,(abs_le.mp hx).2⟩).1,Real.cos_le_one x⟩
  · have h := positive_trig (x := -x)
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [Real.cos_neg] using And.intro h.1 h.2.1

theorem signed_sin {x : ℝ} (hx : |x|≤7/10) : |Real.sin x|<16106/25000 := by
  by_cases hp : 0≤x
  · have h := positive_trig ⟨hp,(abs_le.mp hx).2⟩
    simpa only [abs_of_nonneg h.2.2.1] using h.2.2.2.1
  · have h := positive_trig (x := -x)
      ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hs : Real.sin x≤0 := by simpa only [Real.sin_neg,neg_nonneg] using h.2.2.1
    rw [abs_of_nonpos hs]
    simpa only [Real.sin_neg] using h.2.2.2.1

theorem signed_width {x : ℝ} (hx : |x|≤7/10) :
    pairWidth x=(1+Real.cos x+|Real.sin x|)/2 := by
  have hc : 0<Real.cos x := by linarith [(signed_cos hx).1]
  simp [pairWidth,abs_of_pos hc,add_comm,add_left_comm,add_assoc]

theorem quarter_width {x : ℝ} (hx : |x|≤7/10) :
    pairWidth (Real.pi/2+x)=(1+Real.cos x+|Real.sin x|)/2 := by
  have hc : 0<Real.cos x := by linarith [(signed_cos hx).1]
  simp [pairWidth,Real.sin_add,Real.cos_add,abs_of_pos hc,abs_neg]

/-- A lower harmonic support for all three sine-norm applications. -/
theorem ratio_harmonic {x l : ℝ} (hx : x∈Icc (1/10) (7/10))
    (hl : 1939/2000≤l) :
    (203/200:ℝ)<l*Real.cos x+(3/5)*Real.sin x := by
  have hbase : (203/200:ℝ)<(1939/2000)*Real.cos x+(3/5)*Real.sin x := by
    have hh := harmonic_pos_of_endpoints (K := -(203/200:ℝ))
      (A := (1939/2000:ℝ)) (B := (3/5:ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three]) hx
      (by linarith [tenth_trig.1,tenth_trig.2.2])
      (by linarith [cap_trig.1,cap_trig.2.2.1])
    linarith
  have hc : 0≤Real.cos x := by
    linarith [(positive_trig ⟨by linarith [hx.1],hx.2⟩).1]
  have hm := mul_le_mul_of_nonneg_right hl hc
  linarith

end SquaresInCircles.Eight.CommonQuarter
