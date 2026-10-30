module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Eight squares: Taylor bounds of the sine and the cosine

For `x ≥ 0` the Taylor polynomials of the sine and the cosine bound them alternately:
`sin7 x ≤ sin x ≤ sin9 x` and `cos10 x ≤ cos x ≤ cos8 x` (`trig_taylor_bounds`). Starting from
the lower bound `sin_lower_seven`, each bound follows from the one before, as each difference
vanishes at `0` and its derivative is the difference before it. Since consecutive polynomials
differ by one term, `sin x = sin7 x + e x⁹` with `0 ≤ e ≤ 1/9!` and `cos x = cos8 x + e x¹⁰`
with `-1/10! ≤ e ≤ 0` (`sin_remainder_coefficient`, `cos_remainder_coefficient`); the
coefficient `e` depends on `x`, and only these bounds of it are used.

The module also bounds `π` to eighteen decimals (`pi_hand_enclosure`), with the consequences
`2π < 710/113` and `2π < 628318531 / 10⁸`. `TrigLin.lean` turns the Taylor bounds into lower
polynomials of `c₀ + c₁ u + c₂ sin u + c₃ cos u`.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

/-- `π` to eighteen decimals, from the bounds `Real.pi_gt_d20` and `Real.pi_lt_d20` of
Mathlib. -/
theorem pi_hand_enclosure :
    (3141592653589793238 : ℝ)/1000000000000000000 < Real.pi ∧
    Real.pi < (3141592653589793239 : ℝ)/1000000000000000000 := by
  constructor <;> linarith [Real.pi_gt_d20,Real.pi_lt_d20]

theorem two_pi_lt_710_over_113 : 2*Real.pi < (710 : ℝ)/113 := by
  linarith [pi_hand_enclosure.2]

theorem two_pi_lt_628318531_over_1e8 :
    2*Real.pi < (628318531 : ℝ)/100000000 := by
  linarith [pi_hand_enclosure.2]

/-- The Taylor polynomial of the sine through the degree seven. -/
def sin7 (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
/-- The Taylor polynomial of the sine through the degree nine. -/
def sin9 (x : ℝ) : ℝ := sin7 x+x^9/362880
/-- The Taylor polynomial of the cosine through the degree eight. -/
def cos8 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720+x^8/40320
/-- The Taylor polynomial of the cosine through the degree ten. -/
def cos10 (x : ℝ) : ℝ := cos8 x-x^10/3628800

theorem cos_le_cos8 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ cos8 x := by
  have h := nonneg_of_deriv_nonneg (fun t => cos8 t-Real.cos t)
    (by dsimp [cos8]; fun_prop) (by norm_num [cos8])
    (fun t ht => by
      simp (disch := fun_prop) [cos8]
      nlinarith [sin_lower_seven ht]) hx
  linarith

theorem sin_le_sin9 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ sin9 x := by
  have h := nonneg_of_deriv_nonneg (fun t => sin9 t-Real.sin t)
    (by dsimp [sin9,sin7]; fun_prop) (by norm_num [sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [sin9,sin7]
      have hc := cos_le_cos8 ht
      dsimp [cos8] at hc
      linarith) hx
  linarith

theorem cos10_le_cos {x : ℝ} (hx : 0 ≤ x) : cos10 x ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-cos10 t)
    (by dsimp [cos10,cos8]; fun_prop) (by norm_num [cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [cos10,cos8]
      have hs := sin_le_sin9 ht
      dsimp [sin9,sin7] at hs
      linarith) hx
  linarith

/-- For `x ≥ 0`, `sin7 x ≤ sin x ≤ sin9 x` and `cos10 x ≤ cos x ≤ cos8 x`. -/
theorem trig_taylor_bounds {x : ℝ} (hx : 0 ≤ x) :
    sin7 x ≤ Real.sin x ∧ Real.sin x ≤ sin9 x ∧
    cos10 x ≤ Real.cos x ∧ Real.cos x ≤ cos8 x :=
  ⟨sin_lower_seven hx,sin_le_sin9 hx,cos10_le_cos hx,cos_le_cos8 hx⟩

/-- For `x ≥ 0`, `sin x = sin7 x + e x⁹` for some `e ∈ [0, 1/9!]`. -/
theorem sin_remainder_coefficient {x : ℝ} (hx : 0 ≤ x) :
    ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1/362880 ∧ Real.sin x = sin7 x+e*x^9 := by
  rcases hx.eq_or_lt with he | hp
  · subst x
    exact ⟨0,by norm_num,by norm_num,by norm_num [sin7]⟩
  · refine ⟨(Real.sin x-sin7 x)/x^9,?_,?_,?_⟩
    · exact div_nonneg (sub_nonneg.mpr (trig_taylor_bounds hx).1) (pow_pos hp 9).le
    · apply (div_le_iff₀ (pow_pos hp 9)).mpr
      have hs := (trig_taylor_bounds hx).2.1
      dsimp [sin9] at hs
      linarith
    · field_simp [ne_of_gt hp]
      ring

/-- For `x ≥ 0`, `cos x = cos8 x + e x¹⁰` for some `e ∈ [-1/10!, 0]`. -/
theorem cos_remainder_coefficient {x : ℝ} (hx : 0 ≤ x) :
    ∃ e : ℝ, -(1/3628800) ≤ e ∧ e ≤ 0 ∧ Real.cos x = cos8 x+e*x^10 := by
  rcases hx.eq_or_lt with he | hp
  · subst x
    exact ⟨0,by norm_num,by norm_num,by norm_num [cos8]⟩
  · refine ⟨(Real.cos x-cos8 x)/x^10,?_,?_,?_⟩
    · apply (le_div_iff₀ (pow_pos hp 10)).mpr
      have hc := (trig_taylor_bounds hx).2.2.1
      dsimp [cos10] at hc
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (trig_taylor_bounds hx).2.2.2) (pow_pos hp 10).le
    · field_simp [ne_of_gt hp]
      ring

end SquaresInCircles.Eight.Arithmetic
