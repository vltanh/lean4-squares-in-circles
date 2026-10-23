module

public import SquaresInCircles.Eight.Arithmetic.Interval

/-!
# Taylor remainder semantics used by the one-angle tables

The unknown remainder coefficients can depend on the angle.  The witnesses
below are pointwise; no derivative of a remainder coefficient is assumed.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic

/-- The rational pi enclosure already proved in mathlib uses Machin's
identity and arctangent-series bounds; the source proof is reused here. -/
theorem pi_hand_enclosure :
    (3141592653589793238 : ℝ)/1000000000000000000 < Real.pi ∧
    Real.pi < (3141592653589793239 : ℝ)/1000000000000000000 := by
  constructor <;> linarith [Real.pi_gt_d20,Real.pi_lt_d20]

theorem two_pi_lt_710_over_113 : 2*Real.pi < (710 : ℝ)/113 := by
  linarith [pi_hand_enclosure.2]

theorem two_pi_lt_628318531_over_1e8 :
    2*Real.pi < (628318531 : ℝ)/100000000 := by
  linarith [pi_hand_enclosure.2]

def sin7 (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
def sin9 (x : ℝ) : ℝ := sin7 x+x^9/362880
def cos8 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720+x^8/40320
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

theorem trig_taylor_bounds {x : ℝ} (hx : 0 ≤ x) :
    sin7 x ≤ Real.sin x ∧ Real.sin x ≤ sin9 x ∧
    cos10 x ≤ Real.cos x ∧ Real.cos x ≤ cos8 x :=
  ⟨sin_lower_seven hx,sin_le_sin9 hx,cos10_le_cos hx,cos_le_cos8 hx⟩

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

/-- The global cubic radical majorant from hand equation (8.3). -/
def radicalMajorant (h V : ℝ) : ℝ :=
  (5*h+15*V/h-5*V^2/h^3+V^3/h^5)/16

theorem radical_majorant_identity {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V) :
    radicalMajorant h V-Real.sqrt V =
      (Real.sqrt V-h)^4*(V+4*h*Real.sqrt V+5*h^2)/(16*h^5) := by
  have hs : (Real.sqrt V)^2 = V := Real.sq_sqrt hV
  have hid (s : ℝ) : radicalMajorant h (s^2)-s =
      (s-h)^4*(s^2+4*h*s+5*h^2)/(16*h^5) := by
    unfold radicalMajorant
    field_simp [ne_of_gt hh]
    ring
  simpa only [hs] using hid (Real.sqrt V)

theorem sqrt_le_radicalMajorant {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V) :
    Real.sqrt V ≤ radicalMajorant h V := by
  have hn : 0 ≤ (Real.sqrt V-h)^4*(V+4*h*Real.sqrt V+5*h^2)/(16*h^5) := by
    positivity
  rw [← radical_majorant_identity hh hV] at hn
  linarith

end SquaresInCircles.Eight.Arithmetic
