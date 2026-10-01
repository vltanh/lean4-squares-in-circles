import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Two endpoint reductions

A combination `A cos t + B sin t` with `A, B ≥ 0` is concave on intervals in
`[0, π/2]`, so a strict lower bound at both ends of such an interval holds
inside it. A quartic that is positive at `l` and `u` is positive on `[l, u]`
when a quadratic `Q` is nonpositive there: the quartic exceeds its chord
through the two endpoint values by `-(x - l)(u - x) Q x`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

/-- `A cos t + B sin t`, with `A, B ≥ 0`, is concave on an interval in
`[0, π/2]`, so a strict lower bound at both ends holds inside. -/
theorem trig_lower_of_endpoints {A B C l u t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ l) (hu : u ≤ Real.pi / 2)
    (ht : l ≤ t ∧ t ≤ u)
    (hleft : C < A * Real.cos l + B * Real.sin l)
    (hright : C < A * Real.cos u + B * Real.sin u) :
    C < A * Real.cos t + B * Real.sin t := by
  let f : ℝ → ℝ := fun x => A * Real.cos x + B * Real.sin x
  let f' : ℝ → ℝ := fun x => -A * Real.sin x + B * Real.cos x
  let f'' : ℝ → ℝ := fun x => -A * Real.cos x - B * Real.sin x
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul A).add
      ((Real.hasDerivAt_sin x).const_mul B) using 1
    dsimp [f, f']
    ring
  have hdd (x : ℝ) : HasDerivAt f' (f'' x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B) using 1
    dsimp [f', f'']
    ring
  have hconc : ConcaveOn ℝ (Set.Icc l u) f := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
      (f' := f') (f'' := f'') (by dsimp [f]; fun_prop)
    · intro x _
      exact (hd x).hasDerivWithinAt
    · intro x _
      exact (hdd x).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc l u := interior_subset hx
      have hx0 : 0 ≤ x := hl.trans hx'.1
      have hxpi : x ≤ Real.pi / 2 := hx'.2.trans hu
      have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], hxpi⟩
      have hs : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0
        (by linarith [Real.pi_pos])
      have hAc := mul_nonneg hA hc
      have hBs := mul_nonneg hB hs
      dsimp [f'']
      linarith
  have hlu : l ≤ u := ht.1.trans ht.2
  have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl, hlu⟩ ⟨hlu, le_rfl⟩ ht
  exact (lt_min hleft hright).trans_le hmin

/-- The quartic with the coefficients `a0, …, a4`. -/
def quartic (a0 a1 a2 a3 a4 x : ℝ) : ℝ :=
  a0 + a1 * x + a2 * x ^ 2 + a3 * x ^ 3 + a4 * x ^ 4

/-- If the quadratic `Q x` of `hcurv` is nonpositive, a quartic positive at `l`
and `u` is positive at `x ∈ [l, u]`, since it exceeds its chord by
`-(x - l)(u - x) Q x`. -/
theorem quartic_positive_of_chord {a0 a1 a2 a3 a4 l u x : ℝ}
    (hlu : l < u) (hx : l ≤ x ∧ x ≤ u)
    (hl : 0 < quartic a0 a1 a2 a3 a4 l)
    (hu : 0 < quartic a0 a1 a2 a3 a4 u)
    (hcurv : a2 + a3 * (x + l + u) +
      a4 * (x ^ 2 + (l + u) * x + l ^ 2 + l * u + u ^ 2) ≤ 0) :
    0 < quartic a0 a1 a2 a3 a4 x := by
  have hleft : 0 ≤ u - x := sub_nonneg.mpr hx.2
  have hright : 0 ≤ x - l := sub_nonneg.mpr hx.1
  have hcorr := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlu.le) hright) hleft) hcurv
  have hid : (u - l) * quartic a0 a1 a2 a3 a4 x =
      (u - x) * quartic a0 a1 a2 a3 a4 l +
      (x - l) * quartic a0 a1 a2 a3 a4 u -
      (u - l) * (x - l) * (u - x) *
        (a2 + a3 * (x + l + u) +
          a4 * (x ^ 2 + (l + u) * x + l ^ 2 + l * u + u ^ 2)) := by
    dsimp [quartic]
    ring
  have hchord : 0 < (u - x) * quartic a0 a1 a2 a3 a4 l +
      (x - l) * quartic a0 a1 a2 a3 a4 u := by
    rcases lt_or_eq_of_le hx.2 with hxu | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hxu) hl)
        (mul_nonneg hright hu.le)
    · simpa using mul_pos (sub_pos.mpr hlu) hu
  by_contra! hbad
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlu.le) hbad
  nlinarith only [hid, hcorr, hchord, hmul]

end SquaresInCircles.Six.Analytic
