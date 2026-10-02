module

public import SquaresInCircles.Six.Supports

/-!
# Six squares: the chord term

With weight `z` on C–D and `1` on W–D and D–S the force on D is
`(z + sin q, cos q - 1)`, of length at most `(2 + z²/4) sin (q/2) + z cos (q/2)`
(`chord_support`); this leaves in the stresses the chord term
`sin q - L sin (q/2) - M cos (q/2)`, with `L = R̄ (2 + z²/4)` and `M = R̄ z`. Its
second derivative, the curvature, grows with `L` and `M`, and is minus the chord
term of `L/4` and `M/4`. At `chordSin` and `chordCos`, the values for the
largest weight `9/20`, it is therefore convex on `[1/2, 5/3]`, where
`sin q ≥ q - q³/6` exceeds `(L/16) sin (q/2) + (M/16) cos (q/2)`; it lies below
its chords, and Taylor polynomials at the ends bound it by
`3/40 - (3/10) min (q, 1)` on `[1/2, 3/2]` and, beyond `157/200`, by `-19/100`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.Wings
open Normalization

/-- The chord term: up to a constant, the threshold of W–D less the support of D,
with `L = R̄ (2 + z²/4)` and `M = R̄ z`. -/
def chord (L M q : ℝ) : ℝ := Real.sin q-L*Real.sin (q/2)-M*Real.cos (q/2)
def chordFirst (L M q : ℝ) : ℝ := Real.cos q-(L/2)*Real.cos (q/2)+(M/2)*Real.sin (q/2)

/-- `R̄ (2 + z²/4)` and `R̄ z` for `z = 9/20`, the largest weight on C–D, with the
ceiling `R̄ = 1.6886` of the radius. -/
def chordSin : ℝ := 1.6886*(2+(9/20)^2/4)
def chordCos : ℝ := 1.6886*(9/20)

/-- The second derivative of `sin q - L sin (q/2) - M cos (q/2)`. -/
def chordSecond (L M q : ℝ) : ℝ := -Real.sin q+(L/4)*Real.sin (q/2)+(M/4)*Real.cos (q/2)

lemma chord_hasDerivAt (L M q : ℝ) : HasDerivAt (chord L M) (chordFirst L M q) q :=
  (((Real.hasDerivAt_sin q).sub ((((hasDerivAt_id' q).div_const 2).sin).const_mul L)).sub
    ((((hasDerivAt_id' q).div_const 2).cos).const_mul M)).congr_deriv
    (by simp only [chordFirst]; ring)

lemma chordFirst_hasDerivAt (L M q : ℝ) :
    HasDerivAt (chordFirst L M) (chordSecond L M q) q :=
  (((Real.hasDerivAt_cos q).sub ((((hasDerivAt_id' q).div_const 2).cos).const_mul (L/2))).add
    ((((hasDerivAt_id' q).div_const 2).sin).const_mul (M/2))).congr_deriv
    (by simp only [chordSecond]; ring)

/-- Below `chordSin` and `chordCos` the curvature is at most its value at
`chordSin` and `chordCos`. -/
private lemma second_le_top {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 0 ≤ q ∧ q ≤ 5/3) : chordSecond L M q ≤ chordSecond chordSin chordCos q := by
  obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := q/2)
    ⟨by linarith [hq.1],by linarith [hq.2,Real.pi_gt_d2]⟩
  have hLs := mul_le_mul_of_nonneg_right hL hs
  have hMc := mul_le_mul_of_nonneg_right hM hc
  simp only [chordSecond]
  linarith

/-- An affine function less the curvature at `chordSin`, `chordCos` is concave on
`[l, u] ⊆ [1/2, 5/3]`: its second derivative, the curvature at `chordSin/4`,
`chordCos/4`, is negative, as `sin q ≥ q - q³/6`. -/
private lemma top_concave (a c : ℝ) {l u : ℝ} (hl : 1/2 ≤ l) (hu : u ≤ 5/3) :
    ConcaveOn ℝ (Set.Icc l u) (fun q => a+c*q-chordSecond chordSin chordCos q) := by
  have e : (fun q => a+c*q-chordSecond chordSin chordCos q) =
      fun q => a+c*q+chord (chordSin/4) (chordCos/4) q := by
    funext q; simp only [chordSecond,chord]; ring
  rw [e]
  refine concave_of_deriv2 (f' := fun q => c+chordFirst (chordSin/4) (chordCos/4) q)
    (f'' := chordSecond (chordSin/4) (chordCos/4))
    (fun q _ => ((((hasDerivAt_id' q).const_mul c).const_add a).add
      (chord_hasDerivAt _ _ q)).congr_deriv (by ring))
    (fun q _ => (chordFirst_hasDerivAt _ _ q).const_add c) (fun q ⟨h1,h2⟩ => ?_)
  have hq0 : 0 ≤ q := by linarith
  have hs := Real.sin_ge_sub_cube hq0
  have hh := Real.sin_le (show 0 ≤ q/2 by linarith)
  have hc := Real.cos_le_one (q/2)
  have h3 := mul_nonneg hq0 (show 0 ≤ 25/9-q^2 by nlinarith)
  simp only [chordSecond,chordSin,chordCos]
  nlinarith

/-- The curvature at `chordSin`, `chordCos` lies below its Taylor polynomials. -/
private lemma top_endpoint {a c q : ℝ} (hq : 0 ≤ q)
    (h : -sinLower q+(chordSin/4)*sinUpper (q/2)+(chordCos/4)*cosUpper (q/2) < a+c*q) :
    0 < a+c*q-chordSecond chordSin chordCos q := by
  have hs := sinLower_le hq
  have hh := mul_le_mul_of_nonneg_left (le_sinUpper (x := q/2) (by linarith))
    (show (0:ℝ) ≤ chordSin/4 by norm_num [chordSin])
  have hc := mul_le_mul_of_nonneg_left (le_cosUpper (q/2))
    (show (0:ℝ) ≤ chordCos/4 by norm_num [chordCos])
  simp only [chordSecond]
  linarith

/-- The curvature of the chord term is at most `3/40 - (3/10) min(q, 1)` on
`[1/2, 3/2]`. -/
lemma chord_second_envelope {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 1/2 ≤ q ∧ q ≤ 3/2) : chordSecond L M q ≤ 3/40-(3/10)*min q 1 := by
  have hp := second_le_top hL hM ⟨by linarith [hq.1],by linarith [hq.2]⟩
  by_cases hq1 : q ≤ 1
  · rw [min_eq_left hq1]
    have h := concave_gt_of_endpoints (c := 0)
      (top_concave (3/40) (-(3/10)) (l := 1/2) (u := 1) (by norm_num) (by norm_num))
      ⟨hq.1,hq1⟩
      (top_endpoint (by norm_num) (by norm_num [sinLower,sinUpper,cosUpper,chordSin,chordCos]))
      (top_endpoint (by norm_num) (by norm_num [sinLower,sinUpper,cosUpper,chordSin,chordCos]))
    linarith
  · rw [min_eq_right (le_of_not_ge hq1)]
    have h := concave_gt_of_endpoints (c := 0)
      (top_concave (-(9/40)) 0 (l := 1) (u := 3/2) (by norm_num) (by norm_num))
      ⟨le_of_not_ge hq1,hq.2⟩
      (top_endpoint (by norm_num) (by norm_num [sinLower,sinUpper,cosUpper,chordSin,chordCos]))
      (top_endpoint (by norm_num) (by norm_num [sinLower,sinUpper,cosUpper,chordSin,chordCos]))
    linarith

/-- The curvature of the chord term is at most `-19/100` on `[157/200, 5/3]`. -/
lemma chord_second_high {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 157/200 ≤ q ∧ q ≤ 5/3) : chordSecond L M q ≤ -(19/100) := by
  have hp := second_le_top hL hM ⟨by linarith [hq.1],hq.2⟩
  have h := concave_gt_of_endpoints (c := 0)
    (top_concave (-(19/100)) 0 (l := 157/200) (u := 5/3) (by norm_num) (by norm_num)) hq
    (top_endpoint (by norm_num) (by norm_num [sinLower,sinUpper,cosUpper,chordSin,chordCos]))
    (top_endpoint (by norm_num) (by norm_num [sinLower,sinUpper,cosUpper,chordSin,chordCos]))
  linarith

lemma chord_second_nonpositive {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 1/2 ≤ q ∧ q ≤ 5/3) : chordSecond L M q ≤ 0 := by
  by_cases hq1 : q ≤ 1
  · have h := chord_second_envelope hL hM ⟨hq.1,by linarith⟩
    have hm : (1:ℝ)/2 ≤ min q 1 := le_min hq.1 (by norm_num)
    linarith
  · linarith [chord_second_high hL hM ⟨by linarith,hq.2⟩]

end SquaresInCircles.Six.Wings
