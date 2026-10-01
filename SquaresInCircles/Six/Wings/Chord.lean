import SquaresInCircles.Six.Supports

/-!
# The chord term

With weight `z` on C–D and `1` on W–D and D–S the force on D is
`(z + sin q, cos q - 1)`, of length at most `(2 + z²/4) sin (q/2) + z cos (q/2)`
(`chord_support`); this leaves in the stresses the chord term
`sin q - L sin (q/2) - M cos (q/2)`, with `L = R̄ (2 + z²/4)` and `M = R̄ z`. Its
second derivative is bounded by one quintic on `[1/2, 5/3]`, which the
endpoint lemma for concave functions bounds by `3/40 - (3/10) min (q, 1)` and,
beyond `157/200`, by `-19/100`.
-/

noncomputable section
namespace SquaresInCircles.Six.Wings
open Normalization

/-- The chord term: up to a constant, the threshold of W–D less the support of D,
with `L = R̄ (2 + z²/4)` and `M = R̄ z`. -/
def chord (L M q : ℝ) : ℝ := Real.sin q-L*Real.sin (q/2)-M*Real.cos (q/2)
def chordFirst (L M q : ℝ) : ℝ := Real.cos q-(L/2)*Real.cos (q/2)+(M/2)*Real.sin (q/2)

/-- `R̄ (2 + z²/4)` and `R̄ z` for `z = 9/20`, the largest weight on C–D. -/
def chordSin : ℝ := 27701483/8000000
def chordCos : ℝ := 75987/100000

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

private def p (q : ℝ) : ℝ :=
  19/100-(567/1000)*q-(23/1000)*q^2+(149/1000)*q^3+(1/2000)*q^4-(19/2500)*q^5
private def pFirst (q : ℝ) : ℝ :=
  -567/1000-(23/500)*q+(447/1000)*q^2+(1/500)*q^3-(19/500)*q^4
private def pSecond (q : ℝ) : ℝ :=
  -23/500+(447/500)*q+(3/500)*q^2-(19/125)*q^3

private lemma polynomial_upper {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 1/2 ≤ q ∧ q ≤ 5/3) : chordSecond L M q ≤ p q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  obtain ⟨hc,hs⟩ := cos_sin_nonneg (x := q/2) ⟨by linarith,by linarith [Real.pi_gt_d2]⟩
  have hLs := mul_le_mul_of_nonneg_right hL hs
  have hMc := mul_le_mul_of_nonneg_right hM hc
  have hl := sin_lower_seven hq0
  have hu := sin_upper_five (x := q/2) (by linarith)
  have hcu := cos_upper_four (x := q/2) (by linarith)
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2) (show 0 ≤ 5/3+q by linarith)
  have h7 := mul_nonneg (show 0 ≤ 25/9-q^2 by nlinarith only [hsq])
    (show 0 ≤ q^5 by positivity)
  have h3 : 0 ≤ q^3 := by positivity
  have h5 : 0 ≤ q^5 := by positivity
  dsimp [chordSecond,chordSin,chordCos,p] at *
  nlinarith only [hl,hu,hcu,h7,hq0,h3,h5,hLs,hMc,sq_nonneg q,sq_nonneg (q^2)]

private lemma p_hasDeriv (q : ℝ) : HasDerivAt p (pFirst q) q := by
  have h := ((((((hasDerivAt_id' q).const_mul (-(567/1000))).const_add (19/100)).fun_add
    (((hasDerivAt_id' q).pow 2).const_mul (-(23/1000)))).fun_add
    (((hasDerivAt_id' q).pow 3).const_mul (149/1000))).fun_add
    (((hasDerivAt_id' q).pow 4).const_mul (1/2000))).fun_add
    (((hasDerivAt_id' q).pow 5).const_mul (-(19/2500)))
  have e : p = fun x : ℝ => 19/100 + -(567/1000) * x + -(23/1000) * x^2 +
      149/1000 * x^3 + 1/2000 * x^4 + -(19/2500) * x^5 := by
    funext x; simp only [p]; ring
  rw [e]
  exact h.congr_deriv (by simp only [pFirst]; norm_num; ring)

private lemma p_first_hasDeriv (q : ℝ) : HasDerivAt pFirst (pSecond q) q := by
  have h := (((((hasDerivAt_id' q).const_mul (-(23/500))).const_add (-(567/1000))).fun_add
    (((hasDerivAt_id' q).pow 2).const_mul (447/1000))).fun_add
    (((hasDerivAt_id' q).pow 3).const_mul (1/500))).fun_add
    (((hasDerivAt_id' q).pow 4).const_mul (-(19/500)))
  have e : pFirst = fun x : ℝ => -(567/1000) + -(23/500) * x + 447/1000 * x^2 +
      1/500 * x^3 + -(19/500) * x^4 := by
    funext x; simp only [pFirst]; ring
  rw [e]
  exact h.congr_deriv (by simp only [pSecond]; norm_num; ring)

private lemma envelope_concave (a c : ℝ) {l u : ℝ} (hl : 1/2 ≤ l) (hu : u ≤ 5/3) :
    ConcaveOn ℝ (Set.Icc l u) (fun q => a+c*q-p q) :=
  concave_of_deriv2 (f' := fun q => c-pFirst q) (f'' := fun q => -pSecond q)
    (fun q _ => ((((hasDerivAt_id' q).const_mul c).const_add a).fun_sub
      (p_hasDeriv q)).congr_deriv (by ring))
    (fun q _ => ((hasDerivAt_const q c).fun_sub (p_first_hasDeriv q)).congr_deriv (by ring))
    fun q ⟨h1,h2⟩ => by
      have hq0 : 0 ≤ q := by linarith
      have hsq := mul_nonneg (show 0 ≤ 5/3-q by linarith) (show 0 ≤ 5/3+q by linarith)
      have h3 := mul_nonneg (show 0 ≤ 25/9-q^2 by nlinarith only [hsq]) hq0
      have hlq : 1/2 ≤ q := by linarith
      simp only [pSecond]
      nlinarith only [h3,hlq,sq_nonneg q]

/-- The curvature of the chord term is at most `3/40 - (3/10) min(q, 1)` on
`[1/2, 3/2]`. -/
lemma chord_second_envelope {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 1/2 ≤ q ∧ q ≤ 3/2) : chordSecond L M q ≤ 3/40-(3/10)*min q 1 := by
  have hp := polynomial_upper hL hM ⟨hq.1,by linarith [hq.2]⟩
  by_cases hq1 : q ≤ 1
  · rw [min_eq_left hq1]
    have h := concave_gt_of_endpoints (c := 0)
      (envelope_concave (3/40) (-(3/10)) (l := 1/2) (u := 1) (by norm_num) (by norm_num))
      ⟨hq.1,hq1⟩ (by norm_num [p]) (by norm_num [p])
    linarith
  · rw [min_eq_right (le_of_not_ge hq1)]
    have h := concave_gt_of_endpoints (c := 0)
      (envelope_concave (-(9/40)) 0 (l := 1) (u := 3/2) (by norm_num) (by norm_num))
      ⟨le_of_not_ge hq1,hq.2⟩ (by norm_num [p]) (by norm_num [p])
    linarith

/-- The curvature of the chord term is at most `-19/100` on `[157/200, 5/3]`. -/
lemma chord_second_high {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 157/200 ≤ q ∧ q ≤ 5/3) : chordSecond L M q ≤ -(19/100) := by
  have hp := polynomial_upper hL hM ⟨by linarith [hq.1],hq.2⟩
  have h := concave_gt_of_endpoints (c := 0)
    (envelope_concave (-(19/100)) 0 (l := 157/200) (u := 5/3) (by norm_num) (by norm_num))
    hq (by norm_num [p]) (by norm_num [p])
  linarith

lemma chord_second_nonpositive {L M q : ℝ} (hL : L ≤ chordSin) (hM : M ≤ chordCos)
    (hq : 1/2 ≤ q ∧ q ≤ 5/3) : chordSecond L M q ≤ 0 := by
  by_cases hq1 : q ≤ 1
  · have h := chord_second_envelope hL hM ⟨hq.1,by linarith⟩
    have hm : (1:ℝ)/2 ≤ min q 1 := le_min hq.1 (by norm_num)
    linarith
  · linarith [chord_second_high hL hM ⟨by linarith,hq.2⟩]

end SquaresInCircles.Six.Wings
