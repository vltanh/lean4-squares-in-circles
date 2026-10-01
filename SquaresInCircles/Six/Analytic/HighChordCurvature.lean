import SquaresInCircles.Six.Analytic.OwnSouthWestDominant.Chord

/-!
# Curvature of the chord term at high angles

On `157/200 ≤ q ≤ 5/3`, the chord term `sin q - L sin (q/2) - M cos (q/2)` has
second derivative at most `-19/100` whenever `L` and `M` are at most the
coefficients of the west-dominant chord. For those coefficients Taylor bounds
give a quintic majorant of the second derivative; the majorant is convex on the
interval, so it is largest at an endpoint, where it is below `-19/100`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.HighChordCurvature

private def polynomial (q : ℝ) : ℝ :=
  19/100-(567/1000)*q-(23/1000)*q^2+(149/1000)*q^3+
    (1/2000)*q^4-(3/400)*q^5
private def first (q : ℝ) : ℝ :=
  -567/1000-(23/500)*q+(447/1000)*q^2+(1/500)*q^3-(3/80)*q^4
private def second (q : ℝ) : ℝ :=
  -23/500+(447/500)*q+(3/500)*q^2-(3/20)*q^3

private lemma polynomial_upper {q : ℝ} (hq : 157/200 ≤ q ∧ q ≤ 5/3) :
    OwnSouthWestDominant.chordSecond q ≤ polynomial q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hl := Seven.sin_lower_seven hq0
  have hu := Seven.sin_upper_five (x := q/2) (by linarith)
  have hc := Seven.cos_upper_four (x := q/2) (by linarith)
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0 ≤ 5/3+q by linarith)
  have h7 := mul_nonneg (show 0 ≤ 25/9-q^2 by nlinarith only [hsq])
    (show 0 ≤ q^5 by positivity)
  have h3 : 0 ≤ q^3 := by positivity
  have h5 : 0 ≤ q^5 := by positivity
  dsimp [OwnSouthWestDominant.chordSecond,OwnSouthWestDominant.chordSin,
    OwnSouthWestDominant.chordCos,polynomial]
  nlinarith only [hl,hu,hc,h7,hq0,h3,h5,sq_nonneg q,sq_nonneg (q^2)]

private lemma hasDeriv (q : ℝ) : HasDerivAt polynomial (first q) q := by
  convert ((((((hasDerivAt_id q).const_mul (-(567/1000))).const_add (19/100)).fun_add
    (((hasDerivAt_id q).fun_pow 2).const_mul (-(23/1000)))).fun_add
    (((hasDerivAt_id q).fun_pow 3).const_mul (149/1000))).fun_add
    (((hasDerivAt_id q).fun_pow 4).const_mul (1/2000))).fun_add
    (((hasDerivAt_id q).fun_pow 5).const_mul (-(3/400))) using 1
  · funext y; dsimp [polynomial]; ring
  · dsimp [first]; ring

private lemma first_hasDeriv (q : ℝ) : HasDerivAt first (second q) q := by
  convert (((((hasDerivAt_id q).const_mul (-(23/500))).const_add (-(567/1000))).fun_add
    (((hasDerivAt_id q).fun_pow 2).const_mul (447/1000))).fun_add
    (((hasDerivAt_id q).fun_pow 3).const_mul (1/500))).fun_add
    (((hasDerivAt_id q).fun_pow 4).const_mul (-(3/80))) using 1
  · funext y; dsimp [first]; ring
  · dsimp [second]; ring

private lemma second_nonnegative {q : ℝ} (hq : 157/200 ≤ q ∧ q ≤ 5/3) :
    0 ≤ second q := by
  have hq0 : 0 ≤ q := by linarith [hq.1]
  have hsq := mul_nonneg (sub_nonneg.mpr hq.2)
    (show 0 ≤ 5/3+q by linarith)
  have h3 := mul_nonneg (show 0 ≤ 25/9-q^2 by nlinarith only [hsq]) hq0
  dsimp [second]
  nlinarith only [h3,hq.1,sq_nonneg q]

private lemma polynomial_strict_upper {q : ℝ} (hq : 157/200 ≤ q ∧ q ≤ 5/3) :
    polynomial q < -(19/100) := by
  have hc : ConcaveOn ℝ (Set.Icc (157/200) (5/3)) (fun q => -19/100-polynomial q) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (157/200) (5/3))
      (f' := fun q => -first q) (f'' := fun q => -second q)
      (by dsimp [polynomial]; fun_prop)
    · intro q _
      exact ((hasDeriv q).const_sub (-19/100)).hasDerivWithinAt
    · intro q _
      exact (first_hasDeriv q).neg.hasDerivWithinAt
    · intro q hq
      have hq' : q ∈ Set.Icc (157/200:ℝ) (5/3) := interior_subset hq
      exact neg_nonpos.mpr (second_nonnegative hq')
  have h := positive_on_concave_interval hc hq
    (by norm_num [polynomial]) (by norm_num [polynomial])
  linarith

/-- The second derivative of the chord term is at most `-19/100` on
`[157/200, 5/3]`, for `L ≤ 27701483/8000000` and `M ≤ 75987/100000`. -/
theorem upper {L M q : ℝ}
    (hL : L ≤ 27701483/8000000) (hM : M ≤ 75987/100000)
    (hq : 157/200 ≤ q ∧ q ≤ 5/3) :
    -Real.sin q+(L/4)*Real.sin (q/2)+(M/4)*Real.cos (q/2) ≤ -(19/100) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1])
    (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hc := Real.cos_nonneg_of_mem_Icc
    (show q/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hq.1,hq.2,Real.pi_gt_d2])
  have hp := mul_nonneg (show 0 ≤ 27701483/8000000-L by linarith) hs
  have hr := mul_nonneg (show 0 ≤ 75987/100000-M by linarith) hc
  have hu := polynomial_upper hq
  have hn := polynomial_strict_upper hq
  dsimp [OwnSouthWestDominant.chordSecond,OwnSouthWestDominant.chordSin,
    OwnSouthWestDominant.chordCos] at hu
  nlinarith only [hp,hr,hu,hn]

end SquaresInCircles.Six.Analytic.HighChordCurvature
