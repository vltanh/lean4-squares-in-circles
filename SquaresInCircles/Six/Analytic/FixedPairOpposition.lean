import SquaresInCircles.Six.Analytic.FixedPairRadicands

/-!
# The west force for an edge along the primary axis of N

When the edge N–W is along the primary axis of N (source `2`), the west force
along the slice in `n` is a fixed vector plus `rStar` times a turning unit
vector that points against it: `rStar ≤ sin (n - w) + mStar cos (n - w)` if W is
separated from C along its own axis, and `rStar ≤ sin n + mStar cos (n - w)`
otherwise. So the west term of the minorant is concave in `n`. Both inequalities
follow from `mStar > 889/1000` and second-order bounds for the cosine, on each
side of `n - w = 0` or of `n = 0`.
-/
noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

lemma own_west_opposition {no : Bool} {n w : ℝ} (hd : Domain no true n w) :
    rStar≤Real.sin (n-w)+mStar*Real.cos (n-w) := by
  have hb := domain_absolute hd
  have hc0 := (domain_cos_pos hd).2.2.le
  have hm0 := mStar_pos.le
  by_cases hq : n-w≤0
  · have hn := (domain_bounds hd).1
    have hw := hd.2.2
    have hsmall : |n-w|≤19/50 := by
      rw [abs_of_nonpos hq]
      linarith
    have hc := cos_lower_of_abs_le hsmall
    have hs := sin_lower_of_nonpos hq
    have hp := mul_le_mul
      (show (889:ℝ)/1000≤ mStar by linarith [pair_multiplier_bounds]) hc
      (by norm_num : (0:ℝ)≤1-(19/50)^2/2) hm0
    nlinarith [pair_multiplier_bounds]
  · have hq0 : 0≤n-w := (lt_of_not_ge hq).le
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hq0
      (by linarith [(abs_le.mp hb.2.2).2,Real.pi_gt_d2])
    have hc := cos_lower_of_abs_le hb.2.2
    have hp := mul_le_mul
      (show (889:ℝ)/1000≤ mStar by linarith [pair_multiplier_bounds]) hc
      (by norm_num : (0:ℝ)≤1-(6/7)^2/2) hm0
    nlinarith [pair_multiplier_bounds]

lemma cardinal_west_opposition {no : Bool} {n w : ℝ} (hd : Domain no false n w) :
    rStar≤Real.sin n+mStar*Real.cos (n-w) := by
  have hb := domain_absolute hd
  have hm0 := mStar_pos.le
  by_cases hn : n≤0
  · have hbounds := domain_bounds hd
    have hq : |n-w|≤7/10 := by
      apply abs_le.mpr
      constructor <;> linarith [hbounds.2.2.2.2.1,hd.2.1]
    have hc := cos_lower_of_abs_le hq
    have hs := sin_lower_of_nonpos hn
    have hp := mul_le_mul
      (show (889:ℝ)/1000≤ mStar by linarith [pair_multiplier_bounds]) hc
      (by norm_num : (0:ℝ)≤1-(7/10)^2/2) hm0
    nlinarith [pair_multiplier_bounds,hbounds.1]
  · have hn0 : 0≤n := (lt_of_not_ge hn).le
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hn0
      (by linarith [(abs_le.mp hb.1).2,Real.pi_gt_d2])
    have hc := cos_lower_of_abs_le hb.2.2
    have hp := mul_le_mul
      (show (889:ℝ)/1000≤ mStar by linarith [pair_multiplier_bounds]) hc
      (by norm_num : (0:ℝ)≤1-(6/7)^2/2) hm0
    nlinarith [pair_multiplier_bounds]

lemma westWave_alternate_two_wave (wo : Bool) (n w : ℝ) :
    (westWave wo 2 0 n w).cosine*Real.cos n+
      (westWave wo 2 0 n w).sine*Real.sin n =
      -2*rStar*((if wo then Real.sin (n-w) else Real.sin n)+mStar*Real.cos (n-w)) := by
  cases wo <;> simp only [westWave,Bool.false_eq_true,ite_false,ite_true,Matrix.cons_val,
    Real.cos_sub,Real.sin_sub]
  all_goals ring

/-- For source `2`, the west term has nonpositive curvature along the slice in
`n`. -/
theorem west_alternate_two_curvature_nonpos {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) :
    (westWave wo 2 0 n w).curvature Six.radius n≤0 := by
  have hr : 0<(westWave wo 2 0 n w).rotor := by
    cases wo <;> simpa [westWave] using rStar_pos
  have hx : 0<(westWave wo 2 0 n w).arg n := by
    apply westWave_positive (no := no) 2 0
    simpa only [sliceN,sliceW,ite_true,ite_self] using hd
  apply Wave.curvature_nonpos_of_opposition Six.radius_pos.le hr
    (westWave_amplitude wo 2 0 n w) hx
  rw [westWave_alternate_two_wave]
  have hp : rStar≤(if wo then Real.sin (n-w) else Real.sin n)+mStar*Real.cos (n-w) := by
    cases wo
    · exact cardinal_west_opposition hd
    · exact own_west_opposition hd
  have hmul := mul_nonneg (show 0≤2*rStar by linarith [rStar_pos]) (sub_nonneg.mpr hp)
  have hrot : (westWave wo 2 0 n w).rotor=rStar := by cases wo <;> rfl
  rw [hrot]
  nlinarith

end SquaresInCircles.Six.Analytic.FixedPair
