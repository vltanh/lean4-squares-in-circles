import SquaresInCircles.Six.Analytic.FixedPairSlices
import SquaresInCircles.Six.Analytic.FixedPairTrig

/-!
# Nonzero forces and safe curvature interfaces

Every actual fixed-pair force has first coordinate greater than 1/2 on the
stated domain. Thus none of the square-root derivatives is evaluated at a zero
resultant. The bounds below are independent of a grid or numerical tolerance.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

lemma northSource_first_lower (u : Fin 4) (q : ℝ) : -1≤(pairNorthSource u q).1 := by
  fin_cases u <;> simp only [pairNorthSource]
  · linarith [Real.sin_le_one q]
  · exact Real.neg_one_le_cos q
  · norm_num
  · norm_num

lemma westSource_first_lower (u : Fin 4) (q : ℝ) : -1≤(pairWestSource u q).1 := by
  fin_cases u <;> simp only [pairWestSource]
  · norm_num
  · norm_num
  · linarith [Real.sin_le_one q]
  · exact Real.neg_one_le_cos q

lemma northForce_first_positive {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) : 1/2<(northForce no u n w).1 := by
  have hc := cos_lower_of_abs_le (domain_absolute hd).1
  have hb : 9/10≤(pairNorthBase no n).1 := by
    cases no <;> simp only [pairNorthBase,Bool.false_eq_true,if_false,if_true] <;> nlinarith
  have hs := mul_le_mul_of_nonneg_left (northSource_first_lower u (n-w)) rStar_pos.le
  dsimp [northForce]
  nlinarith [pair_multiplier_bounds]

lemma westForce_first_positive {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) : 1/2<(westForce wo u n w).1 := by
  have hc := cos_lower_of_abs_le (domain_absolute hd).2.1
  have hb : 9/10≤(pairWestBase wo w).1 := by
    cases wo <;> simp only [pairWestBase,Bool.false_eq_true,if_false,if_true] <;> nlinarith
  have hs := mul_le_mul_of_nonneg_left (westSource_first_lower u (n-w)) rStar_pos.le
  dsimp [westForce]
  nlinarith [pair_multiplier_bounds]

lemma northSq_positive {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) : 0<northSq no u n w := by
  rw [northSq_eq_norm]
  have hx := northForce_first_positive hd u
  have hy := sq_nonneg (northForce no u n w).2
  nlinarith

lemma westSq_positive {no wo : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (u : Fin 4) : 0<westSq wo u n w := by
  rw [westSq_eq_norm]
  have hx := westForce_first_positive hd u
  have hy := sq_nonneg (westForce wo u n w).2
  nlinarith

lemma northWave_positive {no wo : Bool} {n w x : ℝ} (u : Fin 4) (k : Fin 3)
    (hd : Domain no wo (sliceN k n w x) (sliceW k n w x)) :
    0<(northWave no u k n w).arg x := by
  rw [northWave_arg]
  exact northSq_positive hd u

lemma westWave_positive {no wo : Bool} {n w x : ℝ} (u : Fin 4) (k : Fin 3)
    (hd : Domain no wo (sliceN k n w x) (sliceW k n w x)) :
    0<(westWave wo u k n w).arg x := by
  rw [westWave_arg]
  exact westSq_positive hd u

lemma northRadius_nonneg (u : Fin 4) : 0≤northRadius u := by
  unfold northRadius
  split_ifs
  · exact Six.radius_pos.le
  · linarith [rhoStar_gt_11_10]

lemma northRadius_le_circle (u : Fin 4) : northRadius u≤Six.radius := by
  unfold northRadius
  split_ifs
  · exact le_rfl
  · nlinarith [rhoStar_identity,Six.radius_sq,Six.radius_pos,rhoStar_gt_11_10]

lemma Wave.base_nonneg {W : Wave} (hr : 0<W.rotor)
    (ha : W.cosine^2+W.sine^2=4*W.rotor^2*W.baseSq) : 0≤W.baseSq := by
  by_contra! hb
  have hh := mul_neg_of_pos_of_neg (show 0<4*W.rotor^2 by positivity) hb
  rw [← ha] at hh
  nlinarith [sq_nonneg W.cosine,sq_nonneg W.sine]

/-- A rational upper bound on the two vector lengths suffices for a uniform
curvature bound. The numerical comparison is an explicit scalar hypothesis,
proved by rational algebra at each of the few source cases below. -/
lemma Wave.curvature_le_rational {W : Wave} {x A B M : ℝ}
    (hr : 0<W.rotor)
    (ha : W.cosine^2+W.sine^2=4*W.rotor^2*W.baseSq)
    (hx : 0<W.arg x) (hA : W.rotor≤A) (hB : W.baseSq≤B^2) (hB0 : 0≤B)
    (hm : (1689/1000)*A*B/(A+B)≤M) : W.curvature Six.radius x≤M := by
  have hb := W.base_nonneg hr ha
  have hab : 0<W.rotor+Real.sqrt W.baseSq := by
    linarith [Real.sqrt_nonneg W.baseSq]
  have h := Wave.curvature_bound Six.radius_pos.le hr.le hb ha hx hA hB hB0 hab
  have hAB : 0<A+B := by linarith
  have hprod := mul_le_mul_of_nonneg_right candidate_radius_bounds.2.le
    (show 0≤A*B/(A+B) by positivity)
  have hstep : Six.radius*A*B/(A+B)≤(1689/1000)*A*B/(A+B) := by
    simpa only [mul_div_assoc,mul_assoc] using hprod
  exact h.trans (hstep.trans hm)

/-- The positive current radicand itself implies that an opposing base is at
least as long as the rotor. There is no extra unproved length ordering. -/
lemma Wave.curvature_nonpos_of_opposition {W : Wave} {R x : ℝ}
    (hR : 0≤R) (hr : 0<W.rotor)
    (ha : W.cosine^2+W.sine^2=4*W.rotor^2*W.baseSq)
    (hx : 0<W.arg x)
    (hop : W.cosine*Real.cos x+W.sine*Real.sin x≤-2*W.rotor^2) :
    W.curvature R x≤0 := by
  have hb := W.base_nonneg hr ha
  have hs := Real.sq_sqrt hb
  have hb0 := Real.sqrt_nonneg W.baseSq
  have horder : W.rotor≤Real.sqrt W.baseSq := by
    have harg := hx
    dsimp [Wave.arg,Wave.parameter,harmonicArg] at harg
    nlinarith
  apply harmonicCurvature_nonpos_of_opposition hR hr.le horder
  · dsimp [Wave.parameter]
    rw [hs]
  · rwa [hs]
  · exact hx
  · exact hop

end SquaresInCircles.Six.Analytic.FixedPair
