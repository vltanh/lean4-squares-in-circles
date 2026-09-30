import SquaresInCircles.Six.Analytic.FixedPairFormula

/-!
# Whole-domain trigonometric reserves for the fixed pair

The cardinal helper uses its full [-2/5,2/5] interval. Its nonnegative half
has the stronger reserve used with the whole-circle root bound; the negative
half is combined with the improved root curvature in FixedPairNegativeCardinal.
The split is the genuine sign wall w=0, not a searched numerical subdivision.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

lemma domain_absolute {no wo : Bool} {n w : ℝ} (h : Domain no wo n w) :
    |n|≤5/12 ∧ |w|≤11/25 ∧ |n-w|≤6/7 := by
  rcases domain_bounds h with ⟨hn0,hn1,hw0,hw1,hq0,hq1⟩
  refine ⟨abs_le.mpr ⟨?_,hn1⟩,abs_le.mpr ⟨hw0,?_⟩,abs_le.mpr ⟨?_,hq1⟩⟩ <;> linarith

lemma cos_lower_of_abs_le {x a : ℝ} (h : |x|≤a) : 1-a^2/2≤Real.cos x := by
  have hs := pow_le_pow_left₀ (abs_nonneg x) h 2
  rw [sq_abs] at hs
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]

lemma sin_lower_of_nonpos {x : ℝ} (h : x≤0) : x≤Real.sin x := by
  have hh := Real.sin_le (show 0≤-x by linarith)
  rw [Real.sin_neg] at hh
  linarith

lemma cos_add_abs_sin_ge_one {t : ℝ} (ht : |t|≤Real.pi/2) :
    1≤Real.cos t+|Real.sin t| := by
  have hc := Real.cos_nonneg_of_mem_Icc (abs_le.mp ht)
  simpa only [abs_of_nonneg hc] using one_le_abs_cos_add_abs_sin t

lemma cos_minus_positive_sin_nonneg {t : ℝ} (ht : |t|≤5/12) :
    0≤Real.cos t-max (Real.sin t) 0 := by
  have hs : |Real.sin t|≤|t| := by simpa using Real.abs_sin_sub_sin_le t 0
  have hc := cos_lower_of_abs_le ht
  have hsin := (le_abs_self (Real.sin t)).trans (hs.trans ht)
  rw [sub_nonneg]
  exact max_le (by nlinarith) (by nlinarith)

lemma northTrig_lower {no wo pn pw pq : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) : 1/2≤northTrig no u pn n := by
  have hnb := (domain_absolute hd).1
  have hsign := sign_sin hs.1 (by linarith [Real.pi_gt_d2] : |n|≤Real.pi)
  have hwidth := cos_add_abs_sin_ge_one (by linarith [Real.pi_gt_d2] : |n|≤Real.pi/2)
  have hcos := cos_lower_of_abs_le hnb
  have hpositive := cos_minus_positive_sin_nonneg hnb
  have hcorrection := mul_nonneg cStar_pos.le hpositive
  have hsn : 0≤(sign pn+1)*Real.sin n := by nlinarith [hsign.1,neg_le_abs (Real.sin n)]
  cases no
  · by_cases hu : u=0 ∨ u=3
    · simp only [northTrig,northCosCoeff,northSinCoeff,Bool.false_eq_true,if_false,if_pos hu]
      nlinarith
    · simp only [northTrig,northCosCoeff,northSinCoeff,Bool.false_eq_true,if_false,if_neg hu]
      nlinarith [hsign.1]
  · simp only [northTrig,northCosCoeff,northSinCoeff,if_true]
    nlinarith [hsign.1,hsign.2]

lemma northTrig_cardinal_candidate {wo pn pw pq : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain false wo n w) (hs : Sector pn pw pq n w) (hu : u=0 ∨ u=3) :
    97/100<northTrig false u pn n := by
  have hn : |n|≤203/1000 := abs_le.mpr hd.1
  have hc := cos_lower_of_abs_le hn
  have hsign := sign_sin hs.1 (by linarith [Real.pi_gt_d2] : |n|≤Real.pi)
  have hp : 0≤(sign pn+1)*Real.sin n := by nlinarith [hsign.1,neg_le_abs (Real.sin n)]
  simp only [northTrig,northCosCoeff,northSinCoeff,Bool.false_eq_true,if_false,if_pos hu]
  nlinarith

lemma westTrig_own_lower {no pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no true n w) (hs : Sector pn pw pq n w) : 1/2≤westTrig true pw w := by
  have hw : |w|≤11/25 := (domain_absolute hd).2.1
  have hsign := sign_sin hs.2.1 (by linarith [Real.pi_gt_d2] : |w|≤Real.pi)
  have hwidth := cos_add_abs_sin_ge_one (by linarith [Real.pi_gt_d2] : |w|≤Real.pi/2)
  cases pw
  · simp only [westTrig,westCosCoeff,westSinCoeff,if_true,sign,positivePart,Bool.false_eq_true,if_false]
    nlinarith [hsign.1]
  · have hw0 : 0≤w := hs.2.1
    have hw1 : w≤2/25 := hd.2.2
    have hw2 := mul_nonneg hw0 (sub_nonneg.mpr hw1)
    have hw3 : w^2≤4/625 := by nlinarith [sq_nonneg (w-2/25)]
    have hc := Real.one_sub_sq_div_two_le_cos (x := w)
    have hsin := Real.sin_ge_sub_cube hw0
    have hw4 := mul_nonneg hw0 (show 0≤4/625-w^2 by linarith)
    have hslo : (9/10)*w≤Real.sin w := by nlinarith
    have hcoef : 0≤1/2-cStar := by linarith [pair_coarse_constants]
    have hm := mul_le_mul_of_nonneg_left hslo hcoef
    have hcs := mul_nonneg (show 0≤113/1000-cStar by linarith [pair_coarse_constants]) hw0
    simp only [westTrig,westCosCoeff,westSinCoeff,if_true,sign,positivePart]
    nlinarith

/-- Uniform reserve on the entire cardinal interval. -/
lemma westTrig_cardinal_coarse {no pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no false n w) (hs : Sector pn pw pq n w) :
    23/25≤westTrig false pw w := by
  have hw : |w|≤2/5 := abs_le.mpr hd.2
  have hc := cos_lower_of_abs_le hw
  have hsign := sign_sin hs.2.1 (by linarith [Real.pi_gt_d2] : |w|≤Real.pi)
  have hpositive : 0≤(sign pw+1)*Real.sin w := by
    nlinarith [hsign.1,neg_le_abs (Real.sin w)]
  simp only [westTrig,westCosCoeff,westSinCoeff,Bool.false_eq_true,if_false]
  nlinarith

/-- The positive cardinal half has the stronger width reserve. -/
lemma westTrig_cardinal_lower {no pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no false n w) (hs : Sector pn pw pq n w) (hw0 : 0≤w) :
    493/500<westTrig false pw w := by
  have hw : |w|≤2/5 := abs_le.mpr hd.2
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hw0
    (by linarith [hd.2.2,Real.pi_gt_d2])
  have hsign := sign_sin hs.2.1 (by linarith [Real.pi_gt_d2] : |w|≤Real.pi)
  have hwidth := cos_add_abs_sin_ge_one (by linarith [Real.pi_gt_d2] : |w|≤Real.pi/2)
  rw [abs_of_nonneg hsin] at hsign hwidth
  simp only [westTrig,westCosCoeff,westSinCoeff,Bool.false_eq_true,if_false]
  nlinarith [hsign.1]

lemma differenceTrig_candidate {no wo pn pw pq : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) (hu : u=0 ∨ u=3) :
    11/50<differenceTrig u pq (n-w) := by
  have hb := (domain_absolute hd).2.2
  have hcos : 31/49≤Real.cos (n-w) := by nlinarith [cos_lower_of_abs_le hb]
  have hsin := sign_sin hs.2.2 (by linarith [Real.pi_gt_d2] : |n-w|≤Real.pi)
  have hnonneg : 0≤(sign pq-1)*Real.sin (n-w) := by
    nlinarith [hsin.1,le_abs_self (Real.sin (n-w))]
  have hm := mul_nonneg rStar_pos.le hnonneg
  have hc := mul_le_mul_of_nonneg_left hcos rStar_pos.le
  have he : u≠1 := by rcases hu with rfl | rfl <;> decide
  simp only [differenceTrig,differenceCosCoeff,differenceSinCoeff,if_pos hu,if_neg he]
  nlinarith [pair_coarse_constants]

lemma differenceTrig_candidate_negative {no wo pn pw pq : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w)
    (hu : u=0 ∨ u=3) (hq : n-w≤0) : rStar≤differenceTrig u pq (n-w) := by
  have hb := (domain_absolute hd).2.2
  have hsign := sign_sin hs.2.2 (by linarith [Real.pi_gt_d2] : |n-w|≤Real.pi)
  have hwidth := cos_add_abs_sin_ge_one (by linarith [Real.pi_gt_d2] : |n-w|≤Real.pi/2)
  have hsin : Real.sin (n-w)≤0 := by
    have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-(n-w) by linarith)
      (by have h := abs_le.mp hb; linarith [h.1,Real.pi_gt_d2])
    rw [Real.sin_neg] at hh
    linarith
  rw [abs_of_nonpos hsin] at hwidth hsign
  have hmul := mul_le_mul_of_nonneg_left hwidth rStar_pos.le
  have he : u≠1 := by rcases hu with rfl | rfl <;> decide
  simp only [differenceTrig,differenceCosCoeff,differenceSinCoeff,if_pos hu,if_neg he]
  nlinarith [hsign.1]

lemma differenceTrig_cardinal_west {no pn pw pq : Bool} {u : Fin 4} {n w : ℝ}
    (hd : Domain no false n w) (hs : Sector pn pw pq n w) (hu : u=0 ∨ u=3)
    (hw0 : 0≤w) : 61/200<differenceTrig u pq (n-w) := by
  by_cases hq : n-w≤0
  · have hh := differenceTrig_candidate_negative hd hs hu hq
    linarith [pair_coarse_constants]
  · have hq0 : 0≤n-w := (lt_of_not_ge hq).le
    have hn : n≤5/12 := (domain_bounds hd).2.1
    have hq1 : n-w≤7/12 := by linarith
    have hcos : 239/288≤Real.cos (n-w) := by
      have hb : |n-w|≤7/12 := by rwa [abs_of_nonneg hq0]
      nlinarith [cos_lower_of_abs_le hb]
    have hsign := sign_sin hs.2.2
      (by have hb := domain_absolute hd; linarith [hb.2.2,Real.pi_gt_d2] : |n-w|≤Real.pi)
    have hh : 0≤(sign pq-1)*Real.sin (n-w) := by
      nlinarith [hsign.1,le_abs_self (Real.sin (n-w))]
    have hm := mul_nonneg rStar_pos.le hh
    have hc := mul_le_mul_of_nonneg_left hcos rStar_pos.le
    have he : u≠1 := by rcases hu with rfl | rfl <;> decide
    simp only [differenceTrig,differenceCosCoeff,differenceSinCoeff,if_pos hu,if_neg he]
    nlinarith [pair_coarse_constants]

lemma differenceTrig_alternate_one {no wo pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) : 9/50<differenceTrig 1 pq (n-w) := by
  have hb := (domain_absolute hd).2.2
  have hsign := sign_sin hs.2.2 (by linarith [Real.pi_gt_d2] : |n-w|≤Real.pi)
  have hwidth := cos_add_abs_sin_ge_one (by linarith [Real.pi_gt_d2] : |n-w|≤Real.pi/2)
  have hm := mul_le_mul_of_nonneg_left hwidth rStar_pos.le
  norm_num [differenceTrig,differenceCosCoeff,differenceSinCoeff]
  nlinarith [hsign.1,pair_coarse_constants]

lemma differenceTrig_alternate_two {no wo pn pw pq : Bool} {n w : ℝ}
    (hd : Domain no wo n w) (hs : Sector pn pw pq n w) : 0≤differenceTrig 2 pq (n-w) := by
  have hb := (domain_absolute hd).2.2
  have hsign := sign_sin hs.2.2 (by linarith [Real.pi_gt_d2] : |n-w|≤Real.pi)
  have hh : 0≤(sign pq-1)*Real.sin (n-w) := by
    nlinarith [hsign.1,le_abs_self (Real.sin (n-w))]
  have hm := mul_nonneg rStar_pos.le hh
  norm_num [differenceTrig,differenceCosCoeff,differenceSinCoeff]
  nlinarith

end SquaresInCircles.Six.Analytic.FixedPair
