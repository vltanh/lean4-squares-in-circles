import SquaresInCircles.Six.Analytic.FixedPairPolynomial

/-!
# Whole-domain error control for the endpoint polynomial

The displayed bounds apply on the full pair domain. They come from the proved
Taylor remainders and candidate constants, followed by triangle inequalities.
They are not a collection of sampled or interval-certified endpoint values.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair.Polynomial
open Stress Normalization PairTaylor

private lemma r_product_error {x y B : ℝ}
    (hx : |x|≤B) (he : |x-y|≤1/100000) :
    |rStar*x-rApprox*y|≤B/10000000+37/10000000 := by
  have hp := product_difference rStar rApprox x y
  have h1 := mul_le_mul constants_close.1 hx (abs_nonneg x)
    (by norm_num : (0:ℝ)≤1/10000000)
  have h2 := mul_le_mul (show |rApprox|≤(37:ℝ)/100 by norm_num [rApprox]) he
    (abs_nonneg (x-y)) (by norm_num : (0:ℝ)≤37/100)
  nlinarith

private lemma base_error (own : Bool) {t : ℝ} (ht : |t|≤6/7) :
    |(pairNorthBase own t).1-(baseVector own t).1|≤1/100000 ∧
    |(pairNorthBase own t).2-(baseVector own t).2|≤1/100000 := by
  have hc := cos_error ht
  have hs := sin_error_coarse ht
  cases own
  · constructor
    · exact hc
    · simpa only [pairNorthBase,baseVector,if_false,neg_sub_neg,abs_sub_comm] using hs
  · norm_num [pairNorthBase,baseVector]

private lemma north_source_bounds (u : Fin 4) (q : ℝ) :
    |(pairNorthSource u q).1|≤1 ∧ |(pairNorthSource u q).2|≤1 := by
  have hs : |Real.sin q|≤1 := abs_le.mpr ⟨Real.neg_one_le_sin q,Real.sin_le_one q⟩
  have hc : |Real.cos q|≤1 := abs_le.mpr ⟨Real.neg_one_le_cos q,Real.cos_le_one q⟩
  fin_cases u <;> dsimp [pairNorthSource] <;> constructor
  all_goals first | simpa only [abs_neg] using hs | simpa only [abs_neg] using hc | norm_num

private lemma west_source_bounds (u : Fin 4) (q : ℝ) :
    |(pairWestSource u q).1|≤1 ∧ |(pairWestSource u q).2|≤1 := by
  have hs : |Real.sin q|≤1 := abs_le.mpr ⟨Real.neg_one_le_sin q,Real.sin_le_one q⟩
  have hc : |Real.cos q|≤1 := abs_le.mpr ⟨Real.neg_one_le_cos q,Real.cos_le_one q⟩
  fin_cases u <;> dsimp [pairWestSource] <;> constructor
  all_goals first | simpa only [abs_neg] using hs | simpa only [abs_neg] using hc | norm_num

private lemma north_source_error (u : Fin 4) {q : ℝ} (hq : |q|≤6/7) :
    |(pairNorthSource u q).1-(northSource u q).1|≤1/100000 ∧
    |(pairNorthSource u q).2-(northSource u q).2|≤1/100000 := by
  have hc := cos_error hq
  have hs := sin_error_coarse hq
  fin_cases u <;> dsimp [pairNorthSource,northSource] <;> constructor
  all_goals first
    | exact hs
    | exact hc
    | simpa only [neg_sub_neg,abs_sub_comm] using hs
    | simpa only [neg_sub_neg,abs_sub_comm] using hc
    | norm_num

private lemma west_source_error (u : Fin 4) {q : ℝ} (hq : |q|≤6/7) :
    |(pairWestSource u q).1-(westSource u q).1|≤1/100000 ∧
    |(pairWestSource u q).2-(westSource u q).2|≤1/100000 := by
  have hc := cos_error hq
  have hs := sin_error_coarse hq
  fin_cases u <;> dsimp [pairWestSource,westSource] <;> constructor
  all_goals first
    | exact hs
    | exact hc
    | simpa only [neg_sub_neg,abs_sub_comm] using hs
    | simpa only [neg_sub_neg,abs_sub_comm] using hc
    | norm_num

lemma north_vector_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) (u : Fin 4) :
    |(northForce no u n w).1-(northVector no u n w).1|≤7/500000 ∧
    |(northForce no u n w).2-(northVector no u n w).2|≤7/500000 := by
  have hb := domain_absolute hd
  have hbase := base_error no (show |n|≤6/7 by linarith [hb.1])
  have hsrc := north_source_error u hb.2.2
  have hbounded := north_source_bounds u (n-w)
  have hp1 := r_product_error hbounded.1 hsrc.1
  have hp2 := r_product_error hbounded.2 hsrc.2
  have h1 := sum_difference hbase.1 hp1
  have h2 := sum_difference hbase.2 hp2
  constructor
  · exact h1.trans (by norm_num)
  · exact h2.trans (by norm_num)

lemma west_vector_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) (u : Fin 4) :
    |(westForce wo u n w).1-(westVector wo u n w).1|≤3/200000 ∧
    |(westForce wo u n w).2-(westVector wo u n w).2|≤3/200000 := by
  have hb := domain_absolute hd
  have hbase := base_error wo (show |w|≤6/7 by linarith [hb.2.1])
  change |(pairWestBase wo w).1-(baseVector wo w).1|≤1/100000 ∧
    |(pairWestBase wo w).2-(baseVector wo w).2|≤1/100000 at hbase
  have hsrc := west_source_error u hb.2.2
  have hbounded := west_source_bounds u (n-w)
  have hp1 := r_product_error hbounded.1 hsrc.1
  have hp2 := r_product_error hbounded.2 hsrc.2
  have h1 := sum_difference hbase.1 hp1
  have h2 := sub_difference (sum_difference hbase.2 hp2) constants_close.2.1
  constructor
  · exact h1.trans (by norm_num)
  · exact h2.trans (by norm_num)

lemma halfWidth_error {t : ℝ} (ht : |t|≤6/7) :
    |(1/2+angularWidth t)-halfWidth t|≤1/100000 := by
  have hc := abs_le.mp ((absolute_lipschitz (Real.cos t) (cosP t)).trans (cos_error ht))
  have hs := abs_le.mp ((absolute_lipschitz (Real.sin t) (sinP t)).trans (sin_error_coarse ht))
  apply abs_le.mpr
  dsimp [angularWidth,halfWidth]
  constructor <;> linarith [hc.1,hc.2,hs.1,hs.2]

private lemma halfWidth_abs_bound (t : ℝ) : |1/2+angularWidth t|≤3/2 := by
  have hs : |Real.sin t|≤1 := abs_le.mpr ⟨Real.neg_one_le_sin t,Real.sin_le_one t⟩
  have hc : |Real.cos t|≤1 := abs_le.mpr ⟨Real.neg_one_le_cos t,Real.cos_le_one t⟩
  have hn : 0≤1/2+angularWidth t := by dsimp [angularWidth]; positivity
  rw [abs_of_nonneg hn]
  dsimp [angularWidth]
  linarith

lemma threshold_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    |threshold n w-thresholdP n w|≤1/40000 := by
  have hb := domain_absolute hd
  have hn := halfWidth_error (show |n|≤6/7 by linarith [hb.1])
  have hw := halfWidth_error (show |w|≤6/7 by linarith [hb.2.1])
  have hq := r_product_error (halfWidth_abs_bound (n-w)) (halfWidth_error hb.2.2)
  have hm : |mStar/2-mApprox/2|≤3/20000000 := by
    have hh := abs_le.mp constants_close.2.1
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2]
  have hh := sum_difference (sum_difference (sum_difference hn hw) hq) hm
  exact hh.trans (by norm_num)

private def penaltyFactor (no wo : Bool) (n w : ℝ) : ℝ :=
  (if no then max (Real.sin n) 0+1-Real.cos n else 0)+
    (if wo then max (Real.sin w) 0 else 0)

private def penaltyFactorP (no wo : Bool) (n w : ℝ) : ℝ :=
  (if no then max (sinP n) 0+1-cosP n else 0)+
    (if wo then max (sinP w) 0 else 0)

private lemma penaltyFactor_bound (no wo : Bool) (n w : ℝ) : |penaltyFactor no wo n w|≤4 := by
  have hn0 : 0≤max (Real.sin n) 0 := le_max_right _ _
  have hw0 : 0≤max (Real.sin w) 0 := le_max_right _ _
  have hn1 : max (Real.sin n) 0≤1 := max_le (Real.sin_le_one n) (by norm_num)
  have hw1 : max (Real.sin w) 0≤1 := max_le (Real.sin_le_one w) (by norm_num)
  have hc0 := Real.neg_one_le_cos n
  have hc1 := Real.cos_le_one n
  cases no <;> cases wo <;> dsimp [penaltyFactor] <;> apply abs_le.mpr
  all_goals constructor <;> linarith

private lemma penaltyFactor_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    |penaltyFactor no wo n w-penaltyFactorP no wo n w|≤3/100000 := by
  have hb := domain_absolute hd
  have hn := (positivePart_lipschitz (Real.sin n) (sinP n)).trans
    (sin_error_coarse (show |n|≤6/7 by linarith [hb.1]))
  have hw := (positivePart_lipschitz (Real.sin w) (sinP w)).trans
    (sin_error_coarse (show |w|≤6/7 by linarith [hb.2.1]))
  have hc := cos_error (show |n|≤6/7 by linarith [hb.1])
  have hnb := abs_le.mp hn
  have hwb := abs_le.mp hw
  have hcb := abs_le.mp hc
  cases no <;> cases wo <;> dsimp [penaltyFactor,penaltyFactorP] <;> apply abs_le.mpr
  all_goals constructor <;> linarith [hnb.1,hnb.2,hwb.1,hwb.2,hcb.1,hcb.2]

lemma penalty_error {no wo : Bool} {n w : ℝ} (hd : Domain no wo n w) :
    |penalty no wo n w-penaltyP no wo n w|≤1/200000 := by
  have hid : penalty no wo n w=cStar*penaltyFactor no wo n w := by
    cases no <;> cases wo <;> dsimp [penalty,penaltyFactor] <;> ring
  have hidP : penaltyP no wo n w=cApprox*penaltyFactorP no wo n w := by
    cases no <;> cases wo <;> dsimp [penaltyP,penaltyFactorP] <;> ring
  rw [hid,hidP]
  have hp := product_difference cStar cApprox (penaltyFactor no wo n w) (penaltyFactorP no wo n w)
  have h1 := mul_le_mul constants_close.2.2 (penaltyFactor_bound no wo n w)
    (abs_nonneg _) (by norm_num : (0:ℝ)≤2/10000000)
  have h2 := mul_le_mul (show |cApprox|≤113/1000 by norm_num [cApprox])
    (penaltyFactor_error hd) (abs_nonneg _) (by norm_num : (0:ℝ)≤113/1000)
  nlinarith

end SquaresInCircles.Six.Analytic.FixedPair.Polynomial
