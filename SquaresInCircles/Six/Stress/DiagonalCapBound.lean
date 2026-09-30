import SquaresInCircles.Six.Stress.DiagonalFormula
import SquaresInCircles.Six.Analytic.CandidateBounds

/-!
# Analytic cap-branch closure of the common diagonal bound

The cap expression has reserve (|w|+|s|)/40 throughout the helper rectangle.
The coefficient bounds 139/100 < sqrt(2)m rho < 141/100 now come directly from
candidate algebra in Analytic.CandidateBounds, not a constant certificate.
Only elementary sine/cosine estimates and explicit nonnegative products are
used. The exact support formula determines when this expression is active.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

lemma twice_beta_abs_le (w s : ℝ) : 2*|diagonalBeta w s|≤|w|+|s| := by
  have h := abs_sub_le w s
  have he : w-s=2*diagonalBeta w s := by dsimp [diagonalBeta]; ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h
  exact h

lemma pairBase_eq_diagonal_scale : 2*pairBase=diagonalK*(rhoStar-1) := by
  have h := pairBase_diagonal_identity
  dsimp [diagonalK]
  nlinarith only [h]

/-- Whole-domain cap-expression bound. It is used as the actual support only
where the separately proved cap/vertex condition selects it. -/
theorem diagonal_cap_remainder_lower {w s d : ℝ} (hdom : DiagonalDomain w s d) :
    (|w|+|s|)/40 ≤ pairLine w+pairLine (-s)+diagonalCap w s d+2*pairBase := by
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  let Z := |w|+|s|
  let T := diagonalK*rhoStar
  let P := diagonalK*(rhoStar-1)*(1-Real.cos b*Real.cos z)
  have hparams := diagonal_parameters hdom
  have hsign := diagonal_trig_signs hdom
  have hT : (139:ℝ)/100<T ∧ T<(141:ℝ)/100 := by
    simpa [T,diagonalK] using Analytic.diagonal_constant_bounds
  have hT0 : 0≤T := by linarith [hT.1]
  have hcd0 : 0≤Real.cos z := hsign.2.1.le
  have hcd1 := Real.cos_le_one z
  have hcc : Real.cos b*Real.cos z≤1 := by
    have hh := mul_le_mul (Real.cos_le_one b) hcd1 hcd0 (by norm_num : (0:ℝ)≤1)
    simpa using hh
  have hP : 0≤P := mul_nonneg
    (mul_nonneg diagonalK_pos.le (by linarith [rhoStar_gt_11_10])) (sub_nonneg.mpr hcc)
  have hZ0 : 0≤Z := add_nonneg (abs_nonneg w) (abs_nonneg s)
  have hZb : 2*|b|≤Z := twice_beta_abs_le w s
  have hid : pairLine w+pairLine (-s)+diagonalCap w s d+2*pairBase=
      (47/200)*Z-(99/100)*b+T*Real.sin b*Real.cos z+P := by
    rw [pairLine_sum,pairBase_eq_diagonal_scale]
    dsimp [diagonalCap,P,T,Z,b,z,diagonalBeta]
    ring
  rw [hid]
  change Z/40≤(47/200)*Z-(99/100)*b+T*Real.sin b*Real.cos z+P
  by_cases hb : b≤0
  · have hblo : -11/25≤b := hparams.1.1
    have hsin0 : Real.sin b≤0 := by
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-b by linarith)
        (show -b≤Real.pi by linarith [Real.pi_gt_d2])
      rw [Real.sin_neg] at hh
      linarith
    have hsinlo : b≤Real.sin b := by
      have hh := Real.sin_le (show 0≤-b by linarith)
      rw [Real.sin_neg] at hh
      linarith
    have hp := mul_nonneg (show 0≤-Real.sin b by linarith) (sub_nonneg.mpr hcd1)
    have hprod : b≤Real.sin b*Real.cos z := by nlinarith only [hp,hsinlo]
    have hm := mul_le_mul_of_nonneg_left hprod hT0
    have hcoef := mul_le_mul_of_nonpos_right hT.2.le hb
    rw [abs_of_nonpos hb] at hZb
    nlinarith only [hm,hcoef,hZb,hP]
  · have hb0 : 0≤b := (lt_of_not_ge hb).le
    have hb1 : b≤2/5 := hparams.1.2
    have hbsq : b^2≤4/25 := by
      have hh := mul_nonneg (sub_nonneg.mpr hb1) (show 0≤2/5+b by linarith)
      nlinarith only [hh]
    have hzsq : z^2≤5041/10000 := by
      have hh := pow_le_pow_left₀ (abs_nonneg z) hparams.2.1 2
      rw [sq_abs] at hh
      norm_num at hh
      exact hh
    let q := b^2/6+z^2/2
    have hq0 : 0≤q := by dsimp [q]; positivity
    have hq1 : q≤16723/60000 := by dsimp [q]; linarith
    have hTq := mul_le_mul hT.2.le hq1 hq0 (by norm_num : (0:ℝ)≤141/100)
    have hcoef : 0≤T-99/100-T*q := by linarith [hT.1]
    have hsinlo := Real.sin_ge_sub_cube hb0
    have hsinhi := Real.sin_le hb0
    have hcoslo := Real.one_sub_sq_div_two_le_cos (x := z)
    have hfirst := mul_nonneg (sub_nonneg.mpr hsinhi) (sub_nonneg.mpr hcd1)
    have hsecond := mul_nonneg hb0 (show 0≤Real.cos z-(1-z^2/2) by linarith)
    have hsinprod : b*(1-q)≤Real.sin b*Real.cos z := by
      dsimp [q]
      nlinarith only [hfirst,hsecond,hsinlo]
    have hmul := mul_le_mul_of_nonneg_left hsinprod hT0
    have hreserve := mul_nonneg hb0 hcoef
    nlinarith only [hmul,hreserve,hP,hZ0]

lemma diagonal_cap_zero_helpers (d : ℝ) :
    pairLine 0+pairLine (-0)+diagonalCap 0 0 d+2*pairBase=
      diagonalK*(rhoStar-1)*(1-Real.cos (d-Real.pi/4)) := by
  rw [pairBase_eq_diagonal_scale]
  simp only [pairLine_zero,neg_zero,diagonalCap,diagonalBeta,diagonalDelta,
    zero_sub,zero_add,sub_zero,zero_div,Real.cos_zero,Real.sin_zero,mul_zero,add_zero]
  ring

/-- The only zero of the cap remainder has exactly the candidate angles. -/
theorem diagonal_cap_zero_iff {w s d : ℝ} (hdom : DiagonalDomain w s d)
    (heq : pairLine w+pairLine (-s)+diagonalCap w s d+2*pairBase=0) :
    w=0 ∧ s=0 ∧ d=Real.pi/4 := by
  have hlow := diagonal_cap_remainder_lower hdom
  rw [heq] at hlow
  have hw : w=0 := abs_eq_zero.mp (by nlinarith [abs_nonneg w,abs_nonneg s])
  have hs : s=0 := abs_eq_zero.mp (by nlinarith [abs_nonneg w,abs_nonneg s])
  subst w
  subst s
  rw [diagonal_cap_zero_helpers] at heq
  have hcoef : 0<diagonalK*(rhoStar-1) := mul_pos diagonalK_pos (by linarith [rhoStar_gt_11_10])
  have hcos : Real.cos (d-Real.pi/4)=1 := by
    have hh := (mul_eq_zero.mp heq).resolve_left (ne_of_gt hcoef)
    linarith
  have hdelta := (diagonal_parameters hdom).2.1
  have hbound : |d-Real.pi/4|≤Real.pi := by
    simpa only [diagonalDelta,zero_add,zero_div,sub_zero] using
      hdelta.trans (by linarith [Real.pi_gt_d2] : (71:ℝ)/100≤Real.pi)
  have hpoly := cos_le_one_sub_fifth_sq hbound
  rw [hcos] at hpoly
  have hz : d-Real.pi/4=0 := by nlinarith [sq_nonneg (d-Real.pi/4)]
  exact ⟨rfl,rfl,sub_eq_zero.mp hz⟩

end SquaresInCircles.Six.Stress
