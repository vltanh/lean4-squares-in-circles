import SquaresInCircles.Six.Analytic.CoupledOwnProfiles

/-!
# The radial sum of D and S on their own axes

Let D and S have the local centres `(a, b)` and `(A, B)`. If they are separated
from C along their own axes, at angles `1/2 ≤ d ≤ s ≤ 2/3`, then
`a + A > 217/100 + (s - d)/3`: multiplying the two separating inequalities by
`sin s` and `cos d` and adding them cancels the first coordinate of the centre
of C. Containment in the disk gives `3a + |b| < 167/50` for each square, by
Cauchy–Schwarz. With `r = s - d`, together they make the separations of D and S
along their second axes, `A cos r - B sin r - b` and `B + a cos r + b sin r`, sum
to more than twice their threshold `(1 + cos r + sin r)/2`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma chart_three_radial_support {a b : ℝ} (hc : ContainedChart a |b|) :
    3*a+|b|<167/50 := by
  have hsq := sq_nonneg ((a+1/2)-3*(|b|+1/2))
  have hC := hc.containment
  have hpos : 0≤3*(a+1/2)+(|b|+1/2) := by linarith [hc.half_le,abs_nonneg b]
  have hbound : (3*(a+1/2)+(|b|+1/2))^2≤10*Q0 := by nlinarith only [hC,hsq]
  by_contra! h
  have hp := mul_nonneg
    (show 0≤3*(a+1/2)+(|b|+1/2)-267/50 by linarith)
    (show 0≤3*(a+1/2)+(|b|+1/2)+267/50 by linarith)
  norm_num [Q0] at hbound
  nlinarith

lemma coupled_own_radial_sum {a b A B cx cy d s : ℝ}
    (hS : ContainedChart A |B|)
    (hy : cy≤c0) (hd : 1/2≤d) (hds : d≤ s) (hs : s≤2/3)
    (hCD : 0≤centralMargin .own (Real.pi+d) a b cx cy)
    (hCS : 0≤centralMargin .own (3*Real.pi/2+s) A B cx cy) :
    217/100+(s-d)/3<a+A := by
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd,hds,hs,Real.pi_gt_d2])
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤d by linarith) (by linarith [Real.pi_gt_d2])
  have hcs := Real.cos_nonneg_of_mem_Icc
    (show s∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd,hds,hs,Real.pi_gt_d2])
  have hss := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤s by linarith) (by linarith [Real.pi_gt_d2])
  have hcr := Real.cos_nonneg_of_mem_Icc
    (show s-d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd,hds,hs,Real.pi_gt_d2])
  have hDgap : 0≤a-1/2-(1/2-cx)*Real.cos d-(1/2-cy)*Real.sin d := by
    have e1 : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
    have e2 : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
    simp only [centralMargin,centralNormal,angularWidth,e1,e2,
      abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hCD
    nlinarith only [hCD]
  have hSgap : 0≤A-1/2-(1/2-cy)*Real.cos s-(1/2+cx)*Real.sin s := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,neg_neg,add_zero,abs_neg,
      abs_of_nonneg hcs,abs_of_nonneg hss] at hCS
    nlinarith only [hCS]
  have hDp := mul_nonneg hDgap hss
  have hSp := mul_nonneg hSgap hcd
  have hcy : 387/1000≤1/2-cy := by dsimp [c0] at hy; linarith [rho0_upper]
  have hcyprod := mul_nonneg (sub_nonneg.mpr hcy) hcr
  rw [Real.cos_sub] at hcyprod
  have hcombined : (Real.cos d+Real.sin s)/2+Real.sin s*Real.cos d+
      (387/1000)*Real.cos (s-d)≤a*Real.sin s+A*Real.cos d := by
    rw [Real.cos_sub]
    linarith only [hDp,hSp,hcyprod]
  have hcoslower : 7/9≤Real.cos d := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := d)
    nlinarith only [hc,mul_nonneg (show 0≤2/3-d by linarith) (show 0≤2/3+d by linarith)]
  have hsinupper := Real.sin_le (show 0≤ s by linarith)
  have hdiff : 0≤Real.cos d-Real.sin s := by linarith
  have hAupper : A≤1113/1000 := hS.a_le_rho0.trans rho0_upper.le
  have hAp := mul_le_mul_of_nonneg_right hAupper hdiff
  have hreserve := coupled_own_reserve_positive hd hds hs
  by_contra! hsum
  have hsumprod := mul_le_mul_of_nonneg_right hsum hss
  dsimp [coupledOwnReserve] at hreserve
  nlinarith only [hcombined,hAp,hsumprod,hreserve]

/-- For `r ∈ [0, 1/6]` and `a + A > 217/100 + r/3`, the separations of D and S
along their second axes sum to more than twice their threshold. -/
lemma overtaking_secondary_sum {a b A B r : ℝ}
    (hD : ContainedChart a |b|) (hS : ContainedChart A |B|)
    (hr : 0≤r ∧ r≤1/6) (hsum : 217/100+r/3<a+A) :
    1+Real.cos r+Real.sin r<
      (A*Real.cos r-B*Real.sin r-b)+(B+a*Real.cos r+b*Real.sin r) := by
  let T := a+A
  let U := |b|+|B|
  let delta := T-U-2
  have hTlo : 217/100<T := by dsimp [T]; linarith [hr.1]
  have hThi : T≤2226/1000 := by
    dsimp [T]
    linarith [hD.a_le_rho0,hS.a_le_rho0,rho0_upper]
  have hdelta : (4/3)*r<delta := by
    have h1 := chart_three_radial_support hD
    have h2 := chart_three_radial_support hS
    dsimp [delta,T,U]
    linarith
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hs1 := Real.sin_le hr.1
  have hc1 := Real.cos_le_one r
  have hcp := mul_nonneg (sub_nonneg.mpr hThi) (sub_nonneg.mpr hc1)
  have hcLower := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := r))
    (by norm_num : (0:ℝ)≤1226/1000)
  have hsp := mul_nonneg (show 0≤T-217/100 by linarith) hs0
  have hdp := mul_pos (sub_pos.mpr hdelta) (show 0<1-Real.sin r by linarith [hr.2])
  have hrem := mul_nonneg hr.1 (sub_nonneg.mpr hs1)
  have hdiff : -U≤B-b := by
    dsimp [U]
    linarith [neg_le_abs B,le_abs_self b]
  have hdiffprod := mul_nonneg (sub_nonneg.mpr hdiff)
    (show 0≤1-Real.sin r by linarith [hr.2])
  have hpolynomial := mul_nonneg hr.1
    (show 0≤151/300-(5839/3000)*r by linarith [hr.2])
  have he :
      T*Real.cos r-U*(1-Real.sin r)-(1+Real.cos r+Real.sin r)=
      (T-1)*(Real.cos r-1)+(T-3)*Real.sin r+delta*(1-Real.sin r) := by
    dsimp [delta]
    ring
  have hstrict : 0<T*Real.cos r-U*(1-Real.sin r)-(1+Real.cos r+Real.sin r) := by
    nlinarith only [hcp,hcLower,hsp,hdp,hrem,hpolynomial,he,hs1]
  dsimp [T] at hstrict
  nlinarith only [hstrict,hdiffprod]

end SquaresInCircles.Six.Analytic
