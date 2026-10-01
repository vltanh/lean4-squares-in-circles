import SquaresInCircles.Six.Analytic.WestStressMinorant
import SquaresInCircles.Six.Normalization.CapBounds

/-!
# The W-secondary west-cardinal stress and the two exact source expressions

The multipliers are fixed at (3/10,9/20,1/4). A single affine upper bound for
sqrt(61/400-(3/20)z) follows from an explicitly completed square and proves
W-secondary positivity by WestStressMinorant. For D-secondary the W-force
norm has the PLUS mixed term 53/200+(9/40)sin(u-t). It is not dominated by
W-secondary; its separate analytic curvature proof is in WestStressDConcavity.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def westCentralSupport (t:ℝ) : ℝ :=
  c0*(3/10+(9/20)*Real.cos t+(9/20)*max (Real.sin t) 0)

def westStressW (t u:ℝ) : ℝ :=
  17/20+(3/10)*Real.cos u+(3/10)*max (-Real.sin u) 0+
    (9/40)*(Real.cos t+|Real.sin t|)+(1/4)*(Real.cos (u-t)+Real.sin (u-t))-
    westCentralSupport t-R0*Real.sqrt (53/200)-R0*Real.sqrt (61/400-(3/20)*Real.sin t)

def westStressD (t u:ℝ) : ℝ :=
  17/20+(3/10)*Real.cos u+(3/10)*max (-Real.sin u) 0+
    (9/40)*(Real.cos t+|Real.sin t|)+(1/4)*(Real.cos (u-t)+Real.sin (u-t))-
    westCentralSupport t-R0*Real.sqrt (53/200+(9/40)*Real.sin (u-t))-
    R0*Real.sqrt (61/400-(3/20)*Real.sin u)

lemma west_radius_bound : R0<8443/5000 := by
  have h := Real.sqrt_lt_sqrt Q0_pos.le
    (show Q0<((8443:ℝ)/5000)^2 by norm_num [Q0])
  rw [Real.sqrt_sq (by norm_num)] at h
  exact h

lemma west_root_bound : Real.sqrt (53/200:ℝ)≤103/200 := by
  have h := Real.sqrt_le_sqrt (show (53:ℝ)/200≤((103:ℝ)/200)^2 by norm_num)
  rwa [Real.sqrt_sq (by norm_num)] at h

lemma west_angle_bounds {t:ℝ} (ht:-2/3≤t ∧ t≤2/5) :
    7/9≤Real.cos t ∧ -2/3≤Real.sin t ∧ Real.sin t≤2/5 := by
  have hsinU := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤t by linarith [ht.1,Real.pi_gt_d2])
    (show (2:ℝ)/5≤Real.pi/2 by linarith [Real.pi_gt_d2]) ht.2
  have hsinL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(-2:ℝ)/3 by linarith [Real.pi_gt_d2])
    (show t≤Real.pi/2 by linarith [ht.2,Real.pi_gt_d2]) ht.1
  have hsinBound := Real.sin_le (show (0:ℝ)≤2/3 by norm_num)
  rw [show (-2:ℝ)/3=-(2/3) by norm_num,Real.sin_neg] at hsinL
  have hsinBoundU := Real.sin_le (show (0:ℝ)≤2/5 by norm_num)
  have habs : |t|≤2/3 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg t) habs 2
  rw [sq_abs] at hsq
  exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x:=t)],
    by linarith,by linarith⟩

/-- One completed square proves the radical majorant throughout the domain. -/
lemma west_affine_radical {z:ℝ} (hz:z≤2/5) (hz0:-1≤z) :
    Real.sqrt (61/400-(3/20)*z)≤99/250-(13/80)*z := by
  have hpos : 0≤99/250-(13/80)*z := by linarith
  have hid : (99/250-(13/80)*z)^2-(61/400-(3/20)*z) =
      (169/6400)*(z+1704/4225)^2+7/338000 := by ring
  have hs : 61/400-(3/20)*z≤(99/250-(13/80)*z)^2 := by
    nlinarith [sq_nonneg (z+1704/4225)]
  have hh := Real.sqrt_le_sqrt hs
  rwa [Real.sqrt_sq hpos] at hh

lemma westCentralSupport_upper {t:ℝ} (ht:-2/3≤t ∧ t≤2/5) :
    westCentralSupport t ≤ (113/1000)*(3/10+(9/20)*Real.cos t+
      (9/20)*max (Real.sin t) 0) := by
  have htr := west_angle_bounds ht
  have hnonneg : 0≤3/10+(9/20)*Real.cos t+(9/20)*max (Real.sin t) 0 := by
    nlinarith [le_max_right (Real.sin t) 0]
  have hc : c0≤113/1000 := by dsimp [c0]; linarith [rho0_upper]
  exact mul_le_mul_of_nonneg_right hc hnonneg

private lemma radicals_bound {t:ℝ} (ht:-2/3≤t ∧ t≤2/5) :
    R0*Real.sqrt (53/200)+R0*Real.sqrt (61/400-(3/20)*Real.sin t) ≤
      (8443/5000)*(103/200)+(8443/5000)*(99/250-(13/80)*Real.sin t) := by
  have htr := west_angle_bounds ht
  have hroot := west_affine_radical htr.2.2 (by linarith [htr.2.1])
  have ha := mul_le_mul west_radius_bound.le west_root_bound
    (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤8443/5000)
  have hb := mul_le_mul west_radius_bound.le hroot
    (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤8443/5000)
  linarith

lemma west_sin_nonpos {t:ℝ} (ht:-2/3≤t ∧ t≤0) : Real.sin t≤0 := by
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-t by linarith)
    (show -t≤Real.pi by linarith [Real.pi_gt_d2])
  rw [Real.sin_neg] at h
  linarith

/-- The W-secondary stress is positive on the whole ordered triangle. -/
theorem westStressW_positive {t u:ℝ}
    (ht:-2/3≤t) (hu0:-2/5≤u) (hu1:u≤2/5) (htu:t≤u) : 0<westStressW t u := by
  have htb : -2/3≤t ∧ t≤2/5 := ⟨ht,htu.trans hu1⟩
  have hc := westCentralSupport_upper htb
  have hr := radicals_bound htb
  by_cases ht0:t≤0
  · have hs := west_sin_nonpos ⟨ht,ht0⟩
    by_cases hu0':u≤0
    · have hsu := west_sin_nonpos ⟨by linarith,hu0'⟩
      have hm := westMinorant_negative ht ⟨hu0,hu0'⟩ htu
      change 0< -3611073/5000000+(3/10)*Real.cos u+(-3/10)*Real.sin u+
        (3483/20000)*Real.cos t+(19759/400000)*Real.sin t+
        (1/4)*(Real.cos (u-t)+Real.sin (u-t)) at hm
      unfold westStressW
      rw [abs_of_nonpos hs,max_eq_right hs,max_eq_left (by linarith : 0≤-Real.sin u)] at *
      nlinarith [hc,hr]
    · have hsu := Real.sin_nonneg_of_nonneg_of_le_pi
        (show 0≤u by linarith) (show u≤Real.pi by linarith [Real.pi_gt_d2])
      have hm := westMinorant_mixed ⟨ht,ht0⟩ ⟨by linarith,hu1⟩
      change 0< -3611073/5000000+(3/10)*Real.cos u+0*Real.sin u+
        (3483/20000)*Real.cos t+(19759/400000)*Real.sin t+
        (1/4)*(Real.cos (u-t)+Real.sin (u-t)) at hm
      unfold westStressW
      rw [abs_of_nonpos hs,max_eq_right hs,max_eq_right (by linarith : -Real.sin u≤0)] at *
      nlinarith [hc,hr]
  · have hst := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤t by linarith)
      (show t≤Real.pi by linarith [Real.pi_gt_d2])
    have hsu := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤u by linarith)
      (show u≤Real.pi by linarith [Real.pi_gt_d2])
    have hm := westMinorant_positive (show 0≤t by linarith) hu1 htu
    change 0< -3611073/5000000+(3/10)*Real.cos u+0*Real.sin u+
      (3483/20000)*Real.cos t+(179419/400000)*Real.sin t+
      (1/4)*(Real.cos (u-t)+Real.sin (u-t)) at hm
    unfold westStressW
    rw [abs_of_nonneg hst,max_eq_left hst,max_eq_right (by linarith : -Real.sin u≤0)] at *
    nlinarith [hc,hr]

end SquaresInCircles.Six.Analytic
