module

public import SquaresInCircles.Eight.TableFree.FrameHighLowDiagonalCurve

/-!
# Uniform curvature of the explicit high-diagonal contact

The correlation `w*w'` has one quadratic upper bound.  It controls the
first root derivative, while the root equation controls the second.
The resulting contact curvature is less than `-.8` on the complete
interval.  This proof does not use an implicit-function premise.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowDiagonalCurvature
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowDiagonalCurve

theorem sine_linear_lower {x : ℝ} (hx : x∈domain) : (99/100)*x≤Real.sin x := by
  have hs := Real.sin_ge_sub_cube hx.1
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hmul := mul_nonneg hx.1 (show 0≤(11/100:ℝ)^2-x^2 by linarith)
  nlinarith

theorem correlated_slope_upper {x : ℝ} (hx : x∈domain) : w x*wd x≤5/8 := by
  have ht := trig_bounds hx
  have hs := sine_linear_lower hx
  have hs2 := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤99/100) hx.1) hs 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hdc := mul_le_mul
    (show (399/1000:ℝ)≤c0-1/2 by linarith [c0_bounds.1]) hcos
    (by nlinarith : 0≤1-x^2/2) (by linarith [c0_bounds.1] : 0≤c0-1/2)
  have hds := mul_le_mul
    (show c0-1/2≤2/5 by linarith [c0_bounds.2]) (Real.sin_le_self hx.1)
    ht.1 (by norm_num : (0:ℝ)≤2/5)
  have hid : w x*wd x=1-2*(Real.sin x)^2-(c0-1/2)*Real.cos x+(c0-1/2)*Real.sin x := by
    dsimp [w,wd]
    linear_combination Real.sin_sq_add_cos_sq x
  rw [hid]
  nlinarith [sq_nonneg ((17607/5000:ℝ)*x-2/5)]

theorem rho_first_lower {x : ℝ} (hx : x∈domain) : -(17/50:ℝ)≤rhod x := by
  have hnum := correlated_slope_upper hx
  have hr := (rho_bounds hx).1
  have hquot : w x*wd x/rho x≤17/50 := by
    apply (div_le_iff₀ (rho_positive hx)).2
    linarith
  dsimp [rhod]
  nlinarith

theorem rho_second_lower {x : ℝ} (hx : x∈domain) : -(63/100:ℝ)≤rhodd x := by
  have hw := w_bounds hx
  have hr := rho_bounds hx
  have hp := rho_positive hx
  have hd0 : 0≤wd x := by linarith [hw.2.2.1]
  have hd2 := pow_le_pow_left₀ hd0 hw.2.2.2.1 2
  have hw2 := pow_le_pow_left₀ hw.1.le hw.2.1.le 2
  have hwdd := mul_nonpos_of_nonneg_of_nonpos hw.1.le
    (by linarith [hw.2.2.2.2] : wdd x≤0)
  have hfirst : ((wd x)^2+w x*wdd x)/rho x≤25/46 := by
    apply (div_le_iff₀ hp).2
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hd2 (sq_nonneg (w x))
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤46/25) hr.1.le 3
  have hsecond : (w x)^2*(wd x)^2/(rho x)^3≤17/200 := by
    apply (div_le_iff₀ (pow_pos hp 3)).2
    nlinarith
  dsimp [rhodd]
  linarith

theorem contact_second_upper {x : ℝ} (hx : x∈domain) : zdd x<-(4/5:ℝ) := by
  have ht := trig_bounds hx
  have hw := w_bounds hx
  have hr := rho_bounds hx
  have hrd := rho_first_lower hx
  have hrdd := rho_second_lower hx
  have hfirst : wdd x-2*rhod x-w x≤-(23/25:ℝ) := by
    have hsum := ht.2.2.2.2
    dsimp [w,wdd] at *
    linarith [c0_bounds.2]
  have hsecond : rho x-2*wd x-rhodd x≤2103/2500 := by
    linarith [hw.2.2.1]
  have hfirstMul := mul_le_mul_of_nonneg_right hfirst
    (show 0≤Real.cos x by linarith [ht.2.2.1])
  have hcosMul := mul_le_mul_of_nonpos_left ht.2.2.1 (by norm_num : (-(23/25:ℝ))≤0)
  have hsecondMul := mul_le_mul_of_nonneg_right hsecond ht.1
  have hsinMul := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num : (0:ℝ)≤2103/2500)
  dsimp [zdd]
  linarith

theorem source_chart {x : ℝ} (hx : x∈domain) : z x∈extendedDomain := by
  have hh := z_bounds hx
  constructor <;> linarith [hh.1,hh.2]

theorem marker_derivative_lower {x : ℝ} (hx : x∈domain) : (19/20:ℝ)<Ld (z x) := by
  have hz := z_bounds hx
  have he := source_chart hx
  have hc := extended_circle he
  have hp := extended_shift_pos he
  have hsq := pow_le_pow_left₀ (show 0≤z x+1/2 by linarith [hz.1])
    (show z x+1/2≤601/1000 by linarith [hz.2]) 2
  have hA : (47/25:ℝ)<A (z x)+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hratio : slope (z x)<8/25 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  linarith

end SquaresInCircles.Eight.TableFree.FrameHighLowDiagonalCurvature
