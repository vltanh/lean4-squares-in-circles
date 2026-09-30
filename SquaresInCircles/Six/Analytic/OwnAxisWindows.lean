import SquaresInCircles.Six.Analytic.EndpointReduction
import SquaresInCircles.Six.Analytic.OwnMovingPin
import SquaresInCircles.Six.Analytic.PinArc
import SquaresInCircles.Seven.Analysis

/-!
# OWN primary-axis windows, before assigning pins

Each radial profile is a positive sine/cosine combination. Concavity reduces
the excluded outer subinterval to its two natural endpoints. The W-pin upper
bound uses monotonicity and one explicit far-corner contradiction. All rational
constants below are shown in the proof; none is a certificate result.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma quarter_trig_lower : (7:ℝ)/10≤Real.cos (Real.pi/4) ∧
    (7:ℝ)/10≤Real.sin (Real.pi/4) := by
  rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
  have h := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  constructor <;> nlinarith

lemma own_east_positive_profile {t a b cx cy : ℝ}
    (hx0 : 0≤cx) (hy0 : 0≤cy) (ht0 : 0≤t) (ht1 : t≤Real.pi/4)
    (ho : 0≤centralMargin .own t a b cx cy) :
    1/2+(1/2)*Real.cos t+(1/2)*Real.sin t≤a := by
  have hc : 0≤Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hcx := mul_nonneg hx0 hc
  have hcy := mul_nonneg hy0 hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [abs_of_nonneg hc,abs_of_nonneg hs] at ho
  linarith

lemma own_east_negative_profile {v a b cx cy : ℝ}
    (hx0 : 0≤cx) (hy : cy≤c0) (hv0 : 0≤v) (hv1 : v≤Real.pi/4)
    (ho : 0≤centralMargin .own (-v) a b cx cy) :
    1/2+(1/2)*Real.cos v+(387/1000)*Real.sin v≤a := by
  have hc : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_pos])
  have hcx := mul_nonneg hx0 hc
  have hcy : cy≤113/1000 := by dsimp [c0] at hy; linarith [rho0_upper]
  have hprod := mul_nonneg (sub_nonneg.mpr hcy) hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at ho
  nlinarith

/-- The full OWN-E octant reduces to the manuscript's asymmetric window. -/
theorem own_east_window {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx0 : 0≤cx) (hy0 : 0≤cy) (hy : cy≤c0) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own t a b cx cy) : -5/12<t ∧ t<3/10 := by
  have htb := abs_le.mp ht
  have ha := hc.a_le_rho0
  have hq := quarter_trig_lower
  constructor
  · by_contra! hbad
    have hp := own_east_negative_profile (a:=a) (b:=b) hx0 hy
      (show 0≤-t by linarith) (show -t≤Real.pi/4 by linarith)
      (by simpa only [neg_neg] using ho)
    have hl : (613:ℝ)/1000<(1/2)*Real.cos (5/12)+(387/1000)*Real.sin (5/12) := by
      have hs := Real.sin_ge_sub_cube (x:=(5:ℝ)/12) (by norm_num)
      have hc := Real.one_sub_sq_div_two_le_cos (x:=(5:ℝ)/12)
      norm_num at hs hc
      linarith
    have hu : (613:ℝ)/1000<(1/2)*Real.cos (Real.pi/4)+(387/1000)*Real.sin (Real.pi/4) := by
      linarith [hq.1,hq.2]
    have h := trig_lower_of_endpoints (A:=(1:ℝ)/2) (B:=(387:ℝ)/1000)
      (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤5/12)
      (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi/2)
      (t:=-t) ⟨by linarith,by linarith⟩ hl hu
    linarith [rho0_upper]
  · by_contra! hbad
    have hp := own_east_positive_profile hx0 hy0
      (show 0≤t by linarith) htb.2 ho
    have hl : (613:ℝ)/1000<(1/2)*Real.cos (3/10)+(1/2)*Real.sin (3/10) := by
      have hs := Real.sin_ge_sub_cube (x:=(3:ℝ)/10) (by norm_num)
      have hc := Real.one_sub_sq_div_two_le_cos (x:=(3:ℝ)/10)
      norm_num at hs hc
      linarith
    have hu : (613:ℝ)/1000<(1/2)*Real.cos (Real.pi/4)+(1/2)*Real.sin (Real.pi/4) := by
      linarith [hq.1,hq.2]
    have h := trig_lower_of_endpoints (A:=(1:ℝ)/2) (B:=(1:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤3/10)
      (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi/2)
      ⟨hbad,htb.2⟩ hl hu
    linarith [rho0_upper]

lemma own_west_negative_profile {v a b cx cy : ℝ}
    (hx : cx≤c0) (hy0 : 0≤cy) (hv0 : 0≤v) (hv1 : v≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi-v) a b cx cy) :
    1/2+(387/1000)*Real.cos v+(1/2)*Real.sin v≤a := by
  have hc : 0≤Real.cos v := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_pos])
  have hcx : cx≤113/1000 := by dsimp [c0] at hx; linarith [rho0_upper]
  have hp := mul_nonneg (sub_nonneg.mpr hcx) hc
  have hcy := mul_nonneg hy0 hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [Real.cos_pi_sub,Real.sin_pi_sub,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at ho
  nlinarith

lemma own_west_positive_profile {t a b cx cy : ℝ}
    (hx : cx≤c0) (hy : cy≤c0) (ht0 : 0≤t) (ht1 : t≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) :
    1/2+(387/1000)*(Real.cos t+Real.sin t)≤a := by
  have hc : 0≤Real.cos t := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
  have hcx : cx≤113/1000 := by dsimp [c0] at hx; linarith [rho0_upper]
  have hcy : cy≤113/1000 := by dsimp [c0] at hy; linarith [rho0_upper]
  have hp := mul_nonneg (sub_nonneg.mpr hcx) hc
  have hq := mul_nonneg (sub_nonneg.mpr hcy) hs
  dsimp [centralMargin,centralNormal,angularWidth] at ho
  rw [Real.cos_pi_add,Real.sin_pi_add,abs_neg,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs] at ho
  nlinarith

lemma own_west_lower_window {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx : cx≤c0) (hy0 : 0≤cy) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy) : -2/3<t := by
  by_contra! hbad
  have htb := abs_le.mp ht
  have hp := own_west_negative_profile (v:=-t) hx hy0
    (by linarith) (by linarith) (by simpa only [sub_neg_eq_add] using ho)
  have hl : (613:ℝ)/1000<(387/1000)*Real.cos (2/3)+(1/2)*Real.sin (2/3) := by
    have hs := Seven.sin_lower_seven (x:=(2:ℝ)/3) (by norm_num)
    have hc := Seven.cos_lower_six (x:=(2:ℝ)/3) (by norm_num)
    norm_num at hs hc
    linarith
  have hu : (613:ℝ)/1000<(387/1000)*Real.cos (Real.pi/4)+(1/2)*Real.sin (Real.pi/4) := by
    linarith [quarter_trig_lower.1,quarter_trig_lower.2]
  have h := trig_lower_of_endpoints (A:=(387:ℝ)/1000) (B:=(1:ℝ)/2)
    (by norm_num) (by norm_num) (by norm_num : (0:ℝ)≤2/3)
    (by linarith [Real.pi_pos] : Real.pi/4≤Real.pi/2)
    (t:=-t) ⟨by linarith,by linarith⟩ hl hu
  linarith [hc.a_le_rho0,rho0_upper]

/-- The W pin itself sharpens the positive OWN-W endpoint to 5/8. -/
theorem own_west_pin_upper {t a b cx cy : ℝ} (hc : ContainedChart a |b|)
    (hx : cx≤c0) (hy : cy≤c0) (ht : |t|≤Real.pi/4)
    (ho : 0≤centralMargin .own (Real.pi+t) a b cx cy)
    (hpin : openSquare (orientedSquare (Real.pi+t) a b) (polarPin (9/10) (11*Real.pi/12))) :
    t<5/8 := by
  by_contra! hbad
  have htb := abs_le.mp ht
  have hrad := own_west_positive_profile hx hy (by linarith) htb.2 ho
  have hcs0 : (279:ℝ)/200<Real.cos (5/8)+Real.sin (5/8) := by
    have hs := Seven.sin_lower_seven (x:=(5:ℝ)/8) (by norm_num)
    have hc := Seven.cos_lower_six (x:=(5:ℝ)/8) (by norm_num)
    norm_num at hs hc
    linarith
  have hcs := cos_add_sin_mono (x:=(5:ℝ)/8) (by norm_num) hbad htb.2
  have hs0 : (387:ℝ)/500<Real.sin (133/150) := by
    have h := Seven.sin_lower_seven (x:=(133:ℝ)/150) (by norm_num)
    norm_num at h
    linarith
  have hangle : (133:ℝ)/150≤Real.pi/12+t := by linarith [Real.pi_gt_d2]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(133:ℝ)/150 by linarith [Real.pi_pos])
    (show Real.pi/12+t≤Real.pi/2 by linarith [Real.pi_pos]) hangle
  rw [polar_mem_iff] at hpin
  have harg : 11*Real.pi/12-(Real.pi+t)=-(Real.pi/12+t) := by ring
  rw [harg,Real.sin_neg,mul_neg] at hpin
  have hb := (abs_lt.mp hpin.2).1
  have hA : 1+(387/1000)*(279/200)≤a+1/2 := by nlinarith
  have hB : (9/10)*(387/500)≤|b|+1/2 := by
    have hn := neg_le_abs b
    nlinarith
  have hAsq := mul_nonneg (sub_nonneg.mpr hA)
    (show 0≤a+1/2+(1+(387/1000)*(279/200)) by linarith [hc.half_le])
  have hBsq := mul_nonneg (sub_nonneg.mpr hB)
    (show 0≤|b|+1/2+(9/10)*(387/500) by linarith [abs_nonneg b])
  have hbadQ : Q0<(1+(387/1000)*(279/200))^2+((9/10)*(387/500))^2 := by norm_num [Q0]
  nlinarith [hc.containment]

end SquaresInCircles.Six.Analytic
