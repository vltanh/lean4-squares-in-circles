module
public import SquaresInCircles.Six.Analytic.HalfAngleControl
public import SquaresInCircles.Six.Normalization.CentralSAT

@[expose] public section

/-!
# Canonical OWN W cannot turn toward D

This module contains the scalar part of that geometric exclusion. A D-own
square in the first southwest octant obeys
  |bD| + (cos d + sin d)/2 < 97/100.
The proof is one displayed positive quadratic in cos d + sin d - 1.

For 0<=w<=d<=pi/4, the canonical OWN/cardinal margin difference supplies a
lower bound on bW in terms of halfRatio w. Both possible forward secondary
separators then have a strictly negative margin. The two reserves below use
whole-interval Taylor and monotonicity inequalities, not selected cells.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

/-- A stronger transverse bound for D, derived from its actual OWN separator. -/
theorem diagonal_transverse_profile {a b cx cy d : ℝ}
    (hc : ContainedChart a |b|) (hx : cx≤c0) (hy : cy≤c0)
    (hd : 0≤d ∧ d≤Real.pi/4)
    (hown : 0≤centralMargin .own (Real.pi+d) a b cx cy) :
    |b|+(Real.cos d+Real.sin d)/2<97/100 := by
  have hcd : 0≤Real.cos d := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hd.1,Real.pi_pos],by linarith [hd.2,Real.pi_pos]⟩
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi hd.1 (by linarith [hd.2,Real.pi_pos])
  let v := Real.cos d+Real.sin d
  have hv0 : 1≤v := by
    simpa only [v,abs_of_nonneg hcd,abs_of_nonneg hsd] using one_le_abs_cos_add_abs_sin d
  have hv1 : v≤3/2 := by
    dsimp [v]
    nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.cos d-Real.sin d)]
  have hcx := mul_nonneg (show 0≤1/2-cx-77/200 by linarith [c0_lt_23_200]) hcd
  have hcy := mul_nonneg (show 0≤1/2-cy-77/200 by linarith [c0_lt_23_200]) hsd
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
    abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hown
  have hA : 1+(77/200)*v≤a+1/2 := by dsimp [v]; nlinarith only [hown,hcx,hcy]
  by_contra! hbad
  have hB : 147/100-v/2≤|b|+1/2 := by dsimp [v]; linarith
  have hA0 : 0≤1+(77/200)*v := by linarith
  have hB0 : 0≤147/100-v/2 := by linarith
  have hAsq := mul_nonneg (sub_nonneg.mpr hA)
    (show 0≤a+1/2+(1+(77/200)*v) by linarith [hc.half_le])
  have hBsq := mul_nonneg (sub_nonneg.mpr hB)
    (show 0≤|b|+1/2+(147/100-v/2) by linarith [abs_nonneg b])
  have hid : (1+(77/200)*v)^2+(147/100-v/2)^2-Q0=
      (15929/40000)*(v-1)^2+(1929/20000)*(v-1)+1589/200000 := by
    norm_num [Q0]
    ring
  have hpositive : Q0<(1+(77/200)*v)^2+(147/100-v/2)^2 := by
    nlinarith [sq_nonneg (v-1)]
  nlinarith [hc.containment]

/-- Reserve against the W-secondary separator on the entire ordered octant. -/
theorem canonical_west_secondary_reserve {w d : ℝ}
    (hw : 0≤w) (hwd : w≤d) (hd : d≤Real.pi/4) :
    113/1000+(1113/1000)*(Real.sin (d-w)+halfRatio w)+
        (97/100-(Real.cos d+Real.sin d)/2)*Real.cos (d-w)<
      (1+Real.cos (d-w)+Real.sin (d-w))/2 := by
  let q := d-w
  have hd0 : 0≤d := hw.trans hwd
  have hd1 : d≤4/5 := by linarith [Real.pi_lt_d2]
  have hq0 : 0≤q := by dsimp [q]; linarith
  have hqd : q≤d := by dsimp [q]; linarith
  have hq1 : q≤4/5 := hqd.trans hd1
  have htp := halfRatio_upper ⟨hw,hwd.trans hd1⟩
  have hsum := (small_polynomial_trig ⟨hd0,hd1⟩).2.2.2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := q)
  have hsin := Real.sin_le hq0
  have hq2p := mul_nonneg (sub_nonneg.mpr hq1) (show 0≤4/5+q by linarith)
  have hq2 : q^2≤16/25 := by nlinarith
  let A := (Real.cos d+Real.sin d)/2-47/100
  have hA : 3/100+(6/25)*d≤A := by dsimp [A]; linarith
  have hA0 : 0≤A := by linarith
  have hC := mul_le_mul hA hcos (show 0≤1-q^2/2 by linarith) hA0
  have hS := mul_le_mul_of_nonneg_left hsin (show (0:ℝ)≤613/1000 by norm_num)
  have hT := mul_le_mul_of_nonneg_left htp (show (0:ℝ)≤1113/1000 by norm_num)
  let p := 417/1000-(373/1000)*d-(3/200)*d^2-(3/25)*d^3
  have hd2p := mul_nonneg (sub_nonneg.mpr hd1) (show 0≤4/5+d by linarith)
  have hd2 : d^2≤16/25 := by nlinarith
  have hd3p := mul_le_mul hd1 hd2 (sq_nonneg d) (by norm_num : (0:ℝ)≤4/5)
  have hd3 : d^3≤64/125 := by nlinarith only [hd3p]
  have hp : 1189/25000≤p := by dsimp [p]; linarith
  have hfactor : 0≤(d-q)*(2400*d^2+2400*d*q+300*d+300*q+17)/20000 := by
    apply div_nonneg
    · apply mul_nonneg (sub_nonneg.mpr hqd)
      positivity
    · norm_num
  have hid : 387/1000+(3/100+(6/25)*d)*(1-q^2/2)-(613/1000)*q-
        (1113/1000)*(11/20)*w=
      p+(d-q)*(2400*d^2+2400*d*q+300*d+300*q+17)/20000 := by
    dsimp [p,q]
    ring
  change 113/1000+(1113/1000)*(Real.sin q+halfRatio w)+
      (97/100-(Real.cos d+Real.sin d)/2)*Real.cos q<
      (1+Real.cos q+Real.sin q)/2
  dsimp [A] at hC
  nlinarith only [hC,hS,hT,hp,hfactor,hid]

/-- Reserve against the D-secondary separator on the same whole domain. -/
theorem canonical_diagonal_secondary_reserve {w d : ℝ}
    (hw : 0≤w) (hwd : w≤d) (hd : d≤Real.pi/4) :
    (97/100-(Real.cos d+Real.sin d)/2)+
        (1113/1000)*(Real.sin (d-w)+halfRatio w*Real.cos (d-w))+
        (113/1000)*Real.cos (d-w)<
      (1+Real.cos (d-w)+Real.sin (d-w))/2 := by
  let q := d-w
  have hd0 : 0≤d := hw.trans hwd
  have hd1 : d≤4/5 := by linarith [Real.pi_lt_d2]
  have hq0 : 0≤q := by dsimp [q]; linarith
  have hqd : q≤d := by dsimp [q]; linarith
  have hq1 : q≤4/5 := hqd.trans hd1
  have hcd := (small_polynomial_trig ⟨hd0,hd1⟩).1
  have hsd := (small_polynomial_trig ⟨hd0,hd1⟩).2.2.1
  have hcos := cosine_difference_lower hq0 hqd hd1
  have hsin := sine_difference_upper hqd
  have hT := mul_le_mul_of_nonneg_right
    (halfRatio_lower ⟨hw,hwd.trans hd1⟩) (show 0≤Real.cos d by linarith)
  have hTm := mul_le_mul_of_nonneg_left hT (show (0:ℝ)≤1113/1000 by norm_num)
  have hCm := mul_le_mul_of_nonneg_left hcos (show (0:ℝ)≤387/1000 by norm_num)
  have hpow := mul_nonneg hd0 (sub_nonneg.mpr hd1)
  have hcdpoly := Real.one_sub_sq_div_two_le_cos (x := d)
  have hcdlin : 1-(2/5)*d≤Real.cos d := by nlinarith only [hpow,hcdpoly]
  let coef := (89/200)*(387/1000)*d-1/2+(1113/2000)*Real.cos d
  have hcoef : 0≤coef := by dsimp [coef]; linarith
  have hcp := mul_nonneg hw hcoef
  have hextra : 0≤(89/200)*(387/1000)*w*q := by positivity
  have hdiff : d^2-q^2=w*(d+q) := by dsimp [q]; ring
  have hsub : d-q=w := by dsimp [q]; ring
  have hB : 0≤(387/1000)*(Real.cos q-Real.cos d)+
      (1/2)*(Real.sin q-Real.sin d)+(1113/1000)*halfRatio w*Real.cos d := by
    rw [hsub] at hsin
    rw [hdiff] at hCm
    dsimp [coef] at hcp
    nlinarith only [hCm,hsin,hTm,hcp,hextra]
  have hbase : 1069/25000≤(887/1000)*Real.cos d-(113/1000)*Real.sin d-47/100 := by
    linarith
  rw [halfRatio_shift ⟨hw,hwd.trans hd1⟩]
  change (97/100-(Real.cos d+Real.sin d)/2)+
      (1113/1000)*(Real.sin d-halfRatio w*Real.cos d)+(113/1000)*Real.cos q<
      (1+Real.cos q+Real.sin q)/2
  nlinarith only [hB,hbase]

end SquaresInCircles.Six.Analytic
