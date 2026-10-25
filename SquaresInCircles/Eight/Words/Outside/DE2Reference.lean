module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Words.Outside.DE2Polynomial
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: reference contact for the outside DE2 comparison

The reference uses the same original q and the least sorted H primary `leastPrimary`. It is only
a comparison of real scalar functions; no square of the packing is moved to it. The polynomial
envelopes (`bounds`) are derived here from the exact circle and contact formulas; they give the
positive gap derivative `derivative_pos`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OutsideDE2Reference
open Polynomial OutsideDE2Polynomial

def radius (q : ℝ) : ℝ := Real.sqrt q
def leastPrimary (q : ℝ) : ℝ := Real.sqrt (q/2)-1
def u (q p : ℝ) : ℝ := leastPrimary q-Real.sin p
def z (q p : ℝ) : ℝ := Real.sqrt (q-(u q p)^2)
def x (q p : ℝ) : ℝ := z q p*Real.cos p-u q p*Real.sin p
def y (q p : ℝ) : ℝ := z q p*Real.sin p+u q p*Real.cos p
def beta (q p : ℝ) : ℝ := x q p*(1-Real.cos p/z q p)
def ell (q p : ℝ) : ℝ := 1+Real.cos (7/10 : ℝ)-y q p
def root (q p : ℝ) : ℝ := Real.sqrt (q-(ell q p)^2)
def gap (q p : ℝ) : ℝ := root q p-Real.sin (7/10 : ℝ)-
  x q p*(1-Real.cos p/radius q)
def gapDerivative (q p : ℝ) : ℝ := beta q p*
  (ell q p/root q p+y q p/x q p*(1-Real.cos p/radius q))-
    x q p*Real.sin p/radius q

theorem constant_bounds {q : ℝ} (hq : qLow≤q∧q≤qCap) :
    (Rlo:ℝ)<radius q ∧ radius q<(Rhi:ℝ) ∧
      (Plo:ℝ)<leastPrimary q ∧ leastPrimary q<(Phi:ℝ) := by
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  have hr := Real.sq_sqrt hq0
  have hp := Real.sq_sqrt (show 0≤q/2 by linarith)
  have hr0 := Real.sqrt_nonneg q
  have hp0 := Real.sqrt_nonneg (q/2)
  dsimp [radius,leastPrimary,Rlo,Rhi,Plo,Phi,qLow,qCap] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem taylor_bounds {p : ℝ} (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    0≤aeval p S3 ∧ aeval p S3≤Real.sin p ∧ Real.sin p≤aeval p S5 ∧
      0<aeval p C2 ∧ aeval p C2≤Real.cos p ∧ Real.cos p≤aeval p C4 ∧
        aeval p C4≤1 ∧ 0≤Real.sin p ∧ Real.sin p<129/200 := by
  have hp0 : 0≤p := by linarith [hp.1]
  have hp2 := pow_le_pow_left₀ hp0 hp.2 2
  have hp3 := pow_le_pow_left₀ hp0 hp.2 3
  obtain ⟨hc,hc1,hs,hsu,hsc⟩ := transport_trig ⟨hp0,hp.2⟩
  have hmul := mul_nonneg (sq_nonneg p) (show 0≤12-p^2 by nlinarith)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hs,by linarith⟩
  · rw [S3_eval]; nlinarith [hp.1]
  · rw [S3_eval]; exact Real.sin_ge_sub_cube hp0
  · rw [S5_eval]; exact sin_upper_five hp0
  · rw [C2_eval]; nlinarith
  · rw [C2_eval]; exact Real.one_sub_sq_div_two_le_cos
  · rw [C4_eval]; exact cos_upper_four hp0
  · rw [C4_eval]; nlinarith

theorem z_bounds {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    (Zlo:ℝ)<z q p ∧ z q p≤radius q ∧ 0<q-(u q p)^2 := by
  obtain ⟨-,-,hpl,hpu⟩ := constant_bounds hq
  obtain ⟨-,hs3s,-,-,-,-,-,-,hshi⟩ := taylor_bounds hp
  have hp3 := pow_le_pow_left₀ (show 0≤p by linarith [hp.1]) hp.2 3
  have eP : (Plo:ℝ)=3991/10000 := by norm_num [Plo]
  have eQ : (Phi:ℝ)=3993/10000 := by norm_num [Phi]
  have eZ : (Zlo:ℝ)=981/500 := by norm_num [Zlo]
  rw [S3_eval] at hs3s
  have hu : -(123/500 : ℝ)<u q p ∧ u q p<123/500 := by
    unfold u
    constructor
    · linarith only [hpl,eP,hshi]
    · linarith only [hpu,eQ,hs3s,hp3,hp.1]
  have hu2 : (u q p)^2<(123/500 : ℝ)^2 := sq_lt_sq' hu.1 hu.2
  have hzrad : (Zlo:ℝ)^2<q-(u q p)^2 := by
    have hq1 : (19577/5000:ℝ)≤q := hq.1
    rw [eZ]
    linarith only [hq1,hu2]
  have hz0 : 0<q-(u q p)^2 := lt_of_le_of_lt (sq_nonneg _) hzrad
  refine ⟨(Real.lt_sqrt (by rw [eZ]; norm_num)).mpr hzrad,?_,hz0⟩
  exact Real.sqrt_le_sqrt (by linarith only [sq_nonneg (u q p)])

/-- Bounds used in the polynomial transfer, proved from the reference solution at the
original q. -/
structure Bounds (q p : ℝ) : Prop where
  radius_lower : (Rlo:ℝ)<radius q
  radius_upper : radius q<(Rhi:ℝ)
  z_lower : (Zlo:ℝ)<z q p
  z_upper : z q p≤radius q
  x_lower : aeval p Xlo≤x q p
  x_upper : x q p≤aeval p Xhi
  y_lower : aeval p Ylo≤y q p
  y_upper : y q p≤aeval p Yhi
  beta_lower : aeval p Xlo*aeval p Alo≤beta q p
  radius_factor : aeval p Alo≤1-Real.cos p/radius q
  ell_lower : aeval p Llo≤ell q p
  sine_lower : 0≤Real.sin p
  sine_upper : Real.sin p≤aeval p S5

theorem bounds {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : Bounds q p := by
  obtain ⟨hrl,hru,hpl,hpu⟩ := constant_bounds hq
  obtain ⟨hzl,hzr,-⟩ := z_bounds hq hp
  obtain ⟨hs3,hs3s,hss5,hc2,hc2c,hcc4,-,hs,-⟩ := taylor_bounds hp
  obtain ⟨-,-,hxl,-,ha,-⟩ := factors_positive hp
  have eR : (Rhi:ℝ)=4947/2500 := by norm_num [Rhi]
  have eZ : (Zlo:ℝ)=981/500 := by norm_num [Zlo]
  have eP : (Plo:ℝ)=3991/10000 := by norm_num [Plo]
  have eQ : (Phi:ℝ)=3993/10000 := by norm_num [Phi]
  have hc : 0≤Real.cos p := hc2.le.trans hc2c
  have hc4 : 0≤aeval p C4 := hc.trans hcc4
  have hP0 : 0≤leastPrimary q := by linarith only [hpl,eP]
  have hc1 := Real.cos_le_one p
  have hz0 : 0<z q p := by linarith only [hzl,eZ]
  have hXl : aeval p Xlo≤x q p := by
    have h1 := mul_le_mul hzl.le hc2c hc2.le hz0.le
    have h2 := mul_le_mul hpu.le hss5 hs (by linarith only [eQ])
    have h3 := pow_le_pow_left₀ hs3 hs3s 2
    simp only [Xlo,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast]
    dsimp only [x,u]
    linarith only [h1,h2,h3]
  have hXu : x q p≤aeval p Xhi := by
    have h1 := mul_le_mul (hzr.trans hru.le) hcc4 hc (by linarith only [eR])
    have h2 := mul_le_mul hpl.le hs3s hs3 hP0
    have h3 := pow_le_pow_left₀ hs hss5 2
    simp only [Xhi,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast]
    dsimp only [x,u]
    linarith only [h1,h2,h3]
  have hYl : aeval p Ylo≤y q p := by
    have h1 := mul_le_mul (sub_le_sub hzl.le hcc4) hs3s hs3
      (by linarith only [hzl,eZ,hc1] : 0≤z q p-Real.cos p)
    have h2 := mul_le_mul hpl.le hc2c hc2.le hP0
    simp only [Ylo,map_add,map_sub,map_mul,aeval_C,eq_ratCast]
    dsimp only [y,u]
    linarith only [h1,h2]
  have hYu : y q p≤aeval p Yhi := by
    have h1 := mul_le_mul (sub_le_sub (hzr.trans hru.le) hc2c) hss5 hs
      (by linarith only [eR,hc2c,hc1])
    have h2 := mul_le_mul hpu.le hcc4 hc (by linarith only [eQ])
    simp only [Yhi,map_add,map_sub,map_mul,aeval_C,eq_ratCast]
    dsimp only [y,u]
    linarith only [h1,h2]
  have hfac : aeval p Alo≤1-Real.cos p/z q p := by
    have hh := div_le_div₀ hc4 hcc4 (by rw [eZ]; norm_num) hzl.le
    simp only [Alo,map_sub,map_mul,map_one,aeval_C,eq_ratCast,Rat.cast_div,Rat.cast_one]
    rw [eZ] at hh ⊢
    linarith only [hh]
  have hfacR : aeval p Alo≤1-Real.cos p/radius q := by
    have hh := div_le_div₀ hc le_rfl hz0 hzr
    linarith only [hh,hfac]
  have hb : aeval p Xlo*aeval p Alo≤beta q p :=
    mul_le_mul hXl hfac ha.le (hxl.le.trans hXl)
  have he : aeval p Llo≤ell q p := by
    have hh := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
    have hcos : (478/625 : ℝ)<Real.cos (7/10 : ℝ) := by norm_num at hh ⊢; linarith
    simp only [Llo,map_sub,aeval_C,eq_ratCast]
    dsimp only [ell]
    push_cast
    linarith only [hYu,hcos]
  exact ⟨hrl,hru,hzl,hzr,hXl,hXu,hYl,hYu,hb,hfacR,he,hs,hss5⟩

/-- `Ylo - 1/2` has positive Bernstein coefficients of degree seven on `[11/50, 7/10]`. -/
theorem y_gt_half {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : 1/2<y q p := by
  have h0 : 0≤p-11/50 := sub_nonneg.2 hp.1
  have h1 : 0≤7/10-p := sub_nonneg.2 hp.2
  have hb (i j : ℕ) : 0≤(p-11/50)^i*(7/10-p)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  have hh : 1/2<aeval p Ylo := by
    simp only [Ylo,S3,C2,C4,Zlo,Plo,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    linarith [hb 7 0,hb 6 1,hb 5 2,hb 4 3,hb 3 4,hb 2 5,hb 1 6,hb 0 7]
  linarith [(bounds hq hp).y_lower]

theorem root_bounds {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    0<ell q p ∧ ell q p<3/2 ∧ 0<root q p ∧ root q p≤radius q := by
  have hb := bounds hq hp
  have hy := y_gt_half hq hp
  have hl : 0<ell q p := (factors_positive hp).2.2.2.2.2.trans_le hb.ell_lower
  have hlu : ell q p<3/2 := by dsimp [ell]; linarith [Real.cos_le_one (7/10 : ℝ)]
  have hr : 0<q-(ell q p)^2 := by
    have hq0 := hq.1
    dsimp [qLow] at hq0
    nlinarith
  exact ⟨hl,hlu,Real.sqrt_pos.mpr hr,
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (ell q p)])⟩

theorem derivative_pos {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) : 0<gapDerivative q p := by
  have hb := bounds hq hp
  have hr := root_bounds hq hp
  exact OutsideDE2Polynomial.derivative_positive hp hb.radius_lower.le hb.radius_upper.le
    hb.x_lower hb.x_upper hb.y_lower hb.ell_lower hr.2.2.1 hr.2.2.2
    hb.beta_lower hb.radius_factor hb.sine_lower hb.sine_upper

theorem contact_circle {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    (x q p)^2+(y q p)^2=q ∧
      y q p*Real.cos p-(x q p-1)*Real.sin p=leastPrimary q := by
  have hz : (z q p)^2=q-(u q p)^2 := Real.sq_sqrt (z_bounds hq hp).2.2.le
  have hu := Real.sin_sq_add_cos_sq p
  have hid (Z U s c : ℝ) : (Z*c-U*s)^2+(Z*s+U*c)^2=(Z^2+U^2)*(s^2+c^2) := by ring
  have hi2 (Z U s c : ℝ) : (Z*s+U*c)*c-(Z*c-U*s-1)*s=U*(s^2+c^2)+s := by ring
  constructor
  · rw [x,y,hid,hu]
    linarith
  · rw [x,y,hi2,hu]
    simp [u]

end SquaresInCircles.Eight.OutsideDE2Reference
