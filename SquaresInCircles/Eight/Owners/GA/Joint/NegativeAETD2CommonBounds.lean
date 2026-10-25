module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonCalculus
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonCertificates
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonInverse

/-!
# Eight squares: positive first and third derivatives of the common gain

Parameter monotonicity is established on the whole rectangle. The lower
third-derivative bound then uses exactly its prescribed k=.65 polynomial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

theorem sine_domain {x : ℝ} (hx : x∈Icc 0 frameCap) :
    Real.sin x∈Icc (0:ℝ) (129/200) :=
  ⟨(transport_trig hx).2.2.1,by linarith [(transport_trig hx).2.2.2.1]⟩

theorem ratio_upper {k x : ℝ} (hk : (13/20:ℝ)≤k) (hx : x∈Icc 0 frameCap) :
    R/D k x<(1773/1000:ℝ) := by
  have hy := sine_domain hx
  have hy2 : Real.sin x^2≤(129/200:ℝ)^2 := by nlinarith [hy.1,hy.2]
  have hk2 : (13/20:ℝ)^2≤k^2 := by nlinarith
  have hc2 : (1-(129/200:ℝ)^2)≤Real.cos x^2 := by rw [cos_square]; linarith
  have hm := mul_le_mul hk2 hc2 (by norm_num : 0≤1-(129/200:ℝ)^2) (sq_nonneg k)
  have hD := D_positive k x
  have hr : R^2=9789/2500 := Secondary.radius_sq
  have hsq : R^2<((1773/1000)*D k x)^2 := by
    rw [mul_pow,D_square,hr]
    nlinarith
  have hbound : R<(1773/1000)*D k x := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  exact (div_lt_iff₀ hD).2 hbound

theorem first_lower {k x : ℝ} (hk : (13/20:ℝ)≤k) (hx : x∈Icc 0 frameCap) :
    (9/10:ℝ)<F1 k x := by
  have hy := sine_domain hx
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hh := mul_le_mul_of_nonneg_right (ratio_upper hk hx).le hy.1
  have hq : 0<(9/10)*Real.sin x^2-(773/1000)*Real.sin x+K-9/10 := by
    dsimp [K]
    nlinarith [sq_nonneg ((9/5)*Real.sin x-773/1000)]
  have he : R*Real.sin x/D k x=(R/D k x)*Real.sin x := by ring
  dsimp [F1]
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  rw [he,cos_square]
  linarith

theorem signPolynomial_positive {p u : ℝ}
    (hp : p∈Icc (169/400:ℝ) (564001/1000000))
    (hu : u∈Icc (0:ℝ) ((129/200:ℝ)^2)) : 0<signPolynomial p u := by
  let U : ℝ := (129/200)^2
  have hU : 0≤U := by norm_num [U]
  have hu2 : u^2≤U^2 := by dsimp [U] at *; nlinarith [hu.1,hu.2]
  have hA : 8-4*U-4*U^2≤8-4*u-4*u^2 := by dsimp [U] at *; linarith [hu.2]
  have hB : 7-10*U≤7-10*u := by dsimp [U]; linarith [hu.2]
  have hp2 : (169/400:ℝ)^2≤p^2 := by nlinarith [hp.1]
  have ha := mul_le_mul hp2 hA (by norm_num [U]) (sq_nonneg p)
  have hb := mul_le_mul hp.1 hB (by norm_num [U]) (by linarith [hp.1])
  have he : signPolynomial p u=p^2*(8-4*u-4*u^2)+p*(7-10*u)-1 := by
    dsimp [signPolynomial]; ring
  rw [he]
  have hcorner : (0:ℝ)<(169/400)^2*(8-4*U-4*U^2)+(169/400)*(7-10*U)-1 := by
    norm_num [U]
  linarith

theorem parameter_monotonicity {x : ℝ} (hx : x∈Icc 0 frameCap) :
    MonotoneOn (fun k => F1 k x) (Icc (13/20:ℝ) (751/1000)) ∧
    MonotoneOn (fun k => F2 k x) (Icc (13/20:ℝ) (751/1000)) ∧
    MonotoneOn (fun k => F3 k x) (Icc (13/20:ℝ) (751/1000)) := by
  have hy := sine_domain hx
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  refine ⟨?_,?_,?_⟩
  · apply monoOn_of_hasDeriv_nonneg
    · intro k hk; exact (F1_parameter_derivative (k:=k) hx).continuousAt.continuousWithinAt
    · intro k hk; exact F1_parameter_derivative hx
    · intro k hk
      exact div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap)
        (by linarith [hk.1])) hy.1) (pow_nonneg (D_positive k x).le 3)
  · apply monoOn_of_hasDeriv_nonneg
    · intro k hk; exact (F2_parameter_derivative (k:=k) hx).continuousAt.continuousWithinAt
    · intro k hk; exact F2_parameter_derivative hx
    · intro k hk
      have hk0 : 0≤k := by linarith [hk.1]
      dsimp [F2k]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) hk0) hc.le)
        (by positivity)) (pow_nonneg (D_positive k x).le 5)
  · apply monoOn_of_hasDeriv_nonneg
    · intro k hk; exact (F3_parameter_derivative (k:=k) hx).continuousAt.continuousWithinAt
    · intro k hk; exact F3_parameter_derivative hx
    · intro k hk
      have hk0 : 0≤k := by linarith [hk.1]
      have hp : k^2∈Icc (169/400:ℝ) (564001/1000000) := by
        constructor <;> nlinarith [hk.1,hk.2]
      have hu : Real.sin x^2∈Icc (0:ℝ) ((129/200:ℝ)^2) :=
        ⟨sq_nonneg _,by nlinarith [hy.1,hy.2]⟩
      have hh := signPolynomial_positive hp hu
      dsimp [F3k]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) hk0) hy.1)
        hh.le) (pow_nonneg (D_positive k x).le 7)

theorem lowC_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (129/200)) :
    0<shapeC (13/20) y := by
  have hy2 : y^2≤(129/200:ℝ)^2 := by nlinarith [hy.1,hy.2]
  have hy4 : y^4≤(129/200:ℝ)^4 := pow_le_pow_left₀ hy.1 hy.2 4
  have hy6 : 0≤y^6 := pow_nonneg hy.1 6
  dsimp [shapeC]
  norm_num
  nlinarith

theorem low_factor {x : ℝ} (hx : x∈Icc 0 frameCap) :
    D (13/20) x=Real.sqrt (569/400)*inverseRoot ((169/569)*Real.sin x^2) := by
  have hy := sine_domain hx
  have hv : (169/569)*Real.sin x^2<1 := by nlinarith [hy.1,hy.2]
  have hS : 0<Real.sqrt (569/400:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hS2 := Real.sq_sqrt (show (0:ℝ)≤569/400 by norm_num)
  have hv2 := inverseRoot_square hv
  have hprod : 0<Real.sqrt (569/400:ℝ)*inverseRoot ((169/569)*Real.sin x^2) :=
    mul_pos hS (inverseRoot_positive hv)
  have hsquare : (Real.sqrt (569/400:ℝ)*inverseRoot ((169/569)*Real.sin x^2))^2=
      (D (13/20) x)^2 := by rw [mul_pow,hS2,hv2,D_shape]; dsimp [shapeA]; ring
  nlinarith [D_positive (13/20) x]

theorem low_radius_ratio : R/(Real.sqrt (569/400:ℝ))^5<(163983/200000:ℝ) := by
  have hs : 0<Real.sqrt (569/400:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤569/400 by norm_num)
  have hs10 : (Real.sqrt (569/400:ℝ)^5)^2=(569/400:ℝ)^5 := by
    rw [←pow_mul,show 5*2=2*5 by norm_num,pow_mul,hs2]
  have hr : R^2=9789/2500 := Secondary.radius_sq
  have hsq : R^2<((163983/200000)*Real.sqrt (569/400:ℝ)^5)^2 := by
    rw [mul_pow,hs10,hr]
    norm_num
  have hbound := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  exact (div_lt_iff₀ (pow_pos hs 5)).2 hbound

theorem third_low {x : ℝ} (hx : x∈Icc 0 frameCap) : (11/10:ℝ)<F3 (13/20) x := by
  have hy := sine_domain hx
  let v := (169/569)*Real.sin x^2
  have hv : v∈Icc (0:ℝ) (31/250) := by dsimp [v]; constructor <;> nlinarith [hy.1,hy.2]
  have hroot := inverseRoot_positive (show v<1 by linarith [hv.2])
  have hL := inverse_five_upper hv
  have hratio : R/(D (13/20) x)^5≤(163983/200000)*L v := by
    have hm := mul_le_mul low_radius_ratio.le hL (by positivity : 0≤1/(inverseRoot v)^5)
      (by norm_num : (0:ℝ)≤163983/200000)
    rw [low_factor hx,mul_pow]
    convert hm using 1
    · dsimp [v]
      field_simp [(show Real.sqrt (569/400:ℝ)≠0 by positivity),hroot.ne']
  have hC := lowC_positive hy
  have hmul := mul_le_mul_of_nonneg_right hratio (mul_nonneg hy.1 hC.le)
  have hP := Certificate.P_positive hy
  have hid : Polynomial.aeval (Real.sin x) Certificate.P=
      2*K-11/10+5*Real.sin x+(4*K+11/5)*Real.sin x^2+
        Real.sin x^3-(11/10)*Real.sin x^4-
        (163983/200000)*Real.sin x*shapeC (13/20) (Real.sin x)*L v := by
    simp [Certificate.P,Certificate.c,Certificate.l,Certificate.pLow,shapeC,L,K,v]
    ring
  rw [hid] at hP
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  have hc4 : Real.cos x^4=(1-Real.sin x^2)^2 := by
    rw [show Real.cos x^4=(Real.cos x^2)^2 by ring,cos_square]
  apply (lt_div_iff₀ (pow_pos hc 4)).2
  change (11/10)*Real.cos x^4<2*K+5*Real.sin x+4*K*Real.sin x^2+Real.sin x^3-
    R*Real.sin x*shapeC (13/20) (Real.sin x)/(D (13/20) x)^5
  rw [hc4]
  have he : R*Real.sin x*shapeC (13/20) (Real.sin x)/(D (13/20) x)^5=
      (R/(D (13/20) x)^5)*(Real.sin x*shapeC (13/20) (Real.sin x)) := by ring
  rw [he]
  nlinarith


theorem third_lower {k x : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hx : x∈Icc 0 frameCap) : (11/10:ℝ)<F3 k x :=
  (third_low hx).trans_le ((parameter_monotonicity hx).2.2 ⟨le_rfl,by norm_num⟩ hk hk.1)

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
