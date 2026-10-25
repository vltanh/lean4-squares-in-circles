module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2CommonCertificates
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Taylor
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedNegativeCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes

/-!
# Eight squares: removing the merged negative total

The secant term is concave in tan S. The unaffected term has a convex
first derivative and a negative right derivative on the long interval;
on the short interval its ordinary second derivative is negative.
Both arguments retain the complete continuous interval [0,t].
-/

section
/-!
## The two rational inverse-power bounds used by the common gain

Multiplication by the positive odd power of `sqrt (1-v)` removes the
inverse power. The first resulting derivative has one explicitly known
sign change; the second is nonpositive. Thus the displayed binomial
majorant and minorant hold on their complete stated intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain

def inverseRoot (v : ℝ) : ℝ := Real.sqrt (1-v)
def scaledUpper (v : ℝ) : ℝ := L v*(inverseRoot v)^5
def scaledLower (v : ℝ) : ℝ := L2 v*(inverseRoot v)^3

theorem inverseRoot_positive {v : ℝ} (hv : v<1) : 0< inverseRoot v :=
  Real.sqrt_pos.mpr (by linarith)
theorem inverseRoot_square {v : ℝ} (hv : v<1) : (inverseRoot v)^2=1-v :=
  Real.sq_sqrt (by linarith)
theorem inverseRoot_derivative {v : ℝ} (hv : v<1) :
    HasDerivAt inverseRoot (-1/(2*inverseRoot v)) v := by
  have h := ((hasDerivAt_id' v).const_sub 1).sqrt (by linarith : (1:ℝ)-v≠0)
  exact h

theorem L_derivative (v : ℝ) :
    HasDerivAt L (5/2+(35/4)*v+24*v^2) v := by
  have h := ((((hasDerivAt_id' v).const_mul (5/2:ℝ)).const_add 1).add
    ((hasDerivAt_pow 2 v).const_mul (35/8:ℝ))).add ((hasDerivAt_pow 3 v).const_mul (8:ℝ))
  convert h using 1
  · funext x; simp only [L,Pi.add_apply]
  · norm_num; ring
theorem L2_derivative (v : ℝ) :
    HasDerivAt L2 (3/2+(15/4)*v+(105/16)*v^2) v := by
  have h := ((((hasDerivAt_id' v).const_mul (3/2:ℝ)).const_add 1).add
    ((hasDerivAt_pow 2 v).const_mul (15/8:ℝ))).add ((hasDerivAt_pow 3 v).const_mul (35/16:ℝ))
  convert h using 1
  · funext x; simp only [L2,Pi.add_apply]
  · norm_num; ring

theorem scaledUpper_derivative {v : ℝ} (hv : v<1) :
    HasDerivAt scaledUpper ((inverseRoot v)^3*v^2*(69/16-44*v)) v := by
  have hp := inverseRoot_positive hv
  have hh := (L_derivative v).mul ((inverseRoot_derivative hv).pow 5)
  convert hh using 1
  · rfl
  · calc
      (inverseRoot v)^3*v^2*(69/16-44*v)=
          (inverseRoot v)^3*((1-v)*(5/2+(35/4)*v+24*v^2)-(5/2)*L v) := by
        dsimp [L]; ring
      _=(5/2+(35/4)*v+24*v^2)*(inverseRoot v)^5+
          L v*(5*(inverseRoot v)^4*(-1/(2*inverseRoot v))) := by
        rw [←inverseRoot_square hv]
        field_simp [hp.ne']
        ring

theorem scaledLower_derivative {v : ℝ} (hv : v<1) :
    HasDerivAt scaledLower (-(315/32)*v^3*inverseRoot v) v := by
  have hp := inverseRoot_positive hv
  have hh := (L2_derivative v).mul ((inverseRoot_derivative hv).pow 3)
  convert hh using 1
  · rfl
  · calc
      -(315/32)*v^3*inverseRoot v=
          inverseRoot v*((1-v)*(3/2+(15/4)*v+(105/16)*v^2)-(3/2)*L2 v) := by
        dsimp [L2]; ring
      _=(3/2+(15/4)*v+(105/16)*v^2)*(inverseRoot v)^3+
          L2 v*(3*(inverseRoot v)^2*(-1/(2*inverseRoot v))) := by
        rw [←inverseRoot_square hv]
        field_simp [hp.ne']
        ring

theorem scaledUpper_right : (1:ℝ)<scaledUpper (31/250) := by
  have hp := inverseRoot_positive (v:=(31/250:ℝ)) (by norm_num)
  have hs := inverseRoot_square (v:=(31/250:ℝ)) (by norm_num)
  have hL : 0<L (31/250) := by norm_num [L]
  have h0 : 0<scaledUpper (31/250) := mul_pos hL (pow_pos hp 5)
  have hsq : (scaledUpper (31/250))^2=(L (31/250))^2*(219/250:ℝ)^5 := by
    dsimp [scaledUpper]
    rw [mul_pow,←pow_mul,show 5*2=2*5 by norm_num,pow_mul,hs]
    norm_num
  have hh : (1:ℝ)<(L (31/250))^2*(219/250:ℝ)^5 := by norm_num [L]
  nlinarith

theorem inverse_five_upper {v : ℝ} (hv : v∈Icc (0:ℝ) (31/250)) :
    1/(inverseRoot v)^5≤L v := by
  have hinc : MonotoneOn scaledUpper (Icc (0:ℝ) (69/704)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (scaledUpper_derivative (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      exact scaledUpper_derivative (by linarith [hx.2])
    · intro x hx
      exact mul_nonneg (mul_nonneg (pow_nonneg (inverseRoot_positive (by linarith [hx.2])).le 3)
        (sq_nonneg x)) (by linarith [hx.2])
  have hdec : AntitoneOn scaledUpper (Icc (69/704:ℝ) (31/250)) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro x hx
      exact (scaledUpper_derivative (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      exact scaledUpper_derivative (by linarith [hx.2])
    · intro x hx
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg (inverseRoot_positive (by linarith [hx.2])).le 3) (sq_nonneg x))
        (by linarith [hx.1])
  have hscale : 1≤ scaledUpper v := by
    by_cases hh : v≤69/704
    · have ht := hinc ⟨le_rfl,by norm_num⟩ ⟨hv.1,hh⟩ hv.1
      simpa [scaledUpper,L,inverseRoot] using ht
    · exact scaledUpper_right.le.trans (hdec ⟨le_of_not_ge hh,hv.2⟩
        ⟨by norm_num,le_rfl⟩ hv.2)
  exact (div_le_iff₀ (pow_pos (inverseRoot_positive (by linarith [hv.2])) 5)).2 hscale

theorem inverse_three_lower {v : ℝ} (hv : 0≤v) (hv1 : v<1) :
    L2 v≤1/(inverseRoot v)^3 := by
  have hm : AntitoneOn scaledLower (Icc 0 v) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro x hx
      exact (scaledLower_derivative (hx.2.trans_lt hv1)).continuousAt.continuousWithinAt
    · intro x hx
      exact scaledLower_derivative (hx.2.le.trans_lt hv1)
    · intro x hx
      have hroot := inverseRoot_positive (hx.2.le.trans_lt hv1)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hx.1.le 3)) hroot.le
  have hh := hm ⟨le_rfl,hv⟩ ⟨hv,le_rfl⟩ hv
  have hs : scaledLower v≤1 := by simpa [scaledLower,L2,inverseRoot] using hh
  exact (le_div_iff₀ (pow_pos (inverseRoot_positive hv1) 3)).2 hs

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
/-!
## Positive first and third derivatives of the common gain

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
end
end
end

section
/-!
## The degree-150 certificate at actual sine and cosine

The sine
part has degree ten in its sine input. Its exact coefficient norm,
together with a cubic power-difference bound for cosine, gives an
error smaller than the prescribed 10^-8 allowance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary Polynomial HighOrderTaylor BoundedRadicalPerturbation

namespace Certificate
def Y : ℚ[X] := -C (13/6)*X-1-X^2+C (6323/6250)*b pHigh*
  (l2.comp (C (pHigh/(1+pHigh))*X^2))
def yNorm : ℚ := ∑i:Fin 11,|Y.coeff i.val| *i.val*2^i.val

open WholeIntervalPolynomial.Certificate (Scaled)

/-! The degree-ten polynomial `Y` as a scaled integer list (kernel-checked). -/

private def r67_q : Scaled := (Scaled.const (pHigh/(1+pHigh))).mul (Scaled.var.pow 2)
private def r67_Y : Scaled :=
  (((((Scaled.const (13/6)).neg.mul Scaled.var).sub (Scaled.ofNat 1)).sub (Scaled.var.pow 2)).add
    (((Scaled.const (6323/6250)).mul
      (((Scaled.const (1+pHigh)).mul ((Scaled.ofNat 1).add (Scaled.var.pow 2))).sub
        ((Scaled.const (2*pHigh)).mul (Scaled.var.pow 4)))).mul
      ((((Scaled.ofNat 1).add ((Scaled.const (3/2)).mul r67_q)).add
        ((Scaled.const (15/8)).mul (r67_q.pow 2))).add ((Scaled.const (35/16)).mul (r67_q.pow 3)))))

private theorem r67_Y_rep : r67_Y.Rep Y := by
  have hq : r67_q.Rep (C (pHigh/(1+pHigh))*X^2) :=
    (Scaled.rep_const _).mul (Scaled.rep_var.pow 2)
  have hl : l2.comp (C (pHigh/(1+pHigh))*X^2)=1+C (3/2)*(C (pHigh/(1+pHigh))*X^2)+
      C (15/8)*(C (pHigh/(1+pHigh))*X^2)^2+C (35/16)*(C (pHigh/(1+pHigh))*X^2)^3 := by
    simp only [l2,add_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
  rw [Y,b,hl]
  exact ((((Scaled.rep_const _).neg.mul Scaled.rep_var).sub Scaled.rep_one).sub
    (Scaled.rep_var.pow 2)).add
    (((Scaled.rep_const _).mul
      (((Scaled.rep_const _).mul (Scaled.rep_one.add (Scaled.rep_var.pow 2))).sub
        ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4)))).mul
      (((Scaled.rep_one.add ((Scaled.rep_const _).mul hq)).add
        ((Scaled.rep_const _).mul (hq.pow 2))).add ((Scaled.rep_const _).mul (hq.pow 3))))

private theorem r67_Y_facts : r67_Y.s≠0 ∧ r67_Y.l.length≤11 ∧
    (∑i:Fin 11,|r67_Y.l.getD i.val 0| *(i.val:ℤ)*2^i.val)<1000000*(r67_Y.s:ℤ) := by
  decide +kernel

theorem Y_identity : Y=∑i:Fin 11,C (Y.coeff i.val)*X^i.val := by
  obtain ⟨hs,hl,-⟩ := r67_Y_facts
  have hd : Y.natDegree<11 := lt_of_le_of_lt (r67_Y_rep.natDegree_le hs) (by omega)
  conv_lhs => rw [Y.as_sum_range_C_mul_X_pow' hd]
  exact (Fin.sum_univ_eq_sum_range (fun i => C (Y.coeff i)*X^i) 11).symm

theorem Y_norm_bound : yNorm<(1000000:ℚ) := by
  obtain ⟨hs,-,ht⟩ := r67_Y_facts
  have hs' : (0:ℚ)<r67_Y.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have he : yNorm=((∑i:Fin 11,|r67_Y.l.getD i.val 0| *(i.val:ℤ)*2^i.val:ℤ):ℚ)/r67_Y.s := by
    unfold yNorm
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [r67_Y_rep.coeff hs,abs_div,abs_of_pos hs']
    ring
  rw [he,div_lt_iff₀ hs']
  exact_mod_cast ht
end Certificate

def jNative (x y c : ℝ) : ℝ := E2 x*c^3+aeval y Certificate.Y

theorem jNative_formula (x y c : ℝ) :
    jNative x y c=E2 x*c^3-2*K*y-1-y^2+
      (6323/6250)*shapeB (751/1000) y*L2 ((564001/1564001)*y^2) := by
  simp [jNative,Certificate.Y,Certificate.b,Certificate.l2,Certificate.pHigh,shapeB,L2,K]
  ring

theorem polynomial_J_identity (x : ℝ) :
    aeval x Certificate.J=jNative x (S15 x) (C16 x) := by
  simp [Certificate.J,jNative,Certificate.Y,Certificate.e2,Certificate.b,Certificate.l2,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval,E2]
  ring

theorem E2_abs {x : ℝ} (hx : x∈Icc 0 frameCap) : |E2 x|≤1 := by
  let u := x-7/20
  have hu : |u|≤(7/20:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hx.1],by norm_num [frameCap] at hx; linarith [hx.2]⟩
  have hu2 : u^2≤(7/20:ℝ)^2 := by nlinarith [(abs_le.mp hu).1,(abs_le.mp hu).2]
  have hu3 : |u^3|≤(7/20:ℝ)^3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg u) hu 3
  apply abs_le.mpr
  change -1≤-1/250+(33/25)*u-(1/10)*u^2+(19/10)*u^3 ∧
    -1/250+(33/25)*u-(1/10)*u^2+(19/10)*u^3≤1
  constructor <;> nlinarith [(abs_le.mp hu).1,(abs_le.mp hu).2,
    (abs_le.mp hu3).1,(abs_le.mp hu3).2,sq_nonneg u]

theorem power_error {u v ε : ℝ} (hu : |u|≤2) (hv : |v|≤2)
    (hε : 0≤ε) (hd : |u-v|≤ε) (n : ℕ) :
    |u^n-v^n|≤(n:ℝ)*2^n*ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hvp : |v^n|≤(2:ℝ)^n := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg v) hv n
    have hh := product_difference hu hvp hd ih
    have hpow : 0≤(2:ℝ)^n := by positivity
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    simp only [pow_succ,Nat.cast_add,Nat.cast_one] at ⊢
    rw [mul_comm (u^n) u,mul_comm (v^n) v]
    nlinarith [mul_nonneg hpow hε]

theorem Y_error {y t ε : ℝ} (hy : |y|≤2) (ht : |t|≤2)
    (hε : 0≤ε) (hd : |y-t|≤ε) :
    |aeval y Certificate.Y-aeval t Certificate.Y|≤1000000*ε := by
  have hterm (i : Fin 11) :
      |(Certificate.Y.coeff i.val:ℝ)*y^i.val-(Certificate.Y.coeff i.val:ℝ)*t^i.val|≤
        |(Certificate.Y.coeff i.val:ℝ)| *i.val*2^i.val*ε := by
    have hh := constant_product_difference (le_refl |(Certificate.Y.coeff i.val:ℝ)|)
      (power_error hy ht hε hd i.val)
    simpa only [mul_assoc] using hh
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  have hi := Certificate.Y_identity
  have hid (v : ℝ) : aeval v Certificate.Y=∑i:Fin 11,(Certificate.Y.coeff i.val:ℝ)*v^i.val := by
    conv_lhs => rw [hi]
    simp only [map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  rw [hid,hid,←Finset.sum_sub_distrib]
  have hsum := Finset.abs_sum_le_sum_abs (s:=Finset.univ)
    (f:=fun i:Fin 11 => (Certificate.Y.coeff i.val:ℝ)*y^i.val-(Certificate.Y.coeff i.val:ℝ)*t^i.val)
  have hnorm : (Certificate.yNorm:ℝ)<1000000 := by exact_mod_cast Certificate.Y_norm_bound
  have hnorm' : (∑i:Fin 11,|(Certificate.Y.coeff i.val:ℝ)| *i.val*2^i.val)≤1000000 := by
    have he : (Certificate.yNorm:ℝ)=∑i:Fin 11,|(Certificate.Y.coeff i.val:ℝ)| *i.val*2^i.val := by
      simp [Certificate.yNorm]
    rw [← he]
    exact hnorm.le
  have hm := mul_le_mul_of_nonneg_right hnorm' hε
  rw [Finset.sum_mul] at hm
  linarith

theorem J_error {x : ℝ} (hx : x∈Icc 0 frameCap) :
    |jNative x (Real.sin x) (Real.cos x)-aeval x Certificate.J|<(1/100000000:ℝ) := by
  have hb := Analytic.input_bounds hx
  have he := Analytic.input_errors hx
  have habs {v : ℝ} (h : v∈Icc (0:ℝ) 2) : |v|≤2 := by rw [abs_of_nonneg h.1]; exact h.2
  have hsin := habs (v:=Real.sin x) ⟨hb.1.1,by linarith [hb.1.2]⟩
  have hS := habs (v:=S15 x) ⟨hb.2.2.1.1,by linarith [hb.2.2.1.2]⟩
  have hcos := habs (v:=Real.cos x) ⟨by linarith [hb.2.1.1],by linarith [hb.2.1.2]⟩
  have hC := habs (v:=C16 x) ⟨by linarith [hb.2.2.2.1],by linarith [hb.2.2.2.2]⟩
  have hY := Y_error hsin hS (show 0≤remainder by norm_num [remainder]) he.1
  have hp := power_error hcos hC (show 0≤remainder by norm_num [remainder]) he.2 3
  have hE := constant_product_difference (E2_abs hx) hp
  have hid : jNative x (Real.sin x) (Real.cos x)-jNative x (S15 x) (C16 x)=
      (E2 x*Real.cos x^3-E2 x*C16 x^3)+
      (aeval (Real.sin x) Certificate.Y-aeval (S15 x) Certificate.Y) := by dsimp [jNative]; ring
  rw [polynomial_J_identity,hid]
  have hh := abs_add_le (E2 x*Real.cos x^3-E2 x*C16 x^3)
    (aeval (Real.sin x) Certificate.Y-aeval (S15 x) Certificate.Y)
  norm_num [remainder] at hY hE
  linarith

theorem actual_J_positive {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0<jNative x (Real.sin x) (Real.cos x) := by
  have hp := Certificate.J_positive hx
  have he := J_error hx
  have hh := (abs_lt.mp he).1
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
/-!
## The symmetric second-derivative envelope and uncharged allocation

The secant angles range continuously over their complete total
interval. The bound keeps the reserve depending on the unused angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary

theorem B_positive (k : ℝ) {y : ℝ} (hy : y∈Icc (0:ℝ) (129/200)) : 0<shapeB k y := by
  have hy2 : y^2≤(129/200:ℝ)^2 := by nlinarith [hy.1,hy.2]
  have he : shapeB k y=1+y^2+k^2*(1-y^2)*(1+2*y^2) := by dsimp [shapeB]; ring
  rw [he]
  have hp := mul_nonneg (mul_nonneg (sq_nonneg k) (by linarith : 0≤1-y^2))
    (show 0≤1+2*y^2 by positivity)
  linarith [sq_nonneg y]

theorem high_factor {x : ℝ} (hx : x∈Icc 0 frameCap) :
    D (751/1000) x=Real.sqrt (1564001/1000000)*
      inverseRoot ((564001/1564001)*Real.sin x^2) := by
  have hy := sine_domain hx
  have hv : (564001/1564001)*Real.sin x^2<1 := by nlinarith [hy.1,hy.2]
  have hS : 0<Real.sqrt (1564001/1000000:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hS2 := Real.sq_sqrt (show (0:ℝ)≤1564001/1000000 by norm_num)
  have hv2 := inverseRoot_square hv
  have hp := mul_pos hS (inverseRoot_positive hv)
  have he : (Real.sqrt (1564001/1000000:ℝ)*inverseRoot ((564001/1564001)*Real.sin x^2))^2=
      (D (751/1000) x)^2 := by rw [mul_pow,hS2,hv2,D_shape]; dsimp [shapeA]; ring
  nlinarith [D_positive (751/1000) x]

theorem high_radius_ratio : (6323/6250:ℝ)<R/(Real.sqrt (1564001/1000000:ℝ))^3 := by
  have hs : 0<Real.sqrt (1564001/1000000:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤1564001/1000000 by norm_num)
  have hs6 : (Real.sqrt (1564001/1000000:ℝ)^3)^2=(1564001/1000000:ℝ)^3 := by
    rw [←pow_mul,show 3*2=2*3 by norm_num,pow_mul,hs2]
  have hr : R^2=9789/2500 := Secondary.radius_sq
  have hsq : ((6323/6250)*Real.sqrt (1564001/1000000:ℝ)^3)^2<R^2 := by
    rw [mul_pow,hs6,hr]
    norm_num
  have hbound := lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) hsq
  exact (lt_div_iff₀ (pow_pos hs 3)).2 hbound

theorem high_inverse_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (6323/6250)*L2 ((564001/1564001)*Real.sin x^2)<R/(D (751/1000) x)^3 := by
  let v := (564001/1564001)*Real.sin x^2
  have hy := sine_domain hx
  have hv : 0≤v := by dsimp [v]; positivity
  have hv1 : v<1 := by dsimp [v]; nlinarith [hy.1,hy.2]
  have hL := inverse_three_lower hv hv1
  have hroot := inverseRoot_positive hv1
  have hfirst := mul_le_mul_of_nonneg_left hL (show (0:ℝ)≤6323/6250 by norm_num)
  have hsecond := mul_lt_mul_of_pos_right high_radius_ratio
    (show 0<1/(inverseRoot v)^3 by positivity)
  have hh := hfirst.trans_lt hsecond
  rw [high_factor hx,mul_pow]
  calc (6323/6250)*L2 ((564001/1564001)*Real.sin x^2)
      <R/(Real.sqrt (1564001/1000000:ℝ))^3*(1/(inverseRoot v)^3) := hh
    _=R/((Real.sqrt (1564001/1000000:ℝ))^3*(inverseRoot ((564001/1564001)*Real.sin x^2))^3) := by
      rw [div_mul_div_comm,mul_one]

theorem second_envelope {x : ℝ} (hx : x∈Icc 0 frameCap) : F2 (751/1000) x<E2 x := by
  have hj := actual_J_positive hx
  rw [jNative_formula] at hj
  have hB := B_positive (751/1000) (sine_domain hx)
  have hr := mul_lt_mul_of_pos_right (high_inverse_lower hx) hB
  have hc : 0<Real.cos x := by linarith [(transport_trig hx).1]
  dsimp [F2]
  apply (div_lt_iff₀ (pow_pos hc 3)).2
  have he : R*shapeB (751/1000) (Real.sin x)/(D (751/1000) x)^3=
      (R/(D (751/1000) x)^3)*shapeB (751/1000) (Real.sin x) := by ring
  rw [he]
  nlinarith

theorem symmetric_envelope (x : ℝ) :
    E2 x+E2 (frameCap-x)= -1/125-(1/5)*(x-7/20)^2 := by
  dsimp [E2,frameCap]
  ring

theorem second_sum {k r s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (ht : r+s≤frameCap) :
    F2 k r+F2 k s< -1/125-(11/10)*(frameCap-r-s) := by
  have hr' : r∈Icc 0 frameCap := ⟨hr,by linarith⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs,by linarith⟩
  have hc' : frameCap-r∈Icc 0 frameCap := ⟨by linarith [hr'.2],by linarith⟩
  have hmr := (parameter_monotonicity hr').2.1 hk ⟨by norm_num,le_rfl⟩ hk.2
  have hms := (parameter_monotonicity hs').2.1 hk ⟨by norm_num,le_rfl⟩ hk.2
  have hg := derivative_reserve
    (f:=F2 (751/1000)) (df:=F3 (751/1000))
    (l:=0) (u:=frameCap) (k:=(11/10:ℝ))
    (fun x hx => (F2_derivative (k:=(751/1000:ℝ)) hx).continuousAt.continuousWithinAt)
    (fun x hx => F2_derivative (Ioo_subset_Icc_self hx))
    (fun x hx => (third_lower (show (751/1000:ℝ)∈Icc (13/20:ℝ) (751/1000) by norm_num)
      (Ioo_subset_Icc_self hx)).le)
    hs' hc' (by linarith)
  have hleft := second_envelope hr'
  have hright := second_envelope hc'
  have he := symmetric_envelope r
  nlinarith [sq_nonneg (r-7/20)]

theorem second_negative_short {k x : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hx : x∈Icc (0:ℝ) (3/20)) : F2 k x<0 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,by norm_num [frameCap]; linarith [hx.2]⟩
  have hm := (parameter_monotonicity hx').2.1 hk ⟨by norm_num,le_rfl⟩ hk.2
  have he := second_envelope hx'
  have hu : x-7/20≤0 := by linarith [hx.2]
  have hc : (x-7/20)^3≤0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x-7/20)) hu
    simpa only [pow_succ] using hh
  have hE : E2 x<0 := by dsimp [E2]; nlinarith [sq_nonneg (x-7/20)]
  linarith

theorem growth {k x y : ℝ} (hk : (13/20:ℝ)≤k)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (9/10)*(y-x)≤F k y-F k x := by
  exact derivative_reserve (f:=F k) (df:=F1 k)
    (fun t ht => (F_derivative (k:=k) ht).continuousAt.continuousWithinAt)
    (fun t ht => F_derivative (Ioo_subset_Icc_self ht))
    (fun t ht => (first_lower hk (Ioo_subset_Icc_self ht)).le) hx hy hxy

theorem merge_concave {k S : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hS : S∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 S) (fun r => F k r+F k (S-r)) := by
  have hd (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F k r+F k (S-r)) (F1 k r-F1 k (S-r)) r := by
    have hleft := F_derivative (k:=k) ⟨hr.1,hr.2.trans hS.2⟩
    have hright := (F_derivative (k:=k) (x:=S-r) ⟨by linarith [hr.2],by linarith [hS.2,hr.1]⟩).comp r
      ((hasDerivAt_id' r).const_sub S)
    exact (hleft.fun_add hright).congr_deriv (by ring)
  have hdd (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F1 k r-F1 k (S-r)) (F2 k r+F2 k (S-r)) r := by
    have hleft := F1_derivative (k:=k) ⟨hr.1,hr.2.trans hS.2⟩
    have hright := (F1_derivative (k:=k) (x:=S-r) ⟨by linarith [hr.2],by linarith [hS.2,hr.1]⟩).comp r
      ((hasDerivAt_id' r).const_sub S)
    exact (hleft.fun_sub hright).congr_deriv (by ring)
  apply concave_of_deriv2 hd hdd
  intro r hr
  have hh := second_sum hk hr.1 (show 0≤S-r by linarith [hr.2]) (by linarith [hS.2])
  have hS2 := hS.2
  simp only [frameCap] at hh hS2
  linarith

theorem merge {k r s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (ht : r+s≤frameCap) :
    F k (r+s)≤F k r+F k s := by
  have hc := merge_concave hk ⟨add_nonneg hr hs,ht⟩
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,add_nonneg hr hs⟩
    ⟨add_nonneg hr hs,le_rfl⟩ (show r∈Icc 0 (r+s) by exact ⟨hr,by linarith⟩)
  simpa only [F_zero,zero_add,sub_zero,sub_self,add_zero,add_sub_cancel_left,min_self] using hh

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
/-!
## The larger-coefficient derivative on the common-gain rectangle

`VaryingBFunctions.D` is the
actual derivative of V with respect to its larger coefficient. The
slightly wider ratio interval contains k/sec r for every r≤.7.
The derivative in d is controlled before and after its intrinsic
zero-sign event sin d=k/q; no subdivision of the angle is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary OrdinaryCurvatureBounds OrdinaryAngleConcavity
open VaryingBFunctions VaryingBComparison

def varyingShape (ρ u : ℝ) : ℝ :=
  (2*ρ^2-1)+(u-ρ)*u*(ρ^2+2-ρ*u)-ρ^2*u^2

theorem varying_ratio_condition {ρ u : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000))
    (hu : u∈Icc (0:ℝ) (129/200)) : 0≤2*ρ-(1+ρ^2)*u := by
  have hfactor := mul_nonneg (show 0≤ρ-49/100 by linarith [hρ.1])
    (show 0≤2-(129/200)*(ρ+49/100) by linarith [hρ.2])
  have hh := mul_le_mul_of_nonneg_left hu.2 (show 0≤1+ρ^2 by positivity)
  nlinarith

theorem varying_Dr_nonnegative {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap) :
    0≤Dr R ρ d := by
  let u := Real.sin d
  have hu := sine_domain hd
  have hu' := sin_mem hd
  have hN := root_pos ρ hu'
  have hN2 := root_sq ρ hu'
  have hS := shape_pos ρ
  have hS2 := shape_sq ρ
  have hu2 : u^2≤(129/200:ℝ)^2 := by dsimp [u]; nlinarith [hu.1,hu.2]
  have hcondition := mul_nonneg (varying_ratio_condition hρ hu) hu.1
  have hbase : (root ρ u)^2≤(1+ρ^2)*(1-u^2) := by
    dsimp [u] at *
    nlinarith
  have hcube := pow_le_pow_left₀ (sq_nonneg (root ρ u)) hbase 3
  have h01 : 0≤1-u^2 ∧ 1-u^2≤1 := ⟨by linarith,by nlinarith [sq_nonneg u]⟩
  have hpow : (1-u^2)^3≤(1-u^2)^2 := by
    have hh := mul_le_mul_of_nonneg_left h01.2 (sq_nonneg (1-u^2))
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hpow (show 0≤(1+ρ^2)^3 by positivity)
  have hsquare : ((root ρ u)^3)^2≤((1-u^2)*(shape ρ)^3)^2 := by
    rw [show ((root ρ u)^3)^2=((root ρ u)^2)^3 by ring,
      show ((1-u^2)*(shape ρ)^3)^2=(1-u^2)^2*((shape ρ)^2)^3 by ring,hS2]
    nlinarith only [hcube,hprod]
  have hle : (root ρ u)^3≤(1-u^2)*(shape ρ)^3 := by
    nlinarith [pow_nonneg hN.le 3,mul_nonneg h01.1 (pow_nonneg hS.le 3)]
  have hfrac : 1/(shape ρ)^3≤(1-u^2)/(root ρ u)^3 :=
    (div_le_div_iff₀ (pow_pos hS 3) (pow_pos hN 3)).2 (by simpa using hle)
  dsimp [Dr]
  rw [cos_square]
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (by linarith [hρ.1]))
    (sub_nonneg.mpr hfrac)

theorem varying_Dtt_identity {ρ d : ℝ} (hd : d∈Icc 0 frameCap) :
    Dtt R ρ d= -Real.cos d+R*ρ^2*varyingShape ρ (Real.sin d)/(root ρ (Real.sin d))^5 := by
  have hn := (root_pos ρ (sin_mem hd)).ne'
  have hN2 := root_sq ρ (sin_mem hd)
  have h3 : ρ^2*(ρ-Real.sin d)/(root ρ (Real.sin d))^3=
      ρ^2*(ρ-Real.sin d)*(1+ρ^2-2*ρ*Real.sin d)/(root ρ (Real.sin d))^5 := by
    rw [← hN2]; field_simp
  dsimp [Dtt,integrand,integrandD,varyingShape]
  rw [h3,cos_square]
  ring

theorem varying_shape_upper {ρ u : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000))
    (hu : u∈Icc (0:ℝ) (129/200)) (hur : u≤ρ) : varyingShape ρ u≤129/1000 := by
  have hρ0 : 0≤ρ := by linarith [hρ.1]
  have hρ2 : ρ^2≤(751/1000:ℝ)^2 := pow_le_pow_left₀ hρ0 hρ.2 2
  have hprod := mul_le_mul_of_nonneg_left hur hρ0
  have hb : 0≤ρ^2+2-ρ*u := by linarith
  have hbad := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hur) hu.1) hb
  have hsquare := mul_nonneg (sq_nonneg ρ) (sq_nonneg u)
  dsimp [varyingShape]
  nlinarith

theorem varying_Dtt_negative {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap)
    (hsin : Real.sin d≤ρ) : Dtt R ρ d<0 := by
  have hy := sine_domain hd
  have hN := root_pos ρ (sin_mem hd)
  have hN2 := root_sq ρ (sin_mem hd)
  have hNlow : (191/250:ℝ)<root ρ (Real.sin d) := by
    nlinarith [sq_nonneg (ρ-Real.sin d),hy.1,hy.2]
  have hc : (191/250:ℝ)<Real.cos d := by linarith [(transport_trig hd).1]
  have hshape := varying_shape_upper hρ hy hsin
  rw [varying_Dtt_identity hd]
  by_cases hs : varyingShape ρ (Real.sin d)≤0
  · have hh := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Real.sqrt_nonneg qCap) (sq_nonneg ρ)) hs)
      (pow_nonneg hN.le 5)
    linarith
  · have hs0 : 0≤varyingShape ρ (Real.sin d) := le_of_lt (lt_of_not_ge hs)
    have hr : R≤2 := by linarith [Secondary.radius_bounds.2]
    have hρ2 : ρ^2≤(751/1000:ℝ)^2 :=
      pow_le_pow_left₀ (by linarith [hρ.1]) hρ.2 2
    have hprod := mul_le_mul (mul_le_mul hr hρ2 (sq_nonneg ρ) (by norm_num))
      hshape hs0 (by norm_num : (0:ℝ)≤2*(751/1000)^2)
    have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤191/250) hNlow.le 5
    have hfrac : R*ρ^2*varyingShape ρ (Real.sin d)/(root ρ (Real.sin d))^5<191/250 := by
      apply (div_lt_iff₀ (pow_pos hN 5)).2
      nlinarith
    linarith

theorem varying_Dt_upper {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap) :
    Dt R ρ d≤R*ρ^3/(shape ρ)^3 := by
  have hρ0 : 0≤ρ := by linarith [hρ.1]
  by_cases hsin : Real.sin d≤ρ
  · have hmono : AntitoneOn (Dt R ρ) (Icc 0 d) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact (Dt_hasDerivAt (R:=R) (r:=ρ) ⟨hx.1,hx.2.trans hd.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact Dt_hasDerivAt ⟨hx.1.le,hx.2.le.trans hd.2⟩
      · intro x hx
        have hx' : x∈Icc 0 frameCap := ⟨hx.1.le,hx.2.le.trans hd.2⟩
        have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [hx.1,Real.pi_pos])
          (by norm_num [frameCap] at hd; linarith [hd.2,Real.pi_gt_three]) hx.2.le
        exact (varying_Dtt_negative hρ hx' (hs.trans hsin)).le
    have hh := hmono ⟨le_rfl,hd.1⟩ ⟨hd.1,le_rfl⟩ hd.1
    simpa [Dt,integrand,pow_succ,mul_div_assoc] using hh
  · have hsign : integrand ρ (Real.sin d)≤0 := by
      dsimp [integrand]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ρ) (by linarith))
        (pow_nonneg (root_pos ρ (sin_mem hd)).le 3)
    have hprod := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.sqrt_nonneg qCap) (show 0≤Real.cos d by linarith [(transport_trig hd).1])) hsign
    have hright : 0≤R*ρ^3/(shape ρ)^3 :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (pow_nonneg hρ0 3)) (pow_nonneg (shape_pos ρ).le 3)
    dsimp [Dt]
    linarith [(sine_domain hd).1]

theorem varying_D_upper {ρ d : ℝ}
    (hρ : ρ∈Icc (49/100:ℝ) (751/1000)) (hd : d∈Icc 0 frameCap) :
    VaryingBFunctions.D R ρ d≤R*ρ^3/(shape ρ)^3*d := by
  have hh := derivative_reserve
    (f:=fun x => -VaryingBFunctions.D R ρ x) (df:=fun x => -Dt R ρ x)
    (k:=-(R*ρ^3/(shape ρ)^3)) (l:=0) (u:=frameCap)
    (fun x hx => (D_hasDerivAt_t (R:=R) (r:=ρ) hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (D_hasDerivAt_t (R:=R) (r:=ρ) (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (varying_Dt_upper hρ (Ioo_subset_Icc_self hx)))
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hd hd.1
  simp only [D_zero,neg_zero,sub_zero] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
/-!
## Secant curvature and continuous allocation of both negative angles

The coefficient bound is proved by its two positive parameter
derivatives and the prescribed positive-square corner comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary OrdinaryCurvatureBounds OrdinaryAngleConcavity
open VaryingBFunctions VaryingBComparison SecantNormCurvature

def coefficientNorm (k q : ℝ) : ℝ := Real.sqrt (k^2+q^2)
def secantCoefficient (k q : ℝ) : ℝ :=
  R*k^3*q*(2*q^2-1)/(coefficientNorm k q)^3
def chargedFirst (k d r : ℝ) : ℝ := VaryingBFunctions.D R (k/secant r) d*first r
def chargedSecond (k d r : ℝ) : ℝ :=
  Dr R (k/secant r) d*(-k/(secant r)^2)*(first r)^2+
    VaryingBFunctions.D R (k/secant r) d*second r

theorem coefficientNorm_positive {k q : ℝ} (hk : 0<k) : 0<coefficientNorm k q :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg q])
theorem coefficientNorm_square (k q : ℝ) : (coefficientNorm k q)^2=k^2+q^2 :=
  Real.sq_sqrt (by positivity)

theorem coefficientNorm_k_derivative {k q : ℝ} (hq : 0<q) :
    HasDerivAt (fun k => coefficientNorm k q) (k/coefficientNorm k q) k := by
  have hn : k^2+q^2≠0 := by positivity
  refine (((hasDerivAt_id' k).fun_pow 2).add_const (q^2)).sqrt hn |>.congr_deriv ?_
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  rw [coefficientNorm]
  field_simp
theorem coefficientNorm_q_derivative {k q : ℝ} (hk : 0<k) :
    HasDerivAt (coefficientNorm k) (q/coefficientNorm k q) q := by
  have hn : k^2+q^2≠0 := by positivity
  refine (((hasDerivAt_id' q).fun_pow 2).const_add (k^2)).sqrt hn |>.congr_deriv ?_
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  rw [coefficientNorm]
  field_simp

theorem coefficient_k_derivative {k q : ℝ} (hk : 0<k) (hq : 0<q) :
    HasDerivAt (fun k => secantCoefficient k q)
      (3*R*k^2*q^3*(2*q^2-1)/(coefficientNorm k q)^5) k := by
  have hn := (coefficientNorm_positive (q:=q) hk).ne'
  have hd := (((((hasDerivAt_id' k).fun_pow 3).const_mul R).mul_const q).mul_const
    (2*q^2-1)).fun_div ((coefficientNorm_k_derivative hq).fun_pow 3) (pow_ne_zero _ hn)
  refine hd.congr_deriv ?_
  rw [show 3*R*k^2*q^3*(2*q^2-1)/(coefficientNorm k q)^5=
      3*R*k^2*q*(2*q^2-1)*((coefficientNorm k q)^2-k^2)/(coefficientNorm k q)^5 by
    rw [coefficientNorm_square]; ring]
  simp only [Nat.cast_ofNat,Nat.reduceSub,mul_one]
  field_simp

theorem coefficient_q_derivative {k q : ℝ} (hk : 0<k) :
    HasDerivAt (secantCoefficient k)
      (R*k^3*(2*q^2+(6*q^2-1)*k^2)/(coefficientNorm k q)^5) q := by
  have hn := (coefficientNorm_positive (q:=q) hk).ne'
  have hd := (((hasDerivAt_id' q).const_mul (R*k^3)).fun_mul
    ((((hasDerivAt_id' q).fun_pow 2).const_mul 2).sub_const 1)).fun_div
      ((coefficientNorm_q_derivative hk).fun_pow 3) (pow_ne_zero _ hn)
  refine hd.congr_deriv ?_
  rw [show R*k^3*(2*q^2+(6*q^2-1)*k^2)/(coefficientNorm k q)^5=
      R*k^3*((6*q^2-1)*(coefficientNorm k q)^2-3*q^2*(2*q^2-1))/(coefficientNorm k q)^5 by
    rw [coefficientNorm_square]; ring]
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  field_simp
  ring

theorem coefficient_corner : secantCoefficient (751/1000) (327/250)<(39/50:ℝ) := by
  have hn := coefficientNorm_positive (q:=(327/250:ℝ)) (show (0:ℝ)<751/1000 by norm_num)
  dsimp [secantCoefficient]
  apply quotient_lt_of_square (pow_pos hn 3) (by norm_num)
  have hN6 : ((coefficientNorm (751/1000) (327/250))^3)^2=
      ((751/1000:ℝ)^2+(327/250)^2)^3 := by
    rw [show ((coefficientNorm (751/1000) (327/250))^3)^2=
      ((coefficientNorm (751/1000) (327/250))^2)^3 by ring,coefficientNorm_square]
  have hr : R^2=9789/2500 := Secondary.radius_sq
  rw [hN6,mul_pow,mul_pow,mul_pow,hr]
  norm_num

theorem coefficient_upper {k q : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hq : q∈Icc (1:ℝ) (327/250)) :
    secantCoefficient k q<(39/50:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq0 : 0<q := by linarith [hq.1]
  have hmK : MonotoneOn (fun k => secantCoefficient k q) (Icc (13/20:ℝ) (751/1000)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (coefficient_k_derivative (by linarith [hx.1]) hq0).continuousAt.continuousWithinAt
    · intro x hx
      exact coefficient_k_derivative (by linarith [hx.1]) hq0
    · intro x hx
      have hq2 : 0≤2*q^2-1 := by nlinarith [hq.1]
      have hx0 : 0<x := by linarith [hx.1]
      exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (Real.sqrt_nonneg qCap)) (sq_nonneg x)) (pow_nonneg hq0.le 3)) hq2)
        (pow_nonneg (coefficientNorm_positive (q:=q) hx0).le 5)
  have hmQ : MonotoneOn (secantCoefficient (751/1000)) (Icc (1:ℝ) (327/250)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (coefficient_q_derivative (q:=x) (by norm_num : (0:ℝ)<751/1000)).continuousAt.continuousWithinAt
    · intro x hx
      exact coefficient_q_derivative (by norm_num : (0:ℝ)<751/1000)
    · intro x hx
      have hx2 : 0≤6*x^2-1 := by nlinarith [hx.1]
      exact div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (by norm_num))
        (by nlinarith)) (pow_nonneg (coefficientNorm_positive (q:=x)
          (show (0:ℝ)<751/1000 by norm_num)).le 5)
  exact ((hmK hk ⟨by norm_num,le_rfl⟩ hk.2).trans
    (hmQ hq ⟨by norm_num,le_rfl⟩ hq.2)).trans_lt coefficient_corner

theorem full_secant_domain {r : ℝ} (hr : r∈Icc 0 frameCap) :
    secant r∈Icc (1:ℝ) (327/250) := by
  have hc : 0<Real.cos r := by linarith [(transport_trig hr).1]
  refine ⟨secant_ge_one hc,?_⟩
  dsimp [secant]
  apply (div_le_iff₀ hc).2
  nlinarith [(transport_trig hr).1]

theorem secant_ratio_domain {k r : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hr : r∈Icc 0 frameCap) :
    k/secant r∈Icc (49/100:ℝ) (751/1000) := by
  have hq := full_secant_domain hr
  have hq0 : 0<secant r := by linarith [hq.1]
  exact ⟨(le_div_iff₀ hq0).2 (by linarith [hq.2,hk.1]),
    (div_le_iff₀ hq0).2 (by nlinarith [hq.1,hk.2])⟩

theorem second_identity {r : ℝ} (hr : r∈Icc 0 frameCap) :
    second r=secant r*(2*(secant r)^2-1) := by
  have hc : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  dsimp [second,secant]
  field_simp [hc]
  nlinarith only [Real.sin_sq_add_cos_sq r]

theorem normalized_coefficient {k q : ℝ} (hq : 0<q) :
    R*(k/q)^3/(shape (k/q))^3*(q*(2*q^2-1))=secantCoefficient k q := by
  have hnorm : coefficientNorm k q=q*shape (k/q) := by
    simpa [coefficientNorm,PositiveAngularEnvelope.pairNorm,
      PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct] using
      negativeNorm_normalized (l:=k) (t:=0) hq
  dsimp [secantCoefficient]
  rw [hnorm]
  field_simp [hq.ne',(shape_pos (k/q)).ne']

theorem charged_derivative {k d r : ℝ} (hk : 0<k)
    (hd : d∈Icc 0 frameCap) (hr : r∈Icc 0 frameCap) :
    HasDerivAt (fun r => V R k (secant r) d) (chargedFirst k d r) r := by
  have hc : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  have hq : 0<secant r := by linarith [(full_secant_domain hr).1]
  exact (V_hasDerivAt_q (R:=R) hk hq hd).comp r (secant_hasDerivAt hc)

theorem chargedFirst_derivative {k d r : ℝ} (_hk : 0<k)
    (hd : d∈Icc 0 frameCap) (hr : r∈Icc 0 frameCap) :
    HasDerivAt (chargedFirst k d) (chargedSecond k d r) r := by
  have hc : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  have hq : 0<secant r := by linarith [(full_secant_domain hr).1]
  have hh := ((OrdinaryNegativeEnvelope.D_quotient_hasDerivAt (R:=R) (p:=k) hq hd).comp r
    (secant_hasDerivAt hc)).mul (first_hasDerivAt hc)
  convert hh using 1
  · rfl
  · dsimp [chargedSecond]
    ring

theorem charged_curvature {k d r : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hd : d∈Icc 0 frameCap) (hr : r∈Icc 0 frameCap) :
    chargedSecond k d r≤(39/50)*d := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq := full_secant_domain hr
  have hq0 : 0<secant r := by linarith [hq.1]
  have hρ := secant_ratio_domain hk hr
  have hDr := varying_Dr_nonnegative hρ hd
  have hD := varying_D_upper hρ hd
  have hq2 : 0≤ second r := by rw [second_identity hr]; nlinarith [hq.1]
  have hfirst : Dr R (k/secant r) d*(-k/(secant r)^2)*(first r)^2≤0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hDr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) (sq_nonneg _))) (sq_nonneg _)
  have hsecond := mul_le_mul_of_nonneg_right hD hq2
  have he : R*(k/secant r)^3/(shape (k/secant r))^3*d*second r=
      secantCoefficient k (secant r)*d := by
    rw [second_identity hr,←normalized_coefficient hq0]
    ring
  rw [he] at hsecond
  have hcoeff := mul_le_mul_of_nonneg_right (coefficient_upper hk hq).le hd.1
  dsimp [chargedSecond]
  linarith

theorem charged_allocation_concave {k S d : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hS : 0≤S) (hd : 0≤d)
    (hbudget : S+d≤frameCap) :
    ConcaveOn ℝ (Icc 0 S) (fun r => F k r+F k (S-r)+V R k (secant r) d) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hd' : d∈Icc 0 frameCap := ⟨hd,by linarith⟩
  have domains (r : ℝ) (hr : r∈Icc 0 S) : r∈Icc 0 frameCap ∧ S-r∈Icc 0 frameCap :=
    ⟨⟨hr.1,by linarith [hr.2]⟩,⟨by linarith [hr.2],by linarith [hr.1]⟩⟩
  have hf (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F k r+F k (S-r)+V R k (secant r) d)
        (F1 k r-F1 k (S-r)+chargedFirst k d r) r := by
    have hleft := F_derivative (k:=k) (domains r hr).1
    have hright := (F_derivative (k:=k) (domains r hr).2).comp r ((hasDerivAt_id' r).const_sub S)
    exact ((hleft.fun_add hright).fun_add (charged_derivative hk0 hd' (domains r hr).1)).congr_deriv
      (by ring)
  have hf' (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F1 k r-F1 k (S-r)+chargedFirst k d r)
        (F2 k r+F2 k (S-r)+chargedSecond k d r) r := by
    have hleft := F1_derivative (k:=k) (domains r hr).1
    have hright := (F1_derivative (k:=k) (domains r hr).2).comp r ((hasDerivAt_id' r).const_sub S)
    exact ((hleft.fun_sub hright).fun_add
      (chargedFirst_derivative hk0 hd' (domains r hr).1)).congr_deriv (by ring)
  apply concave_of_deriv2 hf hf'
  intro r hr
  have hs := second_sum hk hr.1 (show 0≤S-r by linarith [hr.2])
    (show r+(S-r)≤frameCap by linarith)
  have hv := charged_curvature hk hd' (domains r hr).1
  simp only [frameCap] at hs hbudget
  linarith

theorem merge_charged {k r s d : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (hd : 0≤d) (ht : r+s+d≤frameCap) :
    F k (r+s)+min (V R k 1 d) (V R k (secant (r+s)) d)≤
      F k r+F k s+V R k (secant r) d := by
  have hc := charged_allocation_concave hk (add_nonneg hr hs) hd ht
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,add_nonneg hr hs⟩
    ⟨add_nonneg hr hs,le_rfl⟩ (show r∈Icc 0 (r+s) from ⟨hr,by linarith⟩)
  have hsec0 : secant 0=1 := by simp [secant]
  simp only [F_zero,zero_add,sub_zero,sub_self,add_zero,add_sub_cancel_left,hsec0] at hh
  rwa [min_add_add_left] at hh

theorem merge_charged_right {k r s d : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (hd : 0≤d) (ht : r+s+d≤frameCap) :
    F k (r+s)+min (V R k 1 d) (V R k (secant (r+s)) d)≤
      F k r+F k s+V R k (secant s) d := by
  have hh := merge_charged hk hs hr hd (show s+r+d≤frameCap by linarith)
  simpa only [add_comm s r,add_comm (F k s) (F k r)] using hh

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
/-!
## The two endpoint slopes in the common-gain endpoint principle

Alternating sine and cosine brackets give the two strict upper bounds of `F1` at the angles
`3/20` and `7/10` (`EndpointSlope.endpoint`); the convexity of F′ covers the whole interval
(`first_upper_long`). `zero_slope_lower` bounds the slope at `0`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary OrdinaryCurvatureBounds OrdinaryNegativeSlope
open OrdinaryAngleConcavity PairNormCalculus VaryingBFunctions
open NegativeAPositiveTD.NegativeSlope

namespace EndpointSlope
def angle : Fin 2→ℚ := ![3/20,7/10]
def rootUpper : Fin 2→ℚ := ![249111/200000,1153227/1000000]
def upper : Fin 2→ℚ := ![103/100,133/125]
def numeratorUpper (i : Fin 2) : ℚ := 13/12+sinHi (angle i)-upper i*(cosLo (angle i))^2

theorem data (i : Fin 2) :
    (0:ℚ)<rootUpper i ∧ 0<upper i ∧ 0≤ sinLo (angle i) ∧ 0<cosLo (angle i) ∧
    0<cosHi (angle i) ∧ 0<numeratorUpper i ∧
    1+(751/1000:ℚ)^2*(cosHi (angle i))^2<(rootUpper i)^2 ∧
    numeratorUpper i*rootUpper i<(1978787/1000000:ℚ)*sinLo (angle i) := by
  fin_cases i <;> norm_num [angle,rootUpper,upper,numeratorUpper,
    sinLo,sinHi,cosLo,cosHi,PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,
    PositiveTD.Certificate.S5,PositiveTD.Certificate.C10,PositiveTD.Certificate.C12,
    PositiveTD.Certificate.C4]

theorem domain (i : Fin 2) : (angle i:ℝ)∈Icc 0 frameCap := by
  fin_cases i <;> norm_num [angle,frameCap]

theorem endpoint (i : Fin 2) : F1 (751/1000) (angle i)<(upper i:ℝ) := by
  obtain ⟨d1,d2,d3,d4,-,d6,d7,d8⟩ := data i
  have c1 : (0:ℝ)<(rootUpper i:ℝ) := by exact_mod_cast d1
  have c2 : (0:ℝ)<(upper i:ℝ) := by exact_mod_cast d2
  have c3 : (0:ℝ)≤(sinLo (angle i):ℝ) := by exact_mod_cast d3
  have c4 : (0:ℝ)<(cosLo (angle i):ℝ) := by exact_mod_cast d4
  have c6 : (0:ℝ)<(numeratorUpper i:ℝ) := by exact_mod_cast d6
  have c7 : 1+(751/1000:ℝ)^2*(cosHi (angle i):ℝ)^2<(rootUpper i:ℝ)^2 := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr d7
    push_cast at h
    exact h
  have c8 : (numeratorUpper i:ℝ)*(rootUpper i:ℝ)<(1978787/1000000:ℝ)*(sinLo (angle i):ℝ) := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr d8
    push_cast at h
    exact h
  obtain ⟨hsl,hsh,hcl,hch⟩ := rational_taylor (domain i)
  have hcos : 0<Real.cos (angle i:ℝ) := c4.trans_le hcl
  have hN := D_positive (751/1000) (angle i)
  have hN2 := D_square (751/1000) (angle i)
  have hcos2 := pow_le_pow_left₀ hcos.le hch 2
  have hNsq : (D (751/1000) (angle i))^2<(rootUpper i:ℝ)^2 := by
    rw [hN2]
    linarith [mul_le_mul_of_nonneg_left hcos2 (by norm_num : (0:ℝ)≤(751/1000)^2)]
  have hNup : D (751/1000) (angle i)<(rootUpper i:ℝ) := lt_of_pow_lt_pow_left₀ 2 c1.le hNsq
  have hlo2 := pow_le_pow_left₀ c4.le hcl 2
  have hbr : K+Real.sin (angle i)-(upper i:ℝ)*Real.cos (angle i)^2≤(numeratorUpper i:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlo2 c2.le
    dsimp [numeratorUpper,K]
    push_cast
    linarith
  have hfirst := mul_le_mul_of_nonneg_right hbr hN.le
  have hsecond := mul_lt_mul_of_pos_left hNup c6
  have hthird := mul_le_mul radius_tight.1.le hsl c3 (Real.sqrt_nonneg _)
  have hcross : (K+Real.sin (angle i)-(upper i:ℝ)*Real.cos (angle i)^2)*
      D (751/1000) (angle i)<R*Real.sin (angle i) := by
    linarith [c8]
  have hdiv := (lt_div_iff₀ hN).2 hcross
  dsimp [F1]
  apply (div_lt_iff₀ (sq_pos_of_pos hcos)).2
  linarith
end EndpointSlope

theorem first_upper_long {k t : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc (3/20:ℝ) frameCap) : F1 k t<(133/125:ℝ) := by
  have hdomain {x : ℝ} (hx : x∈Icc (3/20:ℝ) frameCap) : x∈Icc 0 frameCap :=
    ⟨by linarith [hx.1],hx.2⟩
  have hc : ConcaveOn ℝ (Icc (3/20:ℝ) frameCap) (fun x => -F1 (751/1000) x) := by
    apply concave_of_deriv2
      (fun x hx => (F1_derivative (k:=(751/1000:ℝ)) (hdomain hx)).neg)
      (fun x hx => (F2_derivative (k:=(751/1000:ℝ)) (hdomain hx)).neg)
    intro x hx
    have hh := third_lower (show (751/1000:ℝ)∈Icc (13/20:ℝ) (751/1000) by norm_num) (hdomain hx)
    linarith
  have hl := EndpointSlope.endpoint 0
  have hr := EndpointSlope.endpoint 1
  norm_num [EndpointSlope.angle,EndpointSlope.upper,frameCap] at hl hr
  have hh := concave_gt_of_endpoints hc ht
    (show -(133/125:ℝ)< -F1 (751/1000) (3/20) by linarith)
    (show -(133/125:ℝ)< -F1 (751/1000) frameCap by simpa [frameCap] using neg_lt_neg hr)
  have hm := (parameter_monotonicity (hdomain ht)).1 hk ⟨by norm_num,le_rfl⟩ hk.2
  linarith

theorem zero_slope_lower {k : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000)) :
    (539/500:ℝ)<Vd R k 1 0 := by
  have hlow : (539/500:ℝ)<NegativeAPositiveTD.Curvature.shapeD0q (13/20) := by
    have hs := shape_pos (13/20:ℝ)
    have hs2 := shape_sq (13/20:ℝ)
    have hr : R^2=9789/2500 := Secondary.radius_sq
    dsimp [NegativeAPositiveTD.Curvature.shapeD0q]
    apply (lt_div_iff₀ hs).2
    have hsq : ((539/500)*shape (13/20))^2<(R*(13/20))^2 := by
      rw [mul_pow,mul_pow,hs2,hr]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hm := NegativeAPositiveTD.Curvature.shapeD0q_monotone
    (show (13/20:ℝ)∈Icc (0:ℝ) 1 by norm_num)
    (show k∈Icc (0:ℝ) 1 by exact ⟨by linarith [hk.1],by linarith [hk.2]⟩) hk.1
  have he : Vd R k 1 0=NegativeAPositiveTD.Curvature.shapeD0q k := by
    rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
    simp [NegativeAPositiveTD.Curvature.shapeD0q]
  rw [he]
  exact hlow.trans_le hm

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeSlope SecantNormCurvature

def unaffected (k t s : ℝ) : ℝ := F k s+V R k 1 (t-s)
def unaffectedFirst (k t s : ℝ) : ℝ := F1 k s-Vd R k 1 (t-s)
def unaffectedSecond (k t s : ℝ) : ℝ := F2 k s+curvature R k 1 (s-t)-Real.cos (t-s)
def unaffectedThird (k t s : ℝ) : ℝ := F3 k s+curvatureD R k 1 (s-t)-Real.sin (t-s)
def affectedAffine (k t x : ℝ) : ℝ :=
  (K+Real.sin t)*x+Real.cos t-1+R*Real.sqrt (k^2+1)-R*NegativeAPositiveTD.AffectedNorm.norm k t x

theorem unaffected_derivative {k t s : ℝ} (hk : 0<k) (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 t) : HasDerivAt (unaffected k t) (unaffectedFirst k t s) s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hd : t-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [ht.2,hs.1]⟩
  have hh := (V_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) hd).comp s
    ((hasDerivAt_id s).const_sub t)
  convert (F_derivative (k:=k) hs').add hh using 1
  · rfl
  · dsimp [unaffectedFirst]
    ring

theorem unaffectedFirst_derivative {k t s : ℝ} (hk : 0<k) (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 t) : HasDerivAt (unaffectedFirst k t) (unaffectedSecond k t s) s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hd : t-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [ht.2,hs.1]⟩
  have hh := (Vd_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) hd).comp s
    ((hasDerivAt_id s).const_sub t)
  convert (F1_derivative (k:=k) hs').sub hh using 1
  · rfl
  · simp only [neg_sub,one_mul]
    dsimp [unaffectedSecond]
    ring

theorem unaffectedSecond_derivative {k t s : ℝ} (hk : 0<k) (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 t) : HasDerivAt (unaffectedSecond k t) (unaffectedThird k t s) s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have harg : |s-t|≤frameCap := abs_le.mpr ⟨by linarith [ht.2,hs.1],by linarith [hs.2,ht.1,ht.2]⟩
  have hc := (curvature_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) harg).comp s
    ((hasDerivAt_id s).sub_const t)
  have hcos := (Real.hasDerivAt_cos (t-s)).comp s ((hasDerivAt_id s).const_sub t)
  convert ((F2_derivative (k:=k) hs').add hc).sub hcos using 1
  · rfl
  · dsimp [unaffectedThird]
    ring

theorem unaffectedThird_positive {k t s : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    (197/250:ℝ)<unaffectedThird k t s := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  have hratio : (1:ℝ)≤2*k := by linarith [hk.1]
  have harg : s-t∈Icc (-frameCap) frameCap :=
    ⟨by linarith [ht.2,hs.1],by linarith [hs.2,ht.1,ht.2]⟩
  have hz : (0:ℝ)∈Icc (-frameCap) frameCap := by norm_num [frameCap]
  have hc := NegativeAPositiveTD.Curvature.curvatureD_antitone_signed hk0 hk1 hratio
    harg hz (show s-t≤0 by linarith [hs.2])
  rw [curvatureD_zero] at hc
  have hconst := (NegativeAPositiveTD.Curvature.universal_constants hk0 hk1 hratio).2.1
  have hf := third_lower hk ⟨hs.1,hs.2.trans ht.2⟩
  have hy := sine_domain (show t-s∈Icc 0 frameCap by
    exact ⟨by linarith [hs.2],by linarith [ht.2,hs.1]⟩)
  dsimp [unaffectedThird]
  linarith [hy.2]

/-- A convex derivative with a nonpositive right endpoint can only
produce a maximum in the interior. This uses its two-point convexity,
not a root search or an assumed sign-change count. -/
theorem endpoint_min_of_convex_derivative {f g : ℝ→ℝ} {t s : ℝ}
    (ht : 0≤t) (hs : s∈Icc 0 t)
    (hd : ∀x∈Icc 0 t,HasDerivAt f (g x) x)
    (hc : ConcaveOn ℝ (Icc 0 t) (fun x => -g x)) (hgt : g t≤0) :
    min (f 0) (f t)≤f s := by
  by_cases hgs : g s≤0
  · have hanti : AntitoneOn f (Icc s t) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact (hd x ⟨hs.1.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hd x ⟨hs.1.trans hx.1.le,hx.2.le⟩
      · intro x hx
        have hh := hc.min_le_of_mem_Icc hs ⟨ht,le_rfl⟩ (Ioo_subset_Icc_self hx)
        have hm : 0≤ min (-g s) (-g t) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_right (f 0) (f t)).trans (hanti ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2)
  · have hpos : 0<g s := lt_of_not_ge hgs
    have hmono : MonotoneOn f (Icc 0 s) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro x hx
        exact (hd x ⟨hx.1,hx.2.trans hs.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hd x ⟨hx.1.le,hx.2.le.trans hs.2⟩
      · intro x hx
        have hx' : x∈Icc 0 t := ⟨hx.1.le,hx.2.le.trans hs.2⟩
        have hh := hc.min_le_of_mem_Icc hx' ⟨ht,le_rfl⟩
          (show s∈Icc x t from ⟨hx.2.le,hs.2⟩)
        have hleft : g s≤g x := by
          by_contra hn
          have hm : -g s< min (-g x) (-g t) := lt_min (by linarith) (by linarith)
          linarith
        linarith
    exact (min_le_left (f 0) (f t)).trans (hmono ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1)

theorem unaffected_endpoint_long {k t s : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc (3/20:ℝ) frameCap) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤F k s+V R k 1 (t-s) := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht' : t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩
  have hc : ConcaveOn ℝ (Icc 0 t) (fun s => -unaffectedFirst k t s) := by
    apply concave_of_deriv2
      (fun x hx => (unaffectedFirst_derivative hk0 ht' hx).neg)
      (fun x hx => (unaffectedSecond_derivative hk0 ht' hx).neg)
    intro x hx
    have hh := unaffectedThird_positive hk ht' hx
    linarith
  have hright : unaffectedFirst k t t≤0 := by
    have hF := first_upper_long hk ht
    have hV := zero_slope_lower hk
    simp only [unaffectedFirst,sub_self]
    linarith
  have hh := endpoint_min_of_convex_derivative ht'.1 hs
    (fun x hx => unaffected_derivative hk0 ht' hx) hc hright
  simpa [unaffected,F_zero] using hh

theorem unaffected_endpoint_short {k t s : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc (0:ℝ) (3/20)) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤F k s+V R k 1 (t-s) := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hc : ConcaveOn ℝ (Icc 0 t) (unaffected k t) := by
    apply concave_of_deriv2 (fun x hx => unaffected_derivative hk0 ht' hx)
      (fun x hx => unaffectedFirst_derivative hk0 ht' hx)
    intro x hx
    have hF := second_negative_short hk ⟨hx.1,hx.2.trans ht.2⟩
    have hV := mixedN_second_lt (Real.sqrt_nonneg qCap) radius_sq.le hk0
      (show k≤1 by linarith [hk.2]) (show (1:ℝ)≤2*k by linarith [hk.1])
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (show t-x∈Icc 0 frameCap by exact ⟨by linarith [hx.2],by linarith [ht'.2,hx.1]⟩)
    simp only [zero_sub,neg_sub,one_mul] at hV
    dsimp [unaffectedSecond]
    linarith
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,ht.1⟩ ⟨ht.1,le_rfl⟩ hs
  simpa [unaffected,F_zero] using hh

theorem affected_identity {k t s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    F k s+V R k (secant s) (t-s)=affectedAffine k t (Real.tan s) := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hc : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hk0 : 0<k := by linarith [hk.1]
  have hq : 0<secant s := by linarith [(full_secant_domain hs').1]
  have hd : |-(t-s)|≤frameCap := by
    rw [abs_neg,abs_of_nonneg (by linarith [hs.2])]
    linarith [ht.2,hs.1]
  have hn := pairNorm_pos hk0 hq hd
  have hn2 := pairNorm_sq hk0 hq hd
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    (show k∈Icc (0:ℝ) (71/50) by exact ⟨hk0.le,by linarith [hk.2]⟩) ht
  have hN := NegativeAPositiveTD.AffectedNorm.norm_pos (x:=Real.tan s) hv
  have hN2 := NegativeAPositiveTD.AffectedNorm.norm_sq_expanded k t (Real.tan s)
  have he : (pairNorm k (secant s) (-(t-s)))^2=
      (NegativeAPositiveTD.AffectedNorm.norm k t (Real.tan s))^2 := by
    rw [hn2,hN2]
    dsimp [pairEnergy,pairProduct,secant]
    rw [Real.sin_neg,Real.sin_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    linear_combination -Real.sin_sq_add_cos_sq s
  have hnorm : pairNorm k (secant s) (-(t-s))=
      NegativeAPositiveTD.AffectedNorm.norm k t (Real.tan s) := by nlinarith
  have hzero : pairNorm k (secant s) 0=supportNorm k s := by
    simp [pairNorm,supportNorm]
  have hcos : secant s*Real.cos (t-s)=Real.cos t+Real.sin t*Real.tan s := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    dsimp [secant]
    field_simp [hc.ne']
  dsimp [F,normalized,V,affectedAffine]
  rw [hnorm,hzero]
  nlinarith only [hcos]

theorem affected_endpoint {k t s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤F k s+V R k (secant s) (t-s) := by
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    (show k∈Icc (0:ℝ) (71/50) by exact ⟨by linarith [hk.1],by linarith [hk.2]⟩) ht
  have hf (x : ℝ) : HasDerivAt (affectedAffine k t)
      (K+Real.sin t-R*NegativeAPositiveTD.AffectedNorm.first k t x) x := by
    have hh := (((((hasDerivAt_id' x).const_mul (K+Real.sin t)).add_const (Real.cos t)).sub_const
      1).add_const (R*Real.sqrt (k^2+1))).fun_sub
        ((NegativeAPositiveTD.AffectedNorm.norm_hasDerivAt hv).const_mul R)
    exact hh.congr_deriv (by ring)
  have hf' (x : ℝ) : HasDerivAt
      (fun x => K+Real.sin t-R*NegativeAPositiveTD.AffectedNorm.first k t x)
      (-R*NegativeAPositiveTD.AffectedNorm.second k t x) x := by
    convert ((NegativeAPositiveTD.AffectedNorm.first_hasDerivAt hv).const_mul R).const_sub
      (K+Real.sin t) using 1
    ring
  have hc : ConcaveOn ℝ (Icc 0 (Real.tan t)) (affectedAffine k t) := by
    apply concave_of_deriv2 (fun x _ => hf x) (fun x _ => hf' x)
    intro x hx
    dsimp [NegativeAPositiveTD.AffectedNorm.second]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
      (div_nonneg (sq_nonneg _) (pow_nonneg (NegativeAPositiveTD.AffectedNorm.norm_pos hv).le 3))
  have ht0 := NegativeAPositiveTD.SecantCoordinate.tan_nonnegative ht
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan t) :=
    ⟨NegativeAPositiveTD.SecantCoordinate.tan_nonnegative hs',
      NegativeAPositiveTD.SecantCoordinate.tan_monotone hs' ht hs.2⟩
  have h0 := affected_identity hk ht (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have h1 := affected_identity hk ht (show t∈Icc 0 t from ⟨ht.1,le_rfl⟩)
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,ht0⟩ ⟨ht0,le_rfl⟩ hx
  simp only [Real.tan_zero,F_zero,zero_add,sub_zero,sub_self,V_zero,add_zero,
    secant,Real.cos_zero,div_one] at h0 h1
  rw [←h0,←h1,←affected_identity hk ht hs] at hh
  exact hh

/-- The common-gain endpoint principle. The proof also establishes the
short-interval case for every k in the stated coefficient interval. -/
theorem endpoint {k t s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤
      F k s+min (V R k 1 (t-s)) (V R k (secant s) (t-s)) := by
  have hun : min (V R k 1 t) (F k t)≤F k s+V R k 1 (t-s) := by
    by_cases hshort : t≤3/20
    · exact unaffected_endpoint_short hk ⟨ht.1,hshort⟩ hs
    · exact unaffected_endpoint_long hk ⟨le_of_lt (lt_of_not_ge hshort),ht.2⟩ hs
  have haff := affected_endpoint hk ht hs
  by_cases hh : V R k 1 (t-s)≤V R k (secant s) (t-s)
  · rw [min_eq_left hh]
    exact hun
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hh))]
    exact haff

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.CommonGain
end
end
end
