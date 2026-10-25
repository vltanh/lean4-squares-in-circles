module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.DMinorant
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2NegativeSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2SignedCurvature
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNorms

/-!
# Eight squares: the two polynomial reserves in the low separated-block argument

The degree-fourteen polynomial retains
its centered quadratic on the whole short interval. The interior-D
quartic has positive Bernstein coefficients on `[0.27, 0.645]`. No sample points
or interval mesh enter either bound.
-/

section
/-!
## Exact reference reserves for the low-total B/H rectangle

Only the intrinsic coefficient corner k=.5866, m=1.1642 and the original
angle endpoints 0 and 7/10 occur. Every radical comparison is reduced
to a positive rational square. These are not samples of the rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowRectangle
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope
open NegativeAPositiveTD.PositiveSlope NegativeAPositiveTD.Curvature
open PositiveTD.Certificate (S5 S9 S11 C4 C10 taylor_bounds)

abbrev k0 : ℝ := 2933/5000
abbrev M : ℝ := 5821/5000

theorem lower_quotient_of_square {x y b : ℝ} (hx : 0≤x) (hy : 0<y)
    (hb : 0≤b) (hs : b^2*y^2<x^2) : b<x/y := by
  apply (lt_div_iff₀ hy).2
  have hprod : 0≤b*y := mul_nonneg hb hy.le
  nlinarith

lemma zero_norm_power (p q : ℝ) (n : ℕ) :
    ((pairNorm p q 0)^n)^2=(p^2+q^2)^n := by
  rw [show ((pairNorm p q 0)^n)^2=((pairNorm p q 0)^2)^n by ring,
    NonnegativeTotals.Analytic.norm_zero_square]

theorem B_zero_curvature : (741/1000:ℝ)<curvatureZero R 1 M := by
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
    (by norm_num [frameCap] : |(0:ℝ)|≤frameCap)
  unfold curvatureZero
  apply lower_quotient_of_square (by positivity) (pow_pos hn 3) (by norm_num)
  rw [zero_norm_power, mul_pow, radius_sq]
  norm_num [pairProduct,M,qCap]

theorem H_zero_curvature : curvatureZero R k0 1<(437/1000:ℝ) := by
  have hn := pairNorm_pos (by norm_num [k0] : 0<k0) (by norm_num : (0:ℝ)<1)
    (by norm_num [frameCap] : |(0:ℝ)|≤frameCap)
  unfold curvatureZero
  apply quotient_lt_of_square (pow_pos hn 3) (by norm_num)
  rw [zero_norm_power,mul_pow,radius_sq]
  norm_num [pairProduct,k0,qCap]

theorem H_zero_curvature_slope : (429/1000:ℝ)<curvatureSlope R k0 1 := by
  have hn := pairNorm_pos (by norm_num [k0] : 0<k0) (by norm_num : (0:ℝ)<1)
    (by norm_num [frameCap] : |(0:ℝ)|≤frameCap)
  unfold curvatureSlope
  apply lower_quotient_of_square
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg qCap) (by norm_num [pairProduct,k0]))
      (by norm_num [pairEnergy,pairProduct,k0])) (pow_pos hn 5) (by norm_num)
  rw [zero_norm_power,mul_pow,mul_pow,radius_sq]
  norm_num [pairEnergy,pairProduct,k0,qCap]

theorem B_positive_initial_slope : -(251/500:ℝ)<Ud 1 M 0 := by
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
    (by norm_num [frameCap] : |(0:ℝ)|≤frameCap)
  have hh : R*M/pairNorm 1 M 0<(751/500:ℝ) := by
    apply quotient_lt_of_square hn (by norm_num)
    rw [mul_pow,radius_sq,NonnegativeTotals.Analytic.norm_zero_square]
    norm_num [M,qCap]
  simp only [Ud,mixedPDerivative,normD1,pairProduct,sub_zero,Real.cos_zero,
    Real.sin_zero,mul_one,one_mul,sub_self] at ⊢
  rw [← mul_div_assoc]
  linarith

lemma cap_taylor :
    0≤Polynomial.aeval frameCap S11 ∧ Polynomial.aeval frameCap S11≤Real.sin frameCap ∧
      Real.sin frameCap≤Polynomial.aeval frameCap S9 ∧
      0≤Polynomial.aeval frameCap C10 ∧ Polynomial.aeval frameCap C10≤Real.cos frameCap := by
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  exact ⟨ht.1,ht.2.1,ht.2.2.1,by linarith [ht.2.2.2.1],ht.2.2.2.2.1⟩

private lemma r72_S11_cap :
    Polynomial.aeval frameCap S11=(7/10:ℝ)-(7/10)^3/6+(7/10)^5/120-(7/10)^7/5040+
      (7/10)^9/362880-(7/10)^11/39916800 := by
  simp only [S11,S9,S5,map_sub,map_add,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,
    eq_ratCast,frameCap]
  push_cast
  ring

private lemma r72_S9_cap :
    Polynomial.aeval frameCap S9=(7/10:ℝ)-(7/10)^3/6+(7/10)^5/120-(7/10)^7/5040+
      (7/10)^9/362880 := by
  simp only [S9,S5,map_sub,map_add,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,
    eq_ratCast,frameCap]
  push_cast
  ring

private lemma r72_C10_cap :
    Polynomial.aeval frameCap C10=1-(7/10:ℝ)^2/2+(7/10)^4/24-(7/10)^6/720+(7/10)^8/40320-
      (7/10)^10/3628800 := by
  simp only [C10,C4,map_sub,map_add,map_mul,map_pow,map_one,Polynomial.aeval_X,
    Polynomial.aeval_C,eq_ratCast,frameCap]
  push_cast
  ring

theorem B_cap_curvature : (1923/2000:ℝ)<curvature R 1 M frameCap := by
  have ht := cap_taylor
  have hfc : |frameCap|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (by norm_num : (0:ℝ)<1) (by norm_num [M] : (0:ℝ)<M) hfc
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<1) (by norm_num [M] : (0:ℝ)<M) hfc
  have hrat : (1923/2000:ℝ)^2*(1+M^2+2*M*Polynomial.aeval frameCap S9)^3<
      (R*M*((1+M^2)*Polynomial.aeval frameCap S11+
        M*(1+(Polynomial.aeval frameCap S11)^2)))^2 := by
    rw [mul_pow,mul_pow,radius_sq,r72_S11_cap,r72_S9_cap]
    norm_num [M,qCap]
  have hid : curvature R 1 M frameCap=
      R*M*((1+M^2)*Real.sin frameCap+M*(1+(Real.sin frameCap)^2))/
        (pairNorm 1 M frameCap)^3 := by
    simp only [curvature,normD2,pairProduct,pairEnergy]
    ring
  have hR : 0≤R := Real.sqrt_nonneg _
  have hM0 : (0:ℝ)≤M := by norm_num [M]
  rw [hid]
  simp only [pairEnergy,pairProduct] at hn2
  obtain ⟨hsl0,hslS,hSsu,-,-⟩ := ht
  generalize Polynomial.aeval frameCap S11=sl at hsl0 hslS hrat
  generalize Polynomial.aeval frameCap S9=su at hSsu hrat
  generalize Real.sin frameCap=S at hslS hSsu hn2 ⊢
  generalize pairNorm 1 M frameCap=n at hn hn2 ⊢
  generalize M=m at hM0 hrat hn2 ⊢
  have hN : n^2≤1+m^2+2*m*su := by
    have := mul_le_mul_of_nonneg_left hSsu hM0
    nlinarith
  have hN3 := pow_le_pow_left₀ (sq_nonneg n) hN 3
  have hs2 := pow_le_pow_left₀ hsl0 hslS 2
  have hfactor : (1+m^2)*sl+m*(1+sl^2)≤(1+m^2)*S+m*(1+S^2) := by
    have h₁ := mul_le_mul_of_nonneg_left hslS (show 0≤1+m^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hs2 hM0
    nlinarith
  have hlower := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hR hM0)
  have hquot : (1923/2000:ℝ)<R*m*((1+m^2)*sl+m*(1+sl^2))/n^3 := by
    apply lower_quotient_of_square (by positivity) (pow_pos hn 3) (by norm_num)
    have hpow : (n^3)^2=(n^2)^3 := by ring
    rw [hpow]
    have := mul_le_mul_of_nonneg_left hN3 (sq_nonneg (1923/2000:ℝ))
    linarith
  exact hquot.trans_le (div_le_div_of_nonneg_right hlower (pow_nonneg hn.le 3))

theorem H_negative_cap_slope : (513/1000:ℝ)<Vd R k0 1 frameCap := by
  have ht := cap_taylor
  have hfc : |-frameCap|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (by norm_num [k0] : (0:ℝ)<k0) (by norm_num : (0:ℝ)<1) hfc
  have hn2 := pairNorm_sq (by norm_num [k0] : (0:ℝ)<k0) (by norm_num : (0:ℝ)<1) hfc
  have hrat : (513/1000+Polynomial.aeval frameCap S9)^2*
      (k0^2+1-2*k0*Polynomial.aeval frameCap S11)<(R*k0*Polynomial.aeval frameCap C10)^2 := by
    rw [mul_pow,mul_pow,radius_sq,r72_S11_cap,r72_S9_cap,r72_C10_cap]
    norm_num [k0,qCap]
  have hsu0 : 0≤513/1000+Polynomial.aeval frameCap S9 := by
    rw [r72_S9_cap]; norm_num
  have hid : Vd R k0 1 frameCap=
      -Real.sin frameCap+R*k0*Real.cos frameCap/pairNorm k0 1 (-frameCap) := by
    simp only [Vd,mixedNDerivative,normD1,pairProduct,zero_sub,Real.cos_neg]
    ring
  have hR : 0≤R := Real.sqrt_nonneg _
  have hk0 : (0:ℝ)≤k0 := by norm_num [k0]
  rw [hid]
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hn2
  obtain ⟨hsl0,hslS,hSsu,hcl0,hclC⟩ := ht
  generalize Polynomial.aeval frameCap S11=sl at hsl0 hslS hrat
  generalize Polynomial.aeval frameCap S9=su at hSsu hrat hsu0
  generalize Polynomial.aeval frameCap C10=cl at hcl0 hclC hrat
  generalize Real.sin frameCap=S at hslS hSsu hn2 ⊢
  generalize Real.cos frameCap=Co at hclC ⊢
  generalize pairNorm k0 1 (-frameCap)=n at hn hn2 ⊢
  generalize k0=k at hk0 hrat hn2 ⊢
  have hN : n^2≤k^2+1-2*k*sl := by
    have := mul_le_mul_of_nonneg_left hslS hk0
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hN (sq_nonneg (513/1000+su))
  have hquot : 513/1000+su<R*k*cl/n := by
    apply lower_quotient_of_square (by positivity) hn hsu0
    linarith
  have hcos := mul_le_mul_of_nonneg_left hclC (mul_nonneg hR hk0)
  have hquot' := div_le_div_of_nonneg_right hcos hn.le
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowRectangle
end
end
end

section
/-!
## The fixed-coefficient tangents in the low separated alternatives

The larger coefficient varies over its
whole interval. The rational center is exactly 5/4, and the intercept
buffers pay the stated two-sided derivative-rounding errors.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

abbrev p0 : ℝ := 757/1000
abbrev q0 : ℝ := 5/4
abbrev qMax : ℝ := 169/125

def root (q : ℝ) : ℝ := Real.sqrt (p0^2+q^2)
def D0 (q : ℝ) : ℝ := R*p0*q/root q
def D1 (q : ℝ) : ℝ := R*p0^3/(root q)^3
def D2 (q : ℝ) : ℝ := -3*R*p0^3*q/(root q)^5
def D3 (q : ℝ) : ℝ := 3*R*p0^3*(4*q^2-p0^2)/(root q)^7
def C0 (q : ℝ) : ℝ := R*p0^2*q^2/(root q)^3
def C1 (q : ℝ) : ℝ := R*p0^2*q*(2*p0^2-q^2)/(root q)^5
def C2 (q : ℝ) : ℝ := R*p0^2*(2*p0^4-11*p0^2*q^2+2*q^4)/(root q)^7

theorem root_pos (q : ℝ) : 0<root q := Real.sqrt_pos.mpr (by dsimp [p0]; positivity)
theorem root_sq (q : ℝ) : (root q)^2=p0^2+q^2 := Real.sq_sqrt (by positivity)
theorem root_derivative (q : ℝ) : HasDerivAt root (q/root q) q := by
  convert (((hasDerivAt_id q).pow 2).const_add (p0^2)).sqrt
    (by dsimp [p0]; positivity : p0^2+q^2≠0) using 1
  · rfl
  · dsimp [root]
    ring

theorem D0_derivative (q : ℝ) : HasDerivAt D0 (D1 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := ((hasDerivAt_id q).const_mul (R*p0)).div (root_derivative q) hr.ne'
  convert hh using 1
  · rfl
  dsimp [D1]
  field_simp
  linear_combination (-1000000:ℝ)*hs

theorem D1_derivative (q : ℝ) : HasDerivAt D1 (D2 q) q := by
  have hh := (hasDerivAt_const q (R*p0^3)).div
    ((root_derivative q).pow 3) (pow_ne_zero 3 (root_pos q).ne')
  convert hh using 1
  · rfl
  · dsimp [D2]
    field_simp [(root_pos q).ne']
    ring

theorem D2_derivative (q : ℝ) : HasDerivAt D2 (D3 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := ((hasDerivAt_id q).const_mul (-3*R*p0^3)).div
    ((root_derivative q).pow 5) (pow_ne_zero 5 hr.ne')
  convert hh using 1
  · rfl
  dsimp [D3]
  field_simp
  linear_combination (1000000:ℝ)*hs

theorem C0_derivative (q : ℝ) : HasDerivAt C0 (C1 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := (((hasDerivAt_id q).pow 2).const_mul (R*p0^2)).div
    ((root_derivative q).pow 3) (pow_ne_zero 3 hr.ne')
  convert hh using 1
  · rfl
  dsimp [C1]
  field_simp
  linear_combination (-2000000*q)*hs

theorem C1_derivative (q : ℝ) : HasDerivAt C1 (C2 q) q := by
  have hr := root_pos q
  have hs := root_sq q
  have hh := (((hasDerivAt_id q).const_mul (R*p0^2)).mul
    ((hasDerivAt_pow 2 q).const_sub (2*p0^2))).div
    ((root_derivative q).pow 5) (pow_ne_zero 5 hr.ne')
  convert hh using 1
  · rfl
  dsimp [C2]
  field_simp
  linear_combination (3000000000000*q^2-1146098000000)*hs

theorem lower_quotient {x y c : ℝ} (hx : 0<x) (hy : 0<y) (hc : 0≤c)
    (hsq : c^2*y^2<x^2) : c<x/y := by
  apply (lt_div_iff₀ hy).2
  have hp : 0≤c*y := mul_nonneg hc hy.le
  nlinarith

theorem endpoint_bounds :
    D0 q0<12813/10000 ∧ D1 q0∈Ioo (5501/20000:ℝ) (27507/100000) ∧
    C0 q0<28387/50000 ∧ C1 q0∈Ioo (-(8857/100000):ℝ) (-(1771/20000)) ∧
    D2 qMax< -(389/1000:ℝ) := by
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hpow (q : ℝ) (n : ℕ) : ((root q)^n)^2=(p0^2+q^2)^n := by
    rw [←pow_mul,mul_comm,pow_mul,root_sq]
  have hD0 : D0 q0<12813/10000 := by
    unfold D0
    apply quotient_lt_of_square (root_pos _) (by norm_num)
    rw [mul_pow,mul_pow,hR2,root_sq]
    norm_num [qCap]
  have hD1lo : (5501/20000:ℝ)<D1 q0 := by
    unfold D1
    apply lower_quotient (mul_pos hR (by norm_num)) (pow_pos (root_pos _) 3) (by norm_num)
    rw [hpow,mul_pow,hR2]
    norm_num [qCap]
  have hD1hi : D1 q0<27507/100000 := by
    unfold D1
    apply quotient_lt_of_square (pow_pos (root_pos _) 3) (by norm_num)
    rw [hpow,mul_pow,hR2]
    norm_num [qCap]
  have hC0 : C0 q0<28387/50000 := by
    unfold C0
    apply quotient_lt_of_square (pow_pos (root_pos _) 3) (by norm_num)
    rw [hpow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  have he : -C1 q0=R*p0^2*q0*(q0^2-2*p0^2)/(root q0)^5 := by dsimp [C1]; ring
  have hC1lo : (1771/20000:ℝ)< -C1 q0 := by
    rw [he]
    apply lower_quotient (mul_pos (mul_pos (mul_pos hR (by norm_num)) (by norm_num))
      (by norm_num)) (pow_pos (root_pos _) 5) (by norm_num)
    rw [hpow,mul_pow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  have hC1hi : -C1 q0<8857/100000 := by
    rw [he]
    apply quotient_lt_of_square (pow_pos (root_pos _) 5) (by norm_num)
    rw [hpow,mul_pow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  have hD2 : (389/1000:ℝ)< -D2 qMax := by
    have he2 : -D2 qMax=3*R*p0^3*qMax/(root qMax)^5 := by dsimp [D2]; ring
    rw [he2]
    apply lower_quotient (mul_pos (mul_pos (mul_pos (by norm_num) hR) (by norm_num))
      (by norm_num)) (pow_pos (root_pos _) 5) (by norm_num)
    rw [hpow,mul_pow,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  exact ⟨hD0,⟨hD1lo,hD1hi⟩,hC0,⟨by linarith,by linarith⟩,by linarith⟩

theorem D2_upper {q : ℝ} (hq : q∈Icc 1 qMax) : D2 q< -(389/1000:ℝ) := by
  have hm : MonotoneOn D2 (Icc (1:ℝ) qMax) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun q _ => (D2_derivative q).continuousAt.continuousWithinAt)
      (fun q _ => D2_derivative q)
    intro q hq
    have hnum : 0≤4*q^2-p0^2 := by norm_num [p0]; nlinarith [hq.1]
    exact div_nonneg (mul_nonneg (by positivity : 0≤3*R*p0^3) hnum)
      (pow_nonneg (root_pos _).le 7)
  exact (hm hq (by norm_num [qMax]) hq.2).trans_lt endpoint_bounds.2.2.2.2

theorem C2_nonpositive {q : ℝ} (hq : q∈Icc 1 qMax) : C2 q≤0 := by
  have hq0 : 0≤q := by linarith [hq.1]
  have hq2lo : (1:ℝ)≤q^2 := by nlinarith [hq.1]
  have hq2hi := pow_le_pow_left₀ hq0 hq.2 2
  have hprod := mul_nonneg (sub_nonneg.mpr hq2lo) (sub_nonneg.mpr hq2hi)
  have hpoly : 2*p0^4-11*p0^2*q^2+2*q^4≤0 := by
    norm_num [p0,qMax] at *
    nlinarith
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤R*p0^2) hpoly)
    (pow_nonneg (root_pos _).le 7)

/-- The derivative form of the two-sided concave tangent inequality. -/
theorem tangent_upper {f df : ℝ→ℝ} {a b c x : ℝ}
    (hc : c∈Icc a b) (hx : x∈Icc a b)
    (hd : ∀y∈Icc a b,HasDerivAt f (df y) y)
    (hm : AntitoneOn df (Icc a b)) : f x≤f c+df c*(x-c) := by
  by_cases hxc : x≤c
  · have hh := derivative_reserve
      (f:=f) (df:=df) (k:=df c)
      (fun y hy => (hd y ⟨hy.1,hy.2.trans hc.2⟩).continuousAt.continuousWithinAt)
      (fun y hy => hd y ⟨hy.1.le,hy.2.le.trans hc.2⟩)
      (fun y hy => hm ⟨hy.1.le,hy.2.le.trans hc.2⟩ hc hy.2.le)
      (show x∈Icc a c from ⟨hx.1,hxc⟩) (show c∈Icc a c from ⟨hc.1,le_rfl⟩) hxc
    linarith
  · have hcx : c≤x := (lt_of_not_ge hxc).le
    have hh := derivative_reserve
      (f:=fun y => -f y) (df:=fun y => -df y) (k:=-df c)
      (fun y hy => (hd y ⟨hc.1.trans hy.1,hy.2⟩).neg.continuousAt.continuousWithinAt)
      (fun y hy => (hd y ⟨hc.1.trans hy.1.le,hy.2.le⟩).neg)
      (fun y hy => neg_le_neg (hm hc ⟨hc.1.trans hy.1.le,hy.2.le⟩ hy.1.le))
      (show c∈Icc c b from ⟨le_rfl,hc.2⟩) (show x∈Icc c b from ⟨hcx,hx.2⟩) hcx
    linarith

theorem exact_tangents {q : ℝ} (hq : q∈Icc 1 qMax) :
    D0 q≤D0 q0+D1 q0*(q-q0)-(389/2000)*(q-q0)^2 ∧
    C0 q≤C0 q0+C1 q0*(q-q0) := by
  have hcenter : q0∈Icc (1:ℝ) qMax := by norm_num [q0,qMax]
  have hD (q : ℝ) : HasDerivAt
      (fun q => D0 q+(389/2000)*(q-q0)^2)
      (D1 q+(389/1000)*(q-q0)) q := by
    have h1 := (D0_derivative q).add
      ((((hasDerivAt_id q).sub_const q0).pow 2).const_mul (389/2000:ℝ))
    convert h1 using 1
    · rfl
    · simp only [id,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
      ring
  have hD1 (q : ℝ) : HasDerivAt (fun q => D1 q+(389/1000)*(q-q0)) (D2 q+389/1000) q := by
    have h1 := (D1_derivative q).add (((hasDerivAt_id q).sub_const q0).const_mul (389/1000:ℝ))
    convert h1 using 1
    · rfl
    · ring
  have hDm : AntitoneOn (fun q => D1 q+(389/1000)*(q-q0)) (Icc (1:ℝ) qMax) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun q _ => (hD1 q).continuousAt.continuousWithinAt) (fun q _ => hD1 q)
    intro q hq
    linarith [D2_upper (Ioo_subset_Icc_self hq)]
  have hCm : AntitoneOn C1 (Icc (1:ℝ) qMax) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun q _ => (C1_derivative q).continuousAt.continuousWithinAt)
      (fun q _ => C1_derivative q)
    intro q hq
    exact C2_nonpositive (Ioo_subset_Icc_self hq)
  have hd := tangent_upper hcenter hq (fun q _ => hD q) hDm
  have hc := tangent_upper hcenter hq (fun q _ => C0_derivative q) hCm
  simp only [sub_self,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,
    add_zero] at hd
  exact ⟨by linarith,hc⟩

theorem rounded_tangents {q : ℝ} (hq : q∈Icc 1 qMax) :
    D0 q<32033/25000+(13753/50000)*(q-q0)-(389/2000)*(q-q0)^2 ∧
    C0 q<2271/4000-(1107/12500)*(q-q0) := by
  have hqabs : |q-q0|≤1/4 := by
    rw [abs_le]
    norm_num [q0,qMax] at *
    exact ⟨by linarith [hq.1],by linarith [hq.2]⟩
  have hDabs : |D1 q0-13753/50000|≤1/100000 := by
    rw [abs_le]
    constructor <;> linarith [endpoint_bounds.2.1.1,endpoint_bounds.2.1.2]
  have hCabs : |C1 q0+1107/12500|≤1/100000 := by
    rw [abs_le]
    constructor <;> linarith [endpoint_bounds.2.2.2.1.1,endpoint_bounds.2.2.2.1.2]
  have hDerr := mul_le_mul hDabs hqabs (abs_nonneg (q-q0)) (by norm_num : (0:ℝ)≤1/100000)
  have hCerr := mul_le_mul hCabs hqabs (abs_nonneg (q-q0)) (by norm_num : (0:ℝ)≤1/100000)
  rw [←abs_mul] at hDerr hCerr
  have hd := (abs_le.mp hDerr).2
  have hc := (abs_le.mp hCerr).2
  have ht := exact_tangents hq
  have hb := endpoint_bounds
  have e1 : D1 q0*(q-q0)=(D1 q0-13753/50000)*(q-q0)+13753/50000*(q-q0) := by ring
  have e2 : C1 q0*(q-q0)=(C1 q0+1107/12500)*(q-q0)-1107/12500*(q-q0) := by ring
  constructor
  · linarith [hb.1,ht.1]
  · have h3 := hb.2.2.1
    have h4 := ht.2
    rw [e2] at h4
    norm_num at h3 h4 hc ⊢
    linarith

@[simp] theorem D0_original (q : ℝ) : D0 q=NegativeAPositiveTD.Curvature.slopeZero p0 q := by
  simp only [D0,NegativeAPositiveTD.Curvature.slopeZero,pairProduct,pairNorm,root,Real.sin_zero,
    mul_zero,add_zero,mul_assoc]
@[simp] theorem C0_original (q : ℝ) : C0 q=curvatureZero R p0 q := by
  simp only [C0,curvatureZero,pairProduct,pairNorm,root,Real.sin_zero,mul_zero,add_zero,mul_pow,
    mul_assoc]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
end
end
end

section
/-!
## The low separated negative-slope model

The signed curvature tangent is
integrated toward the original negative argument. Only afterward is
the smaller coefficient compared with the prescribed endpoint .757.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

theorem negative_norm_tangent {p q d : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    R*normD1 p q (-d)≤NegativeAPositiveTD.Curvature.slopeZero p q+
      curvatureZero R p q*d-curvatureSlope R p q*d^2/2 := by
  have hq := hp.trans_le hpq
  let f : ℝ→ℝ := fun x => curvatureZero R p q*x-
    curvatureSlope R p q*x^2/2-R*normD1 p q (-x)
  have hf (x : ℝ) (hx : x∈Icc 0 frameCap) : HasDerivAt f
      (curvatureZero R p q-curvatureSlope R p q*x-curvature R p q (-x)) x := by
    have hn := ((normD1_hasDerivAt hp hq
      (show |-x|≤frameCap by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)).comp x
        (hasDerivAt_neg x)).const_mul R
    have hlin := (hasDerivAt_id x).const_mul (curvatureZero R p q)
    have hquad := (((hasDerivAt_id x).pow 2).const_mul (curvatureSlope R p q)).div_const 2
    convert (hlin.sub hquad).sub hn using 1
    · rfl
    · simp only [curvature,id,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
      ring
  have hm : MonotoneOn f (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => hf x (Ioo_subset_Icc_self hx))
    intro x hx
    have ht := NegativeAPositiveTD.Curvature.curvature_signed_tangent hp hpq hqp
      (show |-x|≤frameCap by rw [abs_neg,abs_of_pos hx.1]; exact hx.2.le)
    nlinarith only [ht]
  have hh := hm (by norm_num [frameCap]) hd hd.1
  dsimp [f] at hh
  simp only [mul_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,
    sub_zero,neg_zero] at hh
  have he : R*normD1 p q 0=NegativeAPositiveTD.Curvature.slopeZero p q := by
    simp only [normD1,NegativeAPositiveTD.Curvature.slopeZero,Real.cos_zero,mul_one]
    ring
  rw [he] at hh
  linarith

theorem negative_slope_model {p q d : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hd : d∈Icc 0 frameCap) :
    Vd R p q d≤NegativeAPositiveTD.Curvature.slopeZero p q+(curvatureZero R p q-q)*d-
      q*d^2/6+q*d^3/6 := by
  have hq := hp.trans_le hpq
  have hn := negative_norm_tangent hp hpq hqp hd
  have hC := (NegativeAPositiveTD.Curvature.universal_constants hp hpq hqp).2.1
  have hCsq := mul_le_mul_of_nonneg_right hC.le (sq_nonneg d)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hd.1) hq.le
  simp only [Vd,mixedNDerivative,zero_sub]
  nlinarith only [hn,hCsq,hs]

theorem negative_slope_linear_model {p q d : ℝ}
    (hp : 0<p) (hq : 0<q) (hd : d∈Icc 0 frameCap) :
    Vd R p q d≤NegativeAPositiveTD.Curvature.slopeZero p q+(curvatureZero R p q-q)*d+q*d^3/6 := by
  have hn := NegativeAPositiveTD.Curvature.norm_slope_signed_tangent hp hq
    (show |-d|≤frameCap by rw [abs_neg,abs_of_nonneg hd.1]; exact hd.2)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hd.1) hq.le
  simp only [Vd,mixedNDerivative,zero_sub]
  nlinarith only [hn,hs]

theorem Vd_smaller_monotone {p P q d : ℝ}
    (hp : 0≤p) (hpP : p≤P) (hPq : P≤q) (hq : 0<q) (hd : d∈Icc 0 frameCap) :
    Vd R p q d≤Vd R P q d := by
  have hh := NegativeAPositiveTD.NegativeSlope.normalized_slope_mono
    (div_nonneg hp hq.le) ((div_le_div_iff_of_pos_right hq).2 hpP)
    ((div_le_one hq).2 hPq) hd
  have hscaled := mul_le_mul_of_nonneg_left hh hq.le
  rw [Vd_normalized hq,Vd_normalized hq]
  simpa only [Vd_normalized (by norm_num : (0:ℝ)<1),div_one,one_mul] using hscaled

def A (d : ℝ) : ℝ := 13753/50000-(13607/12500)*d-d^2/6+d^3/6
def B (d : ℝ) : ℝ := 32033/25000-(2729/4000)*d-(5/24)*d^2+(5/24)*d^3
def model (d : ℝ) : ℝ := B d+(500/389)*(A d)^2

theorem quadratic_model {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax) (hd : d∈Icc 0 frameCap) :
    Vd R p q d<B d+A d*(q-q0)-(389/2000)*(q-q0)^2 := by
  have hq0 : 0<q := by linarith [hq.1]
  have hpq : p0≤q := by norm_num [p0]; linarith [hq.1]
  have hqp : q≤2*p0 := by norm_num [p0,qMax] at *; linarith [hq.2]
  have hm := Vd_smaller_monotone hp.le hp0 hpq hq0 hd
  have hn := negative_slope_model (p:=p0) (by norm_num [p0]) hpq hqp hd
  have ht := rounded_tangents hq
  have hC := mul_le_mul_of_nonneg_right ht.2.le hd.1
  rw [D0_original] at ht
  rw [C0_original] at hC
  have he : (32033/25000+(13753/50000)*(q-q0)-(389/2000)*(q-q0)^2)+
      (2271/4000-(1107/12500)*(q-q0)-q)*d-q*d^2/6+q*d^3/6=
        B d+A d*(q-q0)-(389/2000)*(q-q0)^2 := by dsimp [A,B,q0]; ring
  rw [←he]
  nlinarith only [hm,hn,ht.1,hC]

theorem completed_model {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax) (hd : d∈Icc 0 frameCap) :
    Vd R p q d< model d := by
  have hh := quadratic_model hp hp0 hq hd
  dsimp [model]
  nlinarith [sq_nonneg ((q-q0)-(1000/389)*A d)]

theorem model_nonnegative {d : ℝ} (hd : d∈Icc 0 frameCap) : 0≤ model d := by
  have hd2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hd3 := pow_nonneg hd.1 3
  have hB : 0≤B d := by
    dsimp [B,frameCap] at *
    nlinarith
  exact add_nonneg hB (mul_nonneg (by norm_num) (sq_nonneg _))

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope

namespace Certificate
open PositiveTD.Certificate (S5 C4)

def AP : ℚ[X] := C (13753/50000)-C (13607/12500)*X-C (1/6)*X^2+C (1/6)*X^3
def BP : ℚ[X] := C (32033/25000)-C (2729/4000)*X-C (5/24)*X^2+C (5/24)*X^3
def shortPolynomial : ℚ[X] := C (13/12)-C (2/5)*S5.comp (C (7/10)-X)-
  (C4.comp (C (7/10)-X))^2*(BP+C (500/389)*AP^2)
def shortTranslated : ℚ[X] := DirectedPowerBounds.shift (3/25) shortPolynomial

/-! ### Kernel certificates

Each polynomial is represented by a scaled integer coefficient list
(`WholeIntervalPolynomial.Certificate`) built to mirror its definition. -/

open WholeIntervalPolynomial.Certificate in
private theorem r75_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

private theorem r75_shift_eq (a : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.shift a p=WholeIntervalPolynomial.centered (a-1) (a+1) p := by
  rw [DirectedPowerBounds.shift,WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,
    show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul]

/-- A polynomial of degree below `k+n` is its first `k` monomials plus its tail. -/
private theorem r75_split {p : ℚ[X]} (k n : ℕ) (hp : p.natDegree<k+n) :
    p=(∑ i ∈ Finset.range k,C (p.coeff i)*X^i)+PowerTailBounds.tail p k n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+k))*X^(j+k)) n]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_comm k j]

open WholeIntervalPolynomial.Certificate in
private theorem r75_coeff_sub_norm {c : Scaled} {p : ℚ[X]}
    (hc : c.Rep p) (hs : c.s≠0) (j0 k n a m : ℕ) (hm : 0 < m) {r : ℚ} (hr : r*m=a) :
    p.coeff j0-PowerTailBounds.norm p k n r=
      ((c.l.getD j0 0*(m:ℤ)^n-
        ∑ j : Fin n,|c.l.getD (j.val+k) 0| *(a:ℤ)^(j.val+1)*(m:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        ((c.s*m^n:ℕ):ℚ) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have hr' : r=a/m := by field_simp; linarith
  unfold PowerTailBounds.norm
  simp only [hc.coeff hs]
  push_cast
  rw [sub_div,Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := j.isLt
    have hpow : (m:ℚ)^n=m^(n-1-j.val)*m^(j.val+1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [abs_div,abs_of_pos hs',hr',hpow,div_pow]
    field_simp

/-- A rational number below an integer fraction, from an integer inequality. -/
private theorem r75_lt_frac {r : ℚ} {a N : ℤ} {b D : ℕ} (hr : r=a/b) (hb : 0<b) (hD : 0<D)
    (h : a*D<N*b) : r<(N:ℚ)/(D:ℚ) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,div_lt_div_iff₀ hb' hD']
  exact_mod_cast h

/-- The absolute value of an integer fraction below a rational number. -/
private theorem r75_abs_lt {r : ℚ} {N a : ℤ} {D b : ℕ} (hr : r=a/b) (hD : 0<D) (hb : 0<b)
    (h : |N| *b<a*D) : |(N:ℚ)/(D:ℚ)|<r := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,abs_div,abs_of_pos hD',div_lt_div_iff₀ hD' hb']
  have h' : ((|N| *b:ℤ):ℚ)<((a*D:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  exact h'

open WholeIntervalPolynomial.Certificate in
private def r75_YS : Scaled := (⟨[7],10⟩ : Scaled).sub Scaled.var

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_Y : r75_YS.Rep (C (7/10)-X) :=
  (r75_repC 7 10 (by norm_num) (by norm_num)).sub Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r75_S5cS : Scaled :=
  (r75_YS.sub ((⟨[1],6⟩ : Scaled).mul (r75_YS.pow 3))).add ((⟨[1],120⟩ : Scaled).mul (r75_YS.pow 5))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_S5c : r75_S5cS.Rep (S5.comp (C (7/10)-X)) := by
  have e : S5.comp (C (7/10)-X)=(C (7/10)-X)-C (1/6)*(C (7/10)-X)^3+
      C (1/120)*(C (7/10)-X)^5 := by
    simp only [S5,add_comp,sub_comp,mul_comp,C_comp,X_comp,X_pow_comp]
  rw [e]
  exact (r75_rep_Y.sub ((r75_repC 1 6 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 3))).add
    ((r75_repC 1 120 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 5))

open WholeIntervalPolynomial.Certificate in
private def r75_C4cS : Scaled :=
  ((Scaled.ofNat 1).sub ((⟨[1],2⟩ : Scaled).mul (r75_YS.pow 2))).add
    ((⟨[1],24⟩ : Scaled).mul (r75_YS.pow 4))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_C4c : r75_C4cS.Rep (C4.comp (C (7/10)-X)) := by
  have e : C4.comp (C (7/10)-X)=1-C (1/2)*(C (7/10)-X)^2+C (1/24)*(C (7/10)-X)^4 := by
    simp only [C4,add_comp,sub_comp,mul_comp,C_comp,X_pow_comp,one_comp]
  rw [e]
  exact (Scaled.rep_one.sub ((r75_repC 1 2 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 2))).add
    ((r75_repC 1 24 (by norm_num) (by norm_num)).mul (r75_rep_Y.pow 4))

open WholeIntervalPolynomial.Certificate in
private def r75_APS : Scaled :=
  (((⟨[13753],50000⟩ : Scaled).sub ((⟨[13607],12500⟩ : Scaled).mul Scaled.var)).sub
    ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 2))).add ((⟨[1],6⟩ : Scaled).mul (Scaled.var.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_AP : r75_APS.Rep AP :=
  (((r75_repC 13753 50000 (by norm_num) (by norm_num)).sub
    ((r75_repC 13607 12500 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
    ((r75_repC 1 6 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).add
    ((r75_repC 1 6 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 3))

open WholeIntervalPolynomial.Certificate in
private def r75_BPS : Scaled :=
  (((⟨[32033],25000⟩ : Scaled).sub ((⟨[2729],4000⟩ : Scaled).mul Scaled.var)).sub
    ((⟨[5],24⟩ : Scaled).mul (Scaled.var.pow 2))).add ((⟨[5],24⟩ : Scaled).mul (Scaled.var.pow 3))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_BP : r75_BPS.Rep BP :=
  (((r75_repC 32033 25000 (by norm_num) (by norm_num)).sub
    ((r75_repC 2729 4000 (by norm_num) (by norm_num)).mul Scaled.rep_var)).sub
    ((r75_repC 5 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 2))).add
    ((r75_repC 5 24 (by norm_num) (by norm_num)).mul (Scaled.rep_var.pow 3))

open WholeIntervalPolynomial.Certificate in
private def r75_shortS : Scaled :=
  ((⟨[13],12⟩ : Scaled).sub ((⟨[2],5⟩ : Scaled).mul r75_S5cS)).sub
    ((r75_C4cS.pow 2).mul (r75_BPS.add ((⟨[500],389⟩ : Scaled).mul (r75_APS.pow 2))))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_short : r75_shortS.Rep shortPolynomial :=
  ((r75_repC 13 12 (by norm_num) (by norm_num)).sub
    ((r75_repC 2 5 (by norm_num) (by norm_num)).mul r75_rep_S5c)).sub
    ((r75_rep_C4c.pow 2).mul (r75_rep_BP.add
      ((r75_repC 500 389 (by norm_num) (by norm_num)).mul (r75_rep_AP.pow 2))))

open WholeIntervalPolynomial.Certificate in
private theorem r75_rep_shortT : (r75_shortS.center 1 25 3 25).Rep shortTranslated := by
  rw [shortTranslated,r75_shift_eq]
  exact r75_rep_short.centered 1 25 3 25 (by norm_num) (by norm_num) (by norm_num)

theorem short_certificate :
    shortTranslated=C (shortTranslated.coeff 0)+C (shortTranslated.coeff 1)*X+
      C (shortTranslated.coeff 2)*X^2+PowerTailBounds.tail shortTranslated 3 12 ∧
    (21067/2500000:ℚ)<shortTranslated.coeff 0 ∧
    |shortTranslated.coeff 1|<(77231/10000000:ℚ) ∧
    (6217/10000:ℚ)<shortTranslated.coeff 2 ∧
    (4307/20000:ℚ)<shortTranslated.coeff 2-
      PowerTailBounds.norm shortTranslated 3 12 (6/25) := by
  have hs : (r75_shortS.center 1 25 3 25).s≠0 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h := r75_split 3 12 (lt_of_le_of_lt (r75_rep_shortT.natDegree_le hs) (by decide +kernel))
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,
      pow_one] at h
    exact h
  · rw [r75_rep_shortT.coeff hs 0]
    exact r75_lt_frac (a:=21067) (b:=2500000) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · rw [r75_rep_shortT.coeff hs 1]
    exact r75_abs_lt (a:=77231) (b:=10000000) (by norm_num) (by decide +kernel) (by norm_num)
      (by decide +kernel)
  · rw [r75_rep_shortT.coeff hs 2]
    exact r75_lt_frac (a:=6217) (b:=10000) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · rw [r75_coeff_sub_norm r75_rep_shortT hs 2 3 12 6 25 (by norm_num) (by norm_num)]
    exact r75_lt_frac (a:=4307) (b:=20000) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)

theorem short_positive {d : ℝ} (hd : d∈Icc (0:ℝ) (9/25)) :
    (167/20000:ℝ)<aeval d shortPolynomial := by
  obtain ⟨x,hxd⟩ : ∃ x : ℝ,x=d-3/25 := ⟨_,rfl⟩
  have hx : |x|≤((6/25:ℚ):ℝ) := by
    rw [abs_le,hxd]
    push_cast
    exact ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have ht := PowerTailBounds.quadratic_lower short_certificate.1 (by norm_num) hx
  have h0 : (21067/2500000:ℝ)<(shortTranslated.coeff 0:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr short_certificate.2.1
    push_cast at hh
    exact hh
  have h1 : |(shortTranslated.coeff 1:ℝ)|<(77231/10000000:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr short_certificate.2.2.1
    push_cast at hh
    exact hh
  have h2 : (4307/20000:ℝ)<(shortTranslated.coeff 2:ℝ)-
      (PowerTailBounds.norm shortTranslated 3 12 (6/25):ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr short_certificate.2.2.2.2
    push_cast at hh
    exact hh
  have hlin : -(77231/10000000)*|x|≤(shortTranslated.coeff 1:ℝ)*x := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg x)
    rw [←abs_mul] at hh
    have hh' := (abs_le.mp hh).1
    linarith
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(21067/2500000:ℝ)) (b:=-(77231/10000000:ℝ)) (x:=|x|)
    (show (0:ℝ)<4307/20000 by norm_num)
  have hreserve : (167/20000:ℝ)<21067/2500000-
      (77231/10000000:ℝ)^2/(4*(4307/20000)) := by norm_num
  have he : aeval x shortTranslated=aeval d shortPolynomial := by
    have hx' : ((3/25:ℚ):ℝ)+x=d := by rw [hxd]; push_cast; ring
    simp only [shortTranslated,DirectedPowerBounds.shift_eval,hx']
  rw [he] at ht
  rw [sq_abs] at hmin
  nlinarith

@[simp] theorem AP_eval (d : ℝ) : aeval d AP=A d := by
  simp [AP,A]
  ring
@[simp] theorem BP_eval (d : ℝ) : aeval d BP=B d := by simp [BP,B]

theorem short_model_reserve {d : ℝ} (hd : d∈Icc (0:ℝ) (9/25)) :
    0<13/12-(2/5)*aeval (frameCap-d) S5-
      (aeval (frameCap-d) C4)^2*model d := by
  have hp := short_positive hd
  have he : aeval d shortPolynomial=13/12-(2/5)*aeval (frameCap-d) S5-
      (aeval (frameCap-d) C4)^2*model d := by
    simp [shortPolynomial,aeval_comp,frameCap,model,AP_eval,BP_eval]
  rw [he] at hp
  linarith

def interiorPolynomial : ℚ[X] := C (1/1200)-C (9/184)*X+C (79057/211600)*X^2-
  C (881/1150)*X^3+C (375/529)*X^4

theorem interior_positive {y : ℝ} (hy : y∈Icc (27/100:ℝ) (129/200)) :
    0<aeval y interiorPolynomial := by
  have h1 : 0≤y-27/100 := sub_nonneg.2 hy.1
  have h2 : 0≤129/200-y := sub_nonneg.2 hy.2
  simp only [interiorPolynomial,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

end Certificate

def AFirst (d : ℝ) : ℝ := -(13607/12500)-d/3+d^2/2
def lateCubic (d : ℝ) : ℝ := 960319/800000-(41011/100000)*d-d^2/6+d^3/6

theorem A_derivative (d : ℝ) : HasDerivAt A (AFirst d) d := by
  have h := ((((hasDerivAt_id d).const_mul (13607/12500:ℝ)).const_sub (13753/50000:ℝ)).sub
    ((hasDerivAt_pow 2 d).div_const 6)).add ((hasDerivAt_pow 3 d).div_const 6)
  convert h using 1
  · rfl
  · simp only [AFirst,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,show (3:ℕ)-1=2 from rfl,pow_one]
    ring

theorem A_late_upper {d : ℝ} (hd : d∈Icc (9/25:ℝ) frameCap) : A d< -(389/4000:ℝ) := by
  have hm : AntitoneOn A (Icc (9/25:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (A_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => A_derivative d)
    intro d hd
    have h1 := hd.1
    have h2 := hd.2
    simp only [frameCap] at h2
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith) h2.le 2
    simp only [AFirst]
    nlinarith
  have hh := hm (by norm_num [frameCap]) hd hd.1
  have hA : A (9/25)=-(163307/1250000) := by norm_num [A]
  linarith

theorem lateCubic_derivative (d : ℝ) : HasDerivAt lateCubic
    (-(41011/100000)-d/3+d^2/2) d := by
  have h := ((((hasDerivAt_id d).const_mul (41011/100000:ℝ)).const_sub (960319/800000:ℝ)).sub
    ((hasDerivAt_pow 2 d).div_const 6)).add ((hasDerivAt_pow 3 d).div_const 6)
  convert h using 1
  · rfl
  · simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,show (3:ℕ)-1=2 from rfl,pow_one]
    ring

theorem lateCubic_upper {d : ℝ} (hd : d∈Icc (9/25:ℝ) frameCap) : lateCubic d<1039/1000 := by
  have hm : AntitoneOn lateCubic (Icc (9/25:ℝ) frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun d _ => (lateCubic_derivative d).continuousAt.continuousWithinAt)
      (fun d _ => lateCubic_derivative d)
    intro d hd
    have h1 := hd.1
    have h2 := hd.2
    simp only [frameCap] at h2
    have hd2 := pow_le_pow_left₀ (show 0≤d by linarith) h2.le 2
    nlinarith
  have hh := hm (by norm_num [frameCap]) hd hd.1
  have hL : lateCubic (9/25)=20778703/20000000 := by norm_num [lateCubic]
  linarith

theorem late_slope_upper {p q d : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax)
    (hd : d∈Icc (9/25:ℝ) frameCap) : OrdinaryNegativeSlope.Vd Secondary.R p q d<1039/1000 := by
  have hmodel := quadratic_model hp hp0 hq ⟨by linarith [hd.1],hd.2⟩
  have hA := A_late_upper hd
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show A d+389/4000≤0 by linarith) (sub_nonneg.mpr hq.1)
  have he : B d+A d*(q-q0)-(389/2000)*(q-q0)^2=
      lateCubic d+(A d+389/4000)*(q-1)-(389/2000)*(q-1)^2 := by
    dsimp [A,B,lateCubic,q0]
    ring
  rw [he] at hmodel
  have hh : OrdinaryNegativeSlope.Vd Secondary.R p q d<lateCubic d := by
    nlinarith [sq_nonneg (q-1)]
  exact hh.trans (lateCubic_upper hd)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
end
end
end
