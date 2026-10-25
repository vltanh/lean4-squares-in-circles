module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PositiveSlopes
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNorms

/-!
# Eight squares: exact reference reserves for the low-total B/H rectangle

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
