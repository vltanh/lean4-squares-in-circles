module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowNegative
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2CurvatureConstants

/-!
# Exact reference reserves for the low-total B/H rectangle

Uncompiled Section 4.2 of the negative-DE / positive-BT3 hand proof.
Only the intrinsic coefficient corner k=.5866, m=1.1642 and the original
angle endpoints 0 and 7/10 occur. Every radical comparison is reduced
to a positive rational square. These are not samples of the rectangle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowRectangle
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
  linarith

lemma cap_taylor :
    0≤Polynomial.aeval frameCap S11 ∧ Polynomial.aeval frameCap S11≤Real.sin frameCap ∧
      Real.sin frameCap≤Polynomial.aeval frameCap S9 ∧
      0≤Polynomial.aeval frameCap C10 ∧ Polynomial.aeval frameCap C10≤Real.cos frameCap := by
  have ht := taylor_bounds (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  exact ⟨ht.1,ht.2.1,ht.2.2.1,by linarith [ht.2.2.2.1],ht.2.2.2.2.1⟩

theorem B_cap_curvature : (1923/2000:ℝ)<curvature R 1 M frameCap := by
  let sl := Polynomial.aeval frameCap S11
  let su := Polynomial.aeval frameCap S9
  let A : ℝ := 1+M^2
  let n := pairNorm 1 M frameCap
  let lower : ℝ := R*M*(A*sl+M*(1+sl^2))
  have ht := cap_taylor
  have hn : 0<n := pairNorm_pos (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
    (by norm_num [frameCap] : |frameCap|≤frameCap)
  have hn2 := pairNorm_sq (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
    (by norm_num [frameCap] : |frameCap|≤frameCap)
  have hN : n^2≤A+2*M*su := by
    dsimp [pairEnergy,pairProduct,n,A] at hn2 ⊢
    nlinarith only [hn2,mul_le_mul_of_nonneg_left ht.2.2.1 (by norm_num [M] : 0≤2*M)]
  have hN3 := pow_le_pow_left₀ (sq_nonneg n) hN 3
  have hrat : (1923/2000:ℝ)^2*(A+2*M*su)^3<lower^2 := by
    dsimp [lower]
    rw [mul_pow,mul_pow,radius_sq]
    norm_num [A,sl,su,M,qCap,frameCap,S11,S9,S5,C4]
  have hs2 := pow_le_pow_left₀ ht.1 ht.2.1 2
  have hfactor : A*sl+M*(1+sl^2)≤
      A*Real.sin frameCap+M*(1+(Real.sin frameCap)^2) := by
    have h₁ := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A by dsimp [A]; positivity)
    have h₂ := mul_le_mul_of_nonneg_left hs2 (by norm_num [M] : 0≤M)
    linarith
  have hlower := mul_le_mul_of_nonneg_left hfactor
    (show 0≤R*M by positivity)
  have hquot : (1923/2000:ℝ)<lower/n^3 := by
    apply lower_quotient_of_square
      (by dsimp [lower]; have hsl : 0≤sl := ht.1; positivity) (pow_pos hn 3) (by norm_num)
    have hpow : (n^3)^2=(n^2)^3 := by ring
    rw [hpow]
    nlinarith only [hrat,hN3]
  have hcompare := div_le_div_of_nonneg_right hlower (pow_nonneg hn.le 3)
  have hid : curvature R 1 M frameCap=
      R*M*(A*Real.sin frameCap+M*(1+(Real.sin frameCap)^2))/n^3 := by
    dsimp [curvature,normD2,pairProduct,pairEnergy,A,n]
    ring
  rw [hid]
  exact hquot.trans_le hcompare

theorem H_negative_cap_slope : (513/1000:ℝ)<Vd R k0 1 frameCap := by
  let sl := Polynomial.aeval frameCap S11
  let su := Polynomial.aeval frameCap S9
  let cl := Polynomial.aeval frameCap C10
  let n := pairNorm k0 1 (-frameCap)
  have ht := cap_taylor
  have hn : 0<n := pairNorm_pos (by norm_num [k0] : 0<k0) (by norm_num : (0:ℝ)<1)
    (by norm_num [frameCap] : |-frameCap|≤frameCap)
  have hn2 := pairNorm_sq (by norm_num [k0] : 0<k0) (by norm_num : (0:ℝ)<1)
    (by norm_num [frameCap] : |-frameCap|≤frameCap)
  have hN : n^2≤k0^2+1-2*k0*sl := by
    simp only [pairEnergy,pairProduct,Real.sin_neg,one_pow,mul_one] at hn2
    have hh := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num [k0] : 0≤2*k0)
    dsimp [n]
    linarith
  have hrat : (513/1000+su)^2*(k0^2+1-2*k0*sl)<(R*k0*cl)^2 := by
    rw [mul_pow,mul_pow,radius_sq]
    norm_num [sl,su,cl,k0,qCap,frameCap,S11,S9,S5,C10,C4]
  have hprod := mul_le_mul_of_nonneg_left hN (sq_nonneg (513/1000+su))
  have hquot : 513/1000+su<R*k0*cl/n := by
    apply lower_quotient_of_square (by have hcl : 0≤cl := ht.2.2.2.1; positivity) hn
      (by norm_num [su,frameCap,S9,S5,C4])
    linarith
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2 (show 0≤R*k0 by positivity)
  have hquot' := div_le_div_of_nonneg_right hcos hn.le
  have hid : Vd R k0 1 frameCap= -Real.sin frameCap+R*k0*Real.cos frameCap/n := by
    dsimp [Vd,mixedNDerivative,normD1,pairProduct,n]
    rw [zero_sub,Real.cos_neg]
    ring
  rw [hid]
  dsimp [su] at hquot
  linarith [ht.2.2.1]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowRectangle
