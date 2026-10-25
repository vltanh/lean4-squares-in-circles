module

public import SquaresInCircles.Eight.Owners.GA.DMinorantCalculus
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2CurvatureConstants
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Ranges
public import SquaresInCircles.Eight.Owners.PowerTailBounds

/-!
# Eight squares: the low G-pair constants before E-angle reduction

The lower curvature bound is the single degree-sixteen polynomial `reserve` in
`x = 1/6 - θ` (`polynomial_positive`). Its positive higher coefficients and its completed
quadratic are kept as they are.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope

namespace Certificate
open Polynomial

def k : ℚ[X] := C (1677/2500)-C (3/20)*X+C 4*X^2
def l : ℚ[X] := C (10073/10000)+C (17/10)*X+C (11/5)*X^2
def reserve : ℚ[X] := C (4*(9789/2500))*k^4*l^4-(k^2+l^2)^3

/-- `reserve` is `c₂ (x - 271/5330)² + c₁' x + c₀'` plus `∑ cⱼ xʲ` (`j ≥ 3`) with positive `c₀'`,
`c₁'`, `c₂` and `cⱼ`; `linarith` finds this decomposition. -/
theorem polynomial_positive {x : ℝ} (hx : 0≤x) : 0<aeval x reserve := by
  simp only [reserve,k,l,map_sub,map_mul,map_pow,map_add,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [sq_nonneg (x-271/5330),pow_nonneg hx 3,pow_nonneg hx 4,pow_nonneg hx 5,
    pow_nonneg hx 6,pow_nonneg hx 7,pow_nonneg hx 8,pow_nonneg hx 9,pow_nonneg hx 10,
    pow_nonneg hx 11,pow_nonneg hx 12,pow_nonneg hx 13,pow_nonneg hx 14,pow_nonneg hx 15,
    pow_nonneg hx 16]

theorem original_positive {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<4*qCap*(Explicit.k .low θ)^4*(Explicit.l .low θ)^4-
      ((Explicit.k .low θ)^2+(Explicit.l .low θ)^2)^3 := by
  have hh := polynomial_positive (x:=1/6-θ) (by linarith [hθ.2])
  have hk : aeval (1/6-θ) k=Explicit.k .low θ := by
    simp [k,Explicit.k,Explicit.L]
    ring
  have hl : aeval (1/6-θ) l=Explicit.l .low θ := by
    simp [l,Explicit.l,Explicit.L]
    ring
  simp only [reserve,map_sub,map_mul,map_pow,map_add,aeval_C,eq_ratCast,hk,hl] at hh
  have hq : ((4:ℚ):ℝ)*((9789/2500:ℚ):ℝ)=4*qCap := by norm_num [qCap]
  rw [hq] at hh
  exact hh

end Certificate

/-- Increasing either positive coefficient increases the zero-angle norm slope. This is a scalar
comparison; no witness changes. -/
theorem zero_slope_rectangle {p q P Q : ℝ}
    (hp : 0<p) (hq : 0<q) (hpP : p≤P) (hqQ : q≤Q) :
    NegativeAPositiveTD.Curvature.slopeZero p q≤NegativeAPositiveTD.Curvature.slopeZero P Q := by
  have hP := hp.trans_le hpP
  have hQ := hq.trans_le hqQ
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hp hq ht
  have hN := pairNorm_pos hP hQ ht
  have hn2 := pairNorm_sq hp hq ht
  have hN2 := pairNorm_sq hP hQ ht
  simp only [pairEnergy,Real.sin_zero,mul_zero,add_zero] at hn2 hN2
  have hp2 := pow_le_pow_left₀ hp.le hpP 2
  have hq2 := pow_le_pow_left₀ hq.le hqQ 2
  have h₁ := mul_le_mul_of_nonneg_left hq2 (mul_nonneg (sq_nonneg p) (sq_nonneg P))
  have h₂ := mul_le_mul_of_nonneg_left hp2 (mul_nonneg (sq_nonneg q) (sq_nonneg Q))
  have hsq : (p*q*pairNorm P Q 0)^2≤(P*Q*pairNorm p q 0)^2 := by
    simp only [mul_pow]
    rw [hn2,hN2]
    nlinarith only [h₁,h₂]
  have hcross : p*q*pairNorm P Q 0≤P*Q*pairNorm p q 0 := by
    nlinarith [mul_pos (mul_pos hp hq) hN,mul_pos (mul_pos hP hQ) hn]
  have hdiv := (div_le_div_iff₀ hn hN).2 hcross
  have hh := mul_le_mul_of_nonneg_left hdiv (Real.sqrt_nonneg qCap)
  simp only [NegativeAPositiveTD.Curvature.slopeZero,pairProduct]
  rw [mul_div_assoc R (p*q),mul_div_assoc R (P*Q)]
  exact hh

theorem zero_slope_upper {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    NegativeAPositiveTD.Curvature.slopeZero (Explicit.k .low θ) (Explicit.l .low θ)<131/100 := by
  have hr := Explicit.low_ranges hθ
  have hh := zero_slope_rectangle (by linarith [hr.1] : 0<Explicit.k .low θ)
    (by linarith [hr.2.2.1] : 0<Explicit.l .low θ) hr.2.1.le hr.2.2.2.1.le
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=(757/1000:ℝ)) (q:=(1352/1000:ℝ)) (by norm_num) (by norm_num) ht
  have hn2 := pairNorm_sq (p:=(757/1000:ℝ)) (q:=(1352/1000:ℝ)) (by norm_num) (by norm_num) ht
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have he : NegativeAPositiveTD.Curvature.slopeZero (757/1000) (1352/1000)<131/100 := by
    unfold NegativeAPositiveTD.Curvature.slopeZero
    apply quotient_lt_of_square hn (by norm_num)
    rw [mul_pow,hR2,hn2]
    norm_num [pairProduct,pairEnergy,qCap]
  exact hh.trans_lt he

theorem curvature_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (1/2:ℝ)<curvatureZero R (Explicit.k .low θ) (Explicit.l .low θ) := by
  have hr := Explicit.low_ranges hθ
  have hk : 0<Explicit.k .low θ := by linarith [hr.1]
  have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos hk hl ht
  have hn2 := pairNorm_sq hk hl ht
  simp only [pairEnergy,Real.sin_zero,mul_zero,add_zero] at hn2
  have hpoly := Certificate.original_positive hθ
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have hnum : 0<2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 := by
    have hR : 0<R := by linarith [NegativeAPositiveTD.Curvature.radius_bounds.1]
    positivity
  have hsquare : ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2<
      (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2 := by
    rw [show ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2=
      ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^2)^3 by ring,hn2,
      show (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2=
        4*R^2*(Explicit.k .low θ)^4*(Explicit.l .low θ)^4 by ring,hR2]
    generalize qCap = Q at hpoly ⊢
    linarith only [hpoly]
  have hcross : (pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3<
      2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 :=
    lt_of_pow_lt_pow_left₀ 2 hnum.le hsquare
  unfold curvatureZero
  apply (lt_div_iff₀ (pow_pos hn 3)).2
  dsimp [pairProduct]
  generalize R = R0 at hcross ⊢
  linarith only [hcross]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowG
