module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowNegative

/-!
# The low G-pair constants before E-angle reduction

Uncompiled transcription of the complete scalar companion, (25)--(27),
and the angle companion, (33)--(34). The lower curvature certificate is
the single degree-sixteen polynomial in x = 1/6 - theta. Its positive
higher coefficients and its completed quadratic are kept explicitly.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowG
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryCurvatureBounds OrdinaryNegativeSlope
open NegativeAPositiveTD (Curvature)

namespace Certificate
open Polynomial

def k : ℚ[X] := C (1677/2500)-C (3/20)*X+C 4*X^2
def l : ℚ[X] := C (10073/10000)+C (17/10)*X+C (11/5)*X^2
def reserve : ℚ[X] := C (4*(9789/2500))*k^4*l^4-(k^2+l^2)^3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_certificate :
    reserve=C (reserve.coeff 0)+C (reserve.coeff 1)*X+
      C (reserve.coeff 2)*X^2+PowerTailBounds.tail reserve 3 14 ∧
    (123/1000:ℚ)<reserve.coeff 0 ∧
    -(813/500:ℚ)<reserve.coeff 1 ∧ (1599/100:ℚ)<reserve.coeff 2 ∧
    (∀j : Fin 14,(177:ℚ)<reserve.coeff (j.val+3)) := by decide

theorem polynomial_positive {x : ℝ} (hx : 0≤x) : 0<aeval x reserve := by
  have htail : 0≤aeval x (PowerTailBounds.tail reserve 3 14) := by
    simp only [PowerTailBounds.tail,map_sum,map_mul,map_pow,aeval_C,aeval_X]
    apply Finset.sum_nonneg
    intro j _
    have hc : (0:ℝ)<(reserve.coeff (j.val+3):ℝ) := by
      have hh := (coefficient_certificate.2.2.2.2 j)
      have hh' : (177:ℝ)<(reserve.coeff (j.val+3):ℝ) := by exact_mod_cast hh
      linarith
    exact mul_nonneg hc.le (pow_nonneg hx _)
  have h0 : (123/1000:ℝ)<(reserve.coeff 0:ℝ) := by exact_mod_cast coefficient_certificate.2.1
  have h1 : -(813/500:ℝ)<(reserve.coeff 1:ℝ) := by exact_mod_cast coefficient_certificate.2.2.1
  have h2 : (1599/100:ℝ)<(reserve.coeff 2:ℝ) := by exact_mod_cast coefficient_certificate.2.2.2.1
  have hm1 := mul_le_mul_of_nonneg_right h1.le hx
  have hm2 := mul_le_mul_of_nonneg_right h2.le (sq_nonneg x)
  have hi := congrArg (fun p : ℚ[X] => aeval x p) coefficient_certificate.1
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X] at hi
  nlinarith [sq_nonneg (x-271/5330)]

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
  simpa [reserve,hk,hl,qCap] using hh

end Certificate

/-- Increasing either positive coefficient increases the zero-angle norm
slope. This is a scalar comparison, not a source-witness replacement. -/
theorem zero_slope_rectangle {p q P Q : ℝ}
    (hp : 0<p) (hq : 0<q) (hpP : p≤P) (hqQ : q≤Q) :
    Curvature.slopeZero p q≤Curvature.slopeZero P Q := by
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
    rw [mul_pow,mul_pow,hn2,hN2]
    nlinarith only [h₁,h₂]
  have hcross : p*q*pairNorm P Q 0≤P*Q*pairNorm p q 0 := by
    nlinarith [mul_pos (mul_pos hp hq) hN,mul_pos (mul_pos hP hQ) hn]
  have hdiv := (div_le_div_iff₀ hn hN).2 hcross
  have hh := mul_le_mul_of_nonneg_left hdiv (Real.sqrt_nonneg qCap)
  simpa [Curvature.slopeZero,pairProduct,mul_div_assoc] using hh

theorem zero_slope_upper {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Curvature.slopeZero (Explicit.k .low θ) (Explicit.l .low θ)<131/100 := by
  have hr := Explicit.low_ranges hθ
  have hh := zero_slope_rectangle (by linarith [hr.1] : 0<Explicit.k .low θ)
    (by linarith [hr.2.2.1] : 0<Explicit.l .low θ) hr.2.1.le hr.2.2.2.1.le
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hn := pairNorm_pos (p:=(757/1000:ℝ)) (q:=(169/125:ℝ)) (by norm_num) (by norm_num) ht
  have hn2 := pairNorm_sq (p:=(757/1000:ℝ)) (q:=(169/125:ℝ)) (by norm_num) (by norm_num) ht
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have he : Curvature.slopeZero (757/1000) (169/125)<131/100 := by
    unfold Curvature.slopeZero
    apply quotient_lt_of_square hn (by norm_num)
    norm_num [pairProduct,pairEnergy,Real.sin_zero,mul_pow,hR2,qCap] at hn2 ⊢
    nlinarith only [hn2]
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
    have hR : 0<R := by linarith [Curvature.radius_bounds.1]
    positivity
  have hsquare : ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2<
      (2*R*(Explicit.k .low θ*Explicit.l .low θ)^2)^2 := by
    rw [show ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3)^2=
      ((pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^2)^3 by ring,hn2]
    nlinarith [hR2]
  have hcross : (pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0)^3<
      2*R*(Explicit.k .low θ*Explicit.l .low θ)^2 := by
    nlinarith [pow_pos hn 3]
  unfold curvatureZero
  apply (lt_div_iff₀ (pow_pos hn 3)).2
  dsimp [pairProduct]
  nlinarith only [hcross]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowG
