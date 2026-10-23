module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighShape

/-!
# Actual high-T support inputs for the DE3 / BT3 endpoint transfer

Uncompiled Section 8.2. The total-dependent tilt is retained in its
circle support. The cubic square-root upper bound is proved by an
exact positive-square identity, not presumed from the cubic norm masses.
The baseline lower polynomial and all four original norm bounds are
then established at the same original total angle.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighTransfer
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S9 S11 C10 C12 taylor_bounds)

abbrev native (θ : ℝ) : ℝ := θ-(Certificate.L:ℝ)
abbrev k (θ : ℝ) := Explicit.k .high θ
abbrev l (θ : ℝ) := Explicit.l .high θ
abbrev m (θ : ℝ) := Explicit.m .high θ
abbrev c (θ : ℝ) := Explicit.c .high θ θ
abbrev eta (θ : ℝ) := Explicit.eta .high θ

def cubic (w : ℝ) : ℝ := 1+w/2-w^2/8+w^3/16

lemma cubic_nonnegative {w : ℝ} (hw : 0≤w) : 0≤cubic w := by
  have he : cubic w=1+w*((w-1)^2+7)/16 := by dsimp [cubic]; ring
  rw [he]
  positivity

theorem sqrt_cubic_upper {w : ℝ} (hw : 0≤w) : Real.sqrt (1+w)≤cubic w := by
  have hs := Real.sq_sqrt (show 0≤1+w by linarith)
  have hp := cubic_nonnegative hw
  have hid : (cubic w)^2-(1+w)=w^4*((w-2)^2+16)/256 := by
    dsimp [cubic]
    ring
  have hnon : 0≤w^4*((w-2)^2+16)/256 := by positivity
  nlinarith [Real.sqrt_nonneg (1+w)]

lemma sigma_lower_data {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0≤aeval (native θ) Certificate.etaIncrement ∧
      Explicit.sigma .high θ≤aeval (native θ) Certificate.sigmaUpper := by
  let e0 : ℝ := Certificate.eta0
  let e := eta θ
  let w : ℝ := (e^2-e0^2)/(1+e0^2)
  have he := Explicit.high_eta hθ
  have he0 : 0≤e0 := by norm_num [e0,Certificate.eta0]
  have hege : e0≤e := he.1
  have hepos : 0≤e := he0.trans hege
  have hw : 0≤w := div_nonneg (by nlinarith) (by positivity)
  have hwpoly : aeval (native θ) Certificate.etaIncrement=w := by
    simp only [Certificate.etaIncrement,map_mul,map_sub,map_pow,aeval_C,Certificate.highEta_eval,
      HighShape.native_total,native]
    dsimp [w,e,e0,eta]
    push_cast
    ring
  have h0 : 0<Real.sqrt (1+e0^2) := Real.sqrt_pos.mpr (by positivity)
  have h1 : 0<Real.sqrt (1+w) := Real.sqrt_pos.mpr (by positivity)
  have hs0 := Real.sq_sqrt (show 0≤1+e0^2 by positivity)
  have hs1 := Real.sq_sqrt (show 0≤1+w by positivity)
  have hse := Real.sq_sqrt (show 0≤1+e^2 by positivity)
  have hprod : (1+e0^2)*(1+w)=1+e^2 := by
    dsimp [w]
    field_simp [show (1+e0^2:ℝ)≠0 by positivity]
    ring
  have hroot : Real.sqrt (1+e^2)=Real.sqrt (1+e0^2)*Real.sqrt (1+w) := by
    have hsq : (Real.sqrt (1+e0^2)*Real.sqrt (1+w))^2=1+e^2 := by
      rw [mul_pow,hs0,hs1,hprod]
    nlinarith [Real.sqrt_nonneg (1+e^2),mul_pos h0 h1]
  have hbase : R*Real.sqrt (1+e0^2)≤(Certificate.sigmabar:ℝ)+(1+e0)/2 := by
    have hh := NonnegativeTotals.Charges.sigma_upper
    dsimp [PositiveTD.sigma,PositiveTD.eta,Certificate.sigmabar,e0,Certificate.eta0] at *
    linarith
  have hupper := mul_le_mul hbase (sqrt_cubic_upper hw) h1.le
    (show 0≤(Certificate.sigmabar:ℝ)+(1+e0)/2 by norm_num [Certificate.sigmabar,e0,Certificate.eta0])
  refine ⟨by rw [hwpoly]; exact hw,?_⟩
  simp only [Certificate.sigmaUpper,map_sub,map_mul,map_add,map_pow,map_one,aeval_C,
    Certificate.highEta_eval,HighShape.native_total,hwpoly]
  push_cast
  dsimp [Explicit.sigma,fullSupport]
  rw [show (1:ℝ)^2+(eta θ)^2=1+e^2 by dsimp [e]; ring,hroot]
  dsimp [cubic,e,e0,eta,Certificate.eta0] at *
  nlinarith only [hupper]

def base (θ : ℝ) : ℝ := 2*k θ+3*l θ+3+
  m θ*(1+2*Real.cos θ+(1/2+(3/2)*eta θ-Explicit.sigma .high θ)*Real.sin θ)

def norms (θ : ℝ) : Fin 4→ℝ :=
  ![pairNorm (k θ) 1 0,pairNorm (k θ) (l θ) 0,
    pairNorm (l θ) (m θ) 0,pairNorm 1 (c θ) 0]

lemma polynomial_sine_negative {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) Certificate.highSineCoefficient≤0 := by
  have hc := Certificate.high_auxiliary_certificate.2.1
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 (HighShape.native_domain hθ)
  simp only [map_neg] at hh
  linarith

theorem base_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) Certificate.highBase≤base θ := by
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hsig := (sigma_lower_data hθ).2
  have hs := (transport_trig (Explicit.frame_domain .high hθ)).2.2.1
  have hcoef : aeval (native θ) Certificate.highSineCoefficient≤
      1/2+(3/2)*eta θ-Explicit.sigma .high θ := by
    simp only [Certificate.highSineCoefficient,map_add,map_mul,map_sub,aeval_C,
      Certificate.highEta_eval,HighShape.native_total]
    norm_num
    linarith
  have hsin := mul_le_mul_of_nonpos_left ht.2.2.1 (polynomial_sine_negative hθ)
  have hsin' := mul_le_mul_of_nonneg_right hcoef hs
  have hinner : 1+2*aeval θ C10+
      aeval (native θ) Certificate.highSineCoefficient*aeval θ S9≤
      1+2*Real.cos θ+(1/2+(3/2)*eta θ-Explicit.sigma .high θ)*Real.sin θ := by
    linarith [ht.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hinner
    (show 0≤m θ by linarith [(Explicit.high_bounds hθ).m_lower])
  simp only [Certificate.highBase,map_add,map_mul,map_one,aeval_C,aeval_comp,
    Certificate.highK_eval,Certificate.highL_eval,Certificate.highM_eval,
    Certificate.theta_eval,HighShape.native_total]
  dsimp [base,k,l,m]
  linarith

lemma base_polynomial_positive {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<aeval (native θ) (Certificate.highBase-1) := by
  have hc := Certificate.high_auxiliary_certificate.1
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 (HighShape.native_domain hθ)
  norm_num at hh
  linarith

theorem baseline_identity {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.fullBaseline .high 0 θ 0=base θ-R*(norms θ 0+norms θ 1+norms θ 2+norms θ 3) := by
  rw [Explicit.fullBaseline]
  simp only [zero_add,Explicit.sec,NegativeELargeA.secant,Real.cos_zero,Real.tan_zero,
    div_one,sub_self,mul_zero,sub_zero,add_zero,TwoPositive.ASupport.charge_zero]
  rw [edgeWidth_positive_formula (Explicit.frame_domain .high hθ)]
  rw [fullSupport_pair 1 (k θ),fullSupport_pair (k θ) (l θ),
    fullSupport_pair (l θ) (m θ),fullSupport_pair 1 (c θ),pairNorm_symm 1 (k θ) 0]
  dsimp [base,norms,k,l,m,c,eta,Explicit.c]
  ring

theorem norm_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (norms θ i)^2≤aeval (native θ) (Certificate.highNormZero i) := by
  have hc := HighShape.coefficient_majorant hθ
  have hc0 : 0≤c θ := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,(Explicit.high_bounds hθ).m_lower]
  have hc2 := pow_le_pow_left₀ hc0 hc 2
  fin_cases i <;>
    simp only [norms,Certificate.highNormZero,Matrix.cons_val_succ,Matrix.cons_val_zero,
      map_add,map_pow,map_one,Certificate.highK_eval,Certificate.highL_eval,
      Certificate.highM_eval,HighShape.native_total,
      NonnegativeTotals.Analytic.norm_zero_square,one_pow]
  · dsimp [k]; ring_nf; exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact add_le_add_left hc2 1

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighTransfer
