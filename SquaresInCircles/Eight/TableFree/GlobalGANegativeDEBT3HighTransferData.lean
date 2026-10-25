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

private lemma r72_td_nt (θ : ℝ) : native θ+(Certificate.L:ℝ)=θ := by simp [native]

private lemma r72_td_K (θ : ℝ) : aeval (native θ) Certificate.highK=k θ := by
  rw [Certificate.highK_eval,r72_td_nt]

private lemma r72_td_L (θ : ℝ) : aeval (native θ) Certificate.highL=l θ := by
  rw [Certificate.highL_eval,r72_td_nt]

private lemma r72_td_M (θ : ℝ) : aeval (native θ) Certificate.highM=m θ := by
  rw [Certificate.highM_eval,r72_td_nt]

private lemma r72_td_eta (θ : ℝ) : aeval (native θ) Certificate.highEta=eta θ := by
  rw [Certificate.highEta_eval,r72_td_nt]

private lemma r72_td_comp (θ : ℝ) (P : ℚ[X]) :
    aeval (native θ) (P.comp Certificate.theta)=aeval θ P := by
  rw [aeval_comp,Certificate.theta_eval,r72_td_nt]

private lemma r72_td_dom {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    native θ∈Icc ((0:ℚ):ℝ) ((Certificate.span:ℚ):ℝ) := by
  have hx := HighShape.native_domain hθ
  have hspan : ((Certificate.span:ℚ):ℝ)=8/15 := by
    norm_num [Certificate.span,Certificate.h,Certificate.L]
  rw [hspan,Rat.cast_zero]
  exact hx

lemma sigma_lower_data {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0≤aeval (native θ) Certificate.etaIncrement ∧
      Explicit.sigma .high θ≤aeval (native θ) Certificate.sigmaUpper := by
  have he := Explicit.high_eta hθ
  obtain ⟨e,hedef⟩ : ∃e:ℝ,e=eta θ := ⟨_,rfl⟩
  obtain ⟨w,hwdef⟩ : ∃w:ℝ,w=(e^2-(293/1000)^2)/(1+(293/1000)^2) := ⟨_,rfl⟩
  have he1 : (293/1000:ℝ)≤e := by rw [hedef]; exact he.1
  have hw : 0≤w := by
    rw [hwdef]; apply div_nonneg _ (by positivity); nlinarith
  have hwpoly : aeval (native θ) Certificate.etaIncrement=w := by
    simp only [Certificate.etaIncrement,map_mul,map_sub,map_pow,aeval_C,r72_td_eta,
      eq_ratCast,← hedef]
    rw [hwdef]
    push_cast [Certificate.eta0]
    ring
  have h1 : 0<Real.sqrt (1+w) := Real.sqrt_pos.mpr (by positivity)
  have hprod : (1+(293/1000:ℝ)^2)*(1+w)=1+e^2 := by
    rw [hwdef]; field_simp; ring
  have hroot : Real.sqrt (1+e^2)=Real.sqrt (1+(293/1000:ℝ)^2)*Real.sqrt (1+w) := by
    rw [← Real.sqrt_mul (by positivity),hprod]
  have hbase : R*Real.sqrt (1+(293/1000:ℝ)^2)≤
      (1415477291/1000000000:ℝ)+(1+293/1000)/2 := by
    have hh := NonnegativeTotals.Charges.sigma_upper
    simp only [PositiveTD.sigma,PositiveTD.eta,fullSupport,
      NonnegativeTotals.Certificate.sigmabar,one_pow] at hh
    push_cast at hh
    linarith
  have hupper := mul_le_mul hbase (sqrt_cubic_upper hw) h1.le (by norm_num)
  refine ⟨by rw [hwpoly]; exact hw,?_⟩
  have hsig : Explicit.sigma .high θ=
      R*(Real.sqrt (1+(293/1000:ℝ)^2)*Real.sqrt (1+w))-(1+e)/2 := by
    rw [← hroot,hedef]
    simp only [Explicit.sigma,fullSupport,one_pow]
  have hpoly : aeval (native θ) Certificate.sigmaUpper=
      ((1415477291/1000000000:ℝ)+(1+293/1000)/2)*(1+w/2-w^2/8+w^3/16)-(1+e)/2 := by
    simp only [Certificate.sigmaUpper,map_sub,map_mul,map_add,map_pow,map_one,aeval_C,
      r72_td_eta,hwpoly,eq_ratCast,← hedef]
    push_cast [Certificate.sigmabar,Certificate.eta0]
    ring
  rw [hsig,hpoly]
  simp only [cubic] at hupper
  linarith

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
    hc.1 hc.2 (r72_td_dom hθ)
  rw [map_neg,Rat.cast_zero] at hh
  linarith

theorem base_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval (native θ) Certificate.highBase≤base θ := by
  have ht := taylor_bounds (Explicit.frame_domain .high hθ)
  have hsig := (sigma_lower_data hθ).2
  have hs := (transport_trig (Explicit.frame_domain .high hθ)).2.2.1
  have hcoef : aeval (native θ) Certificate.highSineCoefficient≤
      1/2+(3/2)*eta θ-Explicit.sigma .high θ := by
    simp only [Certificate.highSineCoefficient,map_add,map_mul,map_sub,aeval_C,
      r72_td_eta,eq_ratCast]
    push_cast
    linarith
  have hsin := mul_le_mul_of_nonpos_left ht.2.2.1 (polynomial_sine_negative hθ)
  have hsin' := mul_le_mul_of_nonneg_right hcoef hs
  have hinner : 1+2*aeval θ C10+
      aeval (native θ) Certificate.highSineCoefficient*aeval θ S9≤
      1+2*Real.cos θ+(1/2+(3/2)*eta θ-Explicit.sigma .high θ)*Real.sin θ := by
    linarith [ht.2.2.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ m θ by linarith [(Explicit.high_bounds hθ).m_lower])
  simp only [Certificate.highBase,map_add,map_mul,map_one,aeval_C,r72_td_comp,
    r72_td_K,r72_td_L,r72_td_M,eq_ratCast,Rat.cast_ofNat]
  simp only [base]
  linarith

lemma base_polynomial_positive {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<aeval (native θ) (Certificate.highBase-1) := by
  have hc := Certificate.high_auxiliary_certificate.1
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by norm_num [Certificate.span,Certificate.h,Certificate.L] : (0:ℚ)<Certificate.span)
    hc.1 hc.2 (r72_td_dom hθ)
  have h0 : (0:ℝ)<((399/50:ℚ):ℝ) := by norm_num
  exact h0.trans hh

theorem baseline_identity {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.fullBaseline .high 0 θ 0=base θ-R*(norms θ 0+norms θ 1+norms θ 2+norms θ 3) := by
  rw [Explicit.fullBaseline]
  simp only [zero_add,Explicit.sec,NegativeELargeA.secant,Real.cos_zero,Real.tan_zero,
    div_one,sub_self,mul_zero,add_zero,TwoPositive.ASupport.charge_zero]
  rw [edgeWidth_positive_formula (Explicit.frame_domain .high hθ)]
  rw [fullSupport_pair (k θ) 1,fullSupport_pair (l θ) (k θ),
    fullSupport_pair (m θ) (l θ),fullSupport_pair (c θ) 1,pairNorm_symm (l θ) (k θ),
    pairNorm_symm (m θ) (l θ),pairNorm_symm (c θ) 1]
  simp only [base,norms,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Explicit.c]
  ring

theorem norm_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 4) :
    (norms θ i)^2≤aeval (native θ) (Certificate.highNormZero i) := by
  have hc := HighShape.coefficient_majorant hθ
  have hc0 : 0≤c θ := by
    linarith [(Explicit.high_c hθ ⟨by linarith [hθ.1],le_rfl⟩).1,
      (Explicit.high_bounds hθ).m_lower]
  have hc2 := pow_le_pow_left₀ hc0 hc 2
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  all_goals simp only [norms,Certificate.highNormZero,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    map_add,map_pow,map_one,r72_td_K,r72_td_L,r72_td_M,
    NonnegativeTotals.Analytic.norm_zero_square,one_pow]
  · linarith
  · exact le_rfl
  · exact le_rfl
  · linarith [hc2]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighTransfer
