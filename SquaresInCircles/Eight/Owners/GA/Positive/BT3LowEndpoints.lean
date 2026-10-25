module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowPolynomial
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3ScalarData
public import SquaresInCircles.Eight.Owners.GA.Positive.TDLowTransfer

/-!
# Eight squares: both actual small-total BT3 endpoints are positive

The exact diagonal support at D is
kept in the actual expression, then bounded by the stated rational
upper constant. The three squared norms are the original H/G/B norms.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.Analytic
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open NonnegativeTotals

theorem low_ranges {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    lowK t∈Icc (2933/5000:ℝ) K ∧ lowM t∈Icc (10163/10000:ℝ) Cmax := by
  dsimp [lowK,lowM,K,Cmax]
  constructor <;> constructor <;> linarith [ht.1,ht.2]

theorem low_tilted_ranges {t u : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) (hu : u∈Icc 0 t) :
    lowM t≤tilted (lowM t) u ∧ tilted (lowM t) u≤Cmax := by
  have huL : u∈Icc 0 (1/6:ℝ) := ⟨hu.1,hu.2.trans ht.2⟩
  have hm : 0<lowM t := by linarith [(low_ranges ht).2.1]
  have hlower := Explicit.tilt_small_monotone
    (show (0:ℝ)∈Icc 0 (1/6) by norm_num) huL hu.1
  have hflo : 1≤Explicit.tilt u := by simpa [Explicit.tilt] using hlower
  have hlo := mul_le_mul_of_nonneg_left hflo hm.le
  have hs := (Real.sin_le hu.1).trans hu.2
  have hupper : Explicit.tilt u≤1+PositiveTD.eta*t := by
    dsimp [Explicit.tilt,PositiveTD.eta]
    linarith [Real.cos_le_one u]
  have hhi := mul_le_mul_of_nonneg_left hupper hm.le
  have hprod : lowM t*(1+PositiveTD.eta*t)≤Cmax := by
    dsimp [lowM,Cmax,PositiveTD.eta]
    nlinarith [ht.1,sq_nonneg t]
  have he : tilted (lowM t) u=lowM t*Explicit.tilt u := rfl
  rw [he]
  exact ⟨by linarith,hhi.trans hprod⟩

def lowNonradical (ep : Endpoint) (t : ℝ) : ℝ :=
  (match ep with
  | .atA => 2*lowK t+11/2-GlobalGA.Secondary.diagonal+lowM t*(5/2-GlobalGA.Secondary.diagonal)+TwoPositive.ASupport.charge t
  | .atT => 2*lowK t+11/2-GlobalGA.Secondary.diagonal+lowM t*
      (1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos t+
        (1/2+PositiveTD.eta*(1-GlobalGA.Secondary.diagonal)-PositiveTD.sigma)*Real.sin t))+
    Real.cos t-1

def lowNorm (t : ℝ) : Fin 3 → ℝ :=
  ![pairNorm (lowK t) 1 (-t),pairNorm (lowK t) 1 0,pairNorm 1 (lowM t) 0]

theorem low_endpoint_identity (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    lowScalar t (NonnegativeTotals.Analytic.aAt ep t)=
      lowNonradical ep t-R*(lowNorm t 0+lowNorm t 1+lowNorm t 2) := by
  have ht' := PositiveTD.Certificate.low_frame_domain ht
  cases ep <;>
    simp only [lowScalar,lowBaseline,NonnegativeTotals.Analytic.aAt,sub_self,sub_zero,
      edgeWidth_zero,tilted,Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,
      TwoPositive.ASupport.charge_zero,lowNonradical,lowNorm,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
      Matrix.tail_cons,OrdinaryAngleConcavity.V]
  all_goals
    try rw [edgeWidth_positive_formula ht']
    rw [fullSupport_pair 1 (lowK t),fullSupport_pair (lowM t) 1]
    rw [pairNorm_symm 1 (lowK t),pairNorm_symm (lowM t) 1]
    ring

theorem low_J_lower {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    aeval t LowCertificate.J≤TwoPositive.ASupport.charge t := by
  rw [TwoPositive.ASupport.charge_low ht.2]
  have hh := Charges.J_lower_axial (PositiveTD.Certificate.low_frame_domain ht)
  have he : aeval t LowCertificate.J=Charges.polynomialJ t := by
    simp only [LowCertificate.J,Charges.polynomialJ,map_add,map_sub,map_mul,map_one,aeval_C,
      eq_ratCast]
    push_cast
    ring
  rw [he]
  exact hh

theorem low_nonradical_lower (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    aeval t (LowCertificate.A ep)≤lowNonradical ep t := by
  have htf := PositiveTD.Certificate.low_frame_domain ht
  have hm : 0≤lowM t := by linarith [(low_ranges ht).2.1]
  have hT := PositiveTD.Certificate.taylor_bounds htf
  have hs := (transport_trig htf).2.2.1
  have hD : GlobalGA.Secondary.diagonal≤(449607033/500000000:ℝ) := by
    have h := PositiveTD.Certificate.diagonal_le_cbar
    rwa [show (PositiveTD.Certificate.cbar:ℝ)=449607033/500000000 by
      norm_num [PositiveTD.Certificate.cbar]] at h
  have hS : PositiveTD.sigma≤(1415477291/1000000000:ℝ) := by
    have h := Charges.sigma_upper
    rwa [show (NonnegativeTotals.Certificate.sigmabar:ℝ)=1415477291/1000000000 by
      norm_num [NonnegativeTotals.Certificate.sigmabar]] at h
  cases ep
  · have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left hD (5/2)) hm
    have hJ := low_J_lower ht
    norm_num only [LowCertificate.A,LowCertificate.ABase,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,LowCertificate.k_eval,LowCertificate.m_eval,LowCertificate.cbar]
    dsimp [lowNonradical]
    linarith [hT.2.2.2.2.1]
  · have hcos := mul_le_mul_of_nonneg_left hT.2.2.2.2.1
      (show (0:ℝ)≤3/2-449607033/500000000 by norm_num)
    have hsin := mul_le_mul_of_nonpos_left hT.2.2.1
      (show (1/2:ℝ)+(293/1000)*(1-449607033/500000000)-1415477291/1000000000≤0 by
        norm_num)
    have hdc := mul_le_mul_of_nonneg_right hD
      (show 0≤Real.cos t by linarith [(transport_trig htf).1])
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner :
        1+(3/2-449607033/500000000)*aeval t PositiveTD.Certificate.C10+
          (1/2+(293/1000)*(1-449607033/500000000)-1415477291/1000000000)*
            aeval t PositiveTD.Certificate.S9≤
        1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos t+
          (1/2+PositiveTD.eta*(1-GlobalGA.Secondary.diagonal)-PositiveTD.sigma)*Real.sin t := by
      simp only [PositiveTD.eta]
      linarith only [hcos,hsin,hdc,hds,hss]
    have hmul := mul_le_mul_of_nonneg_left hinner hm
    norm_num only [LowCertificate.A,LowCertificate.ABase,map_add,map_sub,map_mul,
      map_one,aeval_C,eq_ratCast,LowCertificate.k_eval,LowCertificate.m_eval,LowCertificate.cbar,
      LowCertificate.sigmabar,NonnegativeTotals.Certificate.sigmabar]
    dsimp [lowNonradical]
    linarith [hT.2.2.2.2.1]

theorem low_norm_square_upper (i : Fin 3) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    (lowNorm t i)^2≤aeval t (LowCertificate.P i) := by
  have hk : 0<lowK t := by linarith [(low_ranges ht).1.1]
  fin_cases i
  · have hh := NonnegativeTotals.Analytic.norm_negative_polynomial hk
      (by norm_num : (0:ℝ)<1) (PositiveTD.Certificate.low_frame_domain ht)
    simpa [lowNorm,LowCertificate.P,LowCertificate.S11,add_comm] using hh
  · simp only [lowNorm,LowCertificate.P,pairNorm]
    simp [Real.sq_sqrt (by positivity : (0:ℝ)≤1+lowK t^2),add_comm]
  · simp only [lowNorm,LowCertificate.P,pairNorm]
    simp [Real.sq_sqrt (by positivity : (0:ℝ)≤1+lowM t^2)]

theorem low_endpoint_positive (ep : Endpoint) {t : ℝ} (ht : t∈Icc 0 (1/6:ℝ)) :
    0<lowScalar t (NonnegativeTotals.Analytic.aAt ep t) := by
  have hm (i : Fin 3) := LowCertificate.mass_positive i ht
  have hn (i : Fin 3) : 0≤lowNorm t i := by fin_cases i <;> exact Real.sqrt_nonneg _
  have hp : 0<aeval t (LowCertificate.numerator ep) := by
    linarith [LowCertificate.numerator_positive ep ht]
  have hh := PositiveTD.Certificate.num3_transfer
    (hm 0) (hm 1) (hm 2) (hn 0) (hn 1) (hn 2)
    (low_norm_square_upper 0 ht) (low_norm_square_upper 1 ht) (low_norm_square_upper 2 ht)
    (low_nonradical_lower ep ht) hp
  rwa [low_endpoint_identity ep ht]

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.Analytic
