module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowNegative

/-!
# The two actual low-total equal-angle endpoints

Uncompiled Section 8.1. The sorted D support is retained: sec(theta)
is below the original D coefficient on the whole low interval. Its
exact diagonal correction is multiplied by the positive original cosine
before the three circle norms are bounded. The polynomial masses are
used only after their whole-interval positivity has been supplied.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowEndpoints
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds num3_transfer)

abbrev k (θ : ℝ) := Explicit.k .low θ
abbrev m (θ : ℝ) := Explicit.m .low θ

def base (ep : Split) (θ : ℝ) : ℝ := match ep with
  | .atA => 2*k θ+11/2-diagonal+m θ*(5/2-diagonal)+TwoPositive.ASupport.charge θ
  | .atT => 2*k θ+11/2-diagonal+m θ*
      (1+(3/2-diagonal)*Real.cos θ+
        (1/2+Explicit.eta .low θ*(1-diagonal)-Explicit.sigma .low θ)*Real.sin θ)

def norms (θ : ℝ) : Fin 3→ℝ := ![pairNorm (k θ) 1 0,pairNorm (k θ) 1 0,pairNorm 1 (m θ) 0]
def nonradical (ep : Split) (θ : ℝ) : ℝ :=
  Real.cos θ*base ep θ+Explicit.K*Real.sin θ+(diagonal-1/2)*(Real.cos θ-1)

theorem base_lower (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (Certificate.lowBase ep)≤base ep θ := by
  have ht := taylor_bounds (Explicit.frame_domain .low hθ)
  have hm : 0≤m θ := by linarith [(Explicit.low_bounds hθ).2.1]
  have hs := (transport_trig (Explicit.frame_domain .low hθ)).2.2.1
  have hD : diagonal≤(Certificate.cbar:ℝ) := by
    simpa [Certificate.cbar,PositiveTD.Certificate.cbar] using PositiveTD.Certificate.diagonal_le_cbar
  have hS : Explicit.sigma .low θ≤(Certificate.sigmabar:ℝ) := by
    simpa [Explicit.sigma,Explicit.eta,Certificate.sigmabar,PositiveBT3.LowCertificate.sigmabar]
      using NonnegativeTotals.Charges.sigma_upper
  cases ep
  · have hj := PositiveBT3.Analytic.low_J_lower hθ
    have hj' : aeval θ Certificate.J≤TwoPositive.ASupport.charge θ := by
      simpa [Certificate.J,Certificate.abar,PositiveBT3.LowCertificate.J,
        PositiveBT3.LowCertificate.C10,PositiveBT3.LowCertificate.S9,PositiveBT3.LowCertificate.abar] using hj
    have hprod := mul_le_mul_of_nonneg_left (sub_le_sub_left hD (5/2)) hm
    simp only [Certificate.lowBase,map_add,map_mul,aeval_C,Certificate.lowK_eval,Certificate.lowM_eval]
    push_cast
    dsimp [base,k,m]
    linarith
  · have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
      (show (0:ℝ)≤3/2-(Certificate.cbar:ℝ) by norm_num [Certificate.cbar])
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+(Certificate.eta0:ℝ)*(1-(Certificate.cbar:ℝ))-
        (Certificate.sigmabar:ℝ)≤0 by norm_num [Certificate.eta0,Certificate.cbar,Certificate.sigmabar])
    have hdc := mul_le_mul_of_nonneg_right hD
      (show 0≤Real.cos θ by linarith [(transport_trig (Explicit.frame_domain .low hθ)).1])
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have hinner : 1+(3/2-(Certificate.cbar:ℝ))*aeval θ C10+
        (1/2+(Certificate.eta0:ℝ)*(1-(Certificate.cbar:ℝ))-(Certificate.sigmabar:ℝ))*aeval θ S9≤
      1+(3/2-diagonal)*Real.cos θ+
        (1/2+Explicit.eta .low θ*(1-diagonal)-Explicit.sigma .low θ)*Real.sin θ := by
      dsimp [Certificate.eta0,Explicit.eta] at *
      nlinarith only [hcos,hsin,hdc,hds,hss]
    have hprod := mul_le_mul_of_nonneg_left hinner hm
    simp only [Certificate.lowBase,map_add,map_mul,aeval_C,Certificate.lowK_eval,Certificate.lowM_eval]
    push_cast
    dsimp [base,k,m]
    linarith

theorem zero_identity (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) 0=
      base ep θ-R*(norms θ 0+norms θ 1+norms θ 2) := by
  have hz := (NegativeDEPositiveTD.Certificate.split_angles ep (Explicit.frame_domain .low hθ)).2.1
  have hc : 1≤Explicit.c .low θ (Explicit.splitT ep θ) := by
    linarith [(Explicit.low_c hθ hz).1,(Explicit.low_bounds hθ).2.1]
  simp only [Explicit.baseline,NegativeDEPositiveTD.Certificate.split_sum,
    Explicit.sec,NegativeELargeA.secant,Real.cos_zero,Real.tan_zero,div_one,
    sub_self,mul_zero,sub_zero,add_zero]
  rw [PositiveBT3.sortedSupport_diagonal hc]
  rw [fullSupport_pair 1 (k θ),fullSupport_pair (k θ) 1,fullSupport_pair 1 (m θ)]
  rw [pairNorm_symm 1 (k θ) 0]
  cases ep <;>
    simp only [base,norms,Explicit.splitA,Explicit.splitT,Explicit.c,Explicit.l,
      Matrix.cons_val_zero,Matrix.cons_val_succ,edgeWidth_zero,Real.cos_zero,
      Real.sin_zero,mul_zero,mul_one,add_zero,TwoPositive.ASupport.charge_zero,
      diagonalSupport]
  all_goals
    try rw [edgeWidth_positive_formula (Explicit.frame_domain .low hθ)]
    dsimp [k,m]
    ring

theorem equal_identity (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Real.cos θ*Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) θ=
      nonradical ep θ-R*(Real.cos θ*norms θ 0+Real.cos θ*norms θ 1+Real.cos θ*norms θ 2) := by
  have hf := Explicit.frame_domain .low hθ
  have hz := (NegativeDEPositiveTD.Certificate.split_angles ep hf).2.1
  have hc := (Explicit.source_coefficients .low hθ hz).2.2.2.2.1
  have hsc := LowNegative.secant_le_c hθ hz ⟨hθ.1,le_rfl⟩
  have hcos := NegativeESecant.cos_pos hf
  rw [Explicit.baseline_correction,NegativeDEPositiveTD.Certificate.split_sum,
    SecantD.PositiveEndpoint.correction_diagonal hc hf hsc,
    zero_identity ep hθ,NegativeESecant.gain_secant _ hf]
  dsimp [nonradical,NegativeESecant.K,Explicit.K,NegativeELargeA.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos.ne']
  ring

theorem nonradical_lower (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (Certificate.lowA ep)≤nonradical ep θ := by
  have ht := taylor_bounds (Explicit.frame_domain .low hθ)
  have hcos : 0≤Real.cos θ := (NegativeESecant.cos_pos (Explicit.frame_domain .low hθ)).le
  have hbase := mul_le_mul ht.2.2.2.2.1 (base_lower ep hθ)
    (Certificate.low_base_positive ep hθ).le hcos
  have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hD : diagonal≤(Certificate.cbar:ℝ) := by
    simpa [Certificate.cbar,PositiveTD.Certificate.cbar] using PositiveTD.Certificate.diagonal_le_cbar
  have hcoef := mul_le_mul_of_nonpos_right (sub_le_sub_right hD (1/2))
    (sub_nonpos.mpr (Real.cos_le_one θ))
  have hlower := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (show 0≤(Certificate.cbar:ℝ)-1/2 by norm_num [Certificate.cbar])
  simp only [Certificate.lowA,map_add,map_mul,map_sub,map_one,aeval_C]
  push_cast
  dsimp [nonradical,Explicit.K,Certificate.K]
  linarith

theorem norm_bound {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 3) :
    (Real.cos θ*norms θ i)^2≤aeval θ (Certificate.lowP i) := by
  have hf := Explicit.frame_domain .low hθ
  have hn : (norms θ i)^2≤aeval θ
      ((![(1+Certificate.lowK^2),(1+Certificate.lowK^2),(1+Certificate.lowM^2)] : Fin 3→ℚ[X]) i) := by
    fin_cases i <;>
      simp [norms,NonnegativeTotals.Analytic.norm_zero_square,add_comm,k,m]
  have hh := NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hn
  fin_cases i <;> simpa [Certificate.lowP] using hh

/-- Both split endpoints are positive for the literal sorted-D stress. -/
theorem equal_positive (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) θ := by
  have hcos := NegativeESecant.cos_pos (Explicit.frame_domain .low hθ)
  have hn (i : Fin 3) : 0≤Real.cos θ*norms θ i :=
    mul_nonneg hcos.le (by fin_cases i <;> exact Real.sqrt_nonneg _)
  have hp := num3_transfer
    (Certificate.low_mass_positive 0 hθ) (Certificate.low_mass_positive 1 hθ)
    (Certificate.low_mass_positive 2 hθ) (hn 0) (hn 1) (hn 2)
    (norm_bound hθ 0) (norm_bound hθ 1) (norm_bound hθ 2)
    (nonradical_lower ep hθ) (Certificate.low_numerator_positive ep hθ)
  rw [←equal_identity ep hθ] at hp
  exact (mul_pos_iff_of_pos_left hcos).mp hp

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowEndpoints
