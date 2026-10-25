module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3LowNegative
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2ScalarIdentities

/-!
# Eight squares: the two low-total equal-angle endpoints

The sorted D support is kept: `sec θ` is below the D coefficient on the whole low interval. Its
diagonal correction is multiplied by the positive cosine before the three circle norms are bounded.
The polynomial masses are used only once they are known to be positive on the whole interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowEndpoints
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds num3_transfer)

abbrev k (θ : ℝ) := Explicit.k .low θ
abbrev m (θ : ℝ) := Explicit.m .low θ

def base (ep : Split) (θ : ℝ) : ℝ := match ep with
  | .atA => 2*k θ+11/2-GlobalGA.Secondary.diagonal+m θ*(5/2-GlobalGA.Secondary.diagonal)+TwoPositive.ASupport.charge θ
  | .atT => 2*k θ+11/2-GlobalGA.Secondary.diagonal+m θ*
      (1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos θ+
        (1/2+Explicit.eta .low θ*(1-GlobalGA.Secondary.diagonal)-Explicit.sigma .low θ)*Real.sin θ)

def norms (θ : ℝ) : Fin 3→ℝ := ![pairNorm (k θ) 1 0,pairNorm (k θ) 1 0,pairNorm 1 (m θ) 0]
def nonradical (ep : Split) (θ : ℝ) : ℝ :=
  Real.cos θ*base ep θ+Explicit.K*Real.sin θ+(GlobalGA.Secondary.diagonal-1/2)*(Real.cos θ-1)

private lemma r72_diag : GlobalGA.Secondary.diagonal≤(449607033/500000000:ℝ) := by
  have h := PositiveTD.Certificate.diagonal_le_cbar
  simp only [PositiveTD.Certificate.cbar] at h
  push_cast at h
  linarith

private lemma r72_sigma (θ : ℝ) : Explicit.sigma .low θ≤(1415477291/1000000000:ℝ) := by
  have h := NonnegativeTotals.Charges.sigma_upper
  simp only [PositiveTD.sigma,PositiveTD.eta,NonnegativeTotals.Certificate.sigmabar] at h
  push_cast at h
  simp only [Explicit.sigma,Explicit.eta]
  linarith

theorem base_lower (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (Certificate.lowBase ep)≤base ep θ := by
  have ht := taylor_bounds (Explicit.frame_domain .low hθ)
  have hm : 0 ≤ m θ := by linarith [(Explicit.low_bounds hθ).2.1]
  have hs := (transport_trig (Explicit.frame_domain .low hθ)).2.2.1
  have hc0 : 0≤Real.cos θ := by linarith [(transport_trig (Explicit.frame_domain .low hθ)).1]
  have hD := r72_diag
  have hS := r72_sigma θ
  cases ep with
  | atA =>
    have hj := PositiveBT3.Analytic.low_J_lower hθ
    have hab : Certificate.abar=NonnegativeTotals.Certificate.abar := by
      norm_num [Certificate.abar,NonnegativeTotals.Certificate.abar]
    have hJ : Certificate.J=PositiveBT3.LowCertificate.J := by
      simp only [Certificate.J,PositiveBT3.LowCertificate.J,PositiveBT3.LowCertificate.C10,
        PositiveBT3.LowCertificate.S9,PositiveBT3.LowCertificate.abar,hab]
    have hprod := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hD (5/2:ℝ)) hm
    simp only [Certificate.lowBase,map_add,map_mul,aeval_C,Certificate.lowK_eval,
      Certificate.lowM_eval,hJ,eq_ratCast,Certificate.cbar]
    push_cast
    simp only [base]
    linarith
  | atT =>
    have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
      (show (0:ℝ)≤3/2-449607033/500000000 by norm_num)
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+(293/1000)*(1-449607033/500000000)-1415477291/1000000000≤0 by norm_num)
    have hdc := mul_le_mul_of_nonneg_right hD hc0
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have he : Explicit.eta .low θ=293/1000 := rfl
    have hinner : 1+(3/2-449607033/500000000)*aeval θ C10+
        ((1/2:ℝ)+(293/1000)*(1-449607033/500000000)-1415477291/1000000000)*aeval θ S9≤
      1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos θ+
        (1/2+Explicit.eta .low θ*(1-GlobalGA.Secondary.diagonal)-Explicit.sigma .low θ)*
          Real.sin θ := by
      rw [he]
      linarith
    have hprod := mul_le_mul_of_nonneg_left hinner hm
    simp only [Certificate.lowBase,map_add,map_mul,map_sub,map_one,aeval_C,Certificate.lowK_eval,
      Certificate.lowM_eval,eq_ratCast,Certificate.cbar,Certificate.eta0,Certificate.sigmabar]
    push_cast
    simp only [base]
    linarith

theorem zero_identity (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) 0=
      base ep θ-R*(norms θ 0+norms θ 1+norms θ 2) := by
  have hz := (NegativeDEPositiveTD.Certificate.split_angles ep (Explicit.frame_domain .low hθ)).2.1
  have hc : 1≤Explicit.c .low θ (Explicit.splitT ep θ) := by
    linarith [(Explicit.low_c hθ hz).1,(Explicit.low_bounds hθ).2.1]
  simp only [Explicit.baseline,NegativeDEPositiveTD.Certificate.split_sum,
    Explicit.sec,NegativeELargeA.secant,Real.cos_zero,Real.tan_zero,div_one,
    sub_self,mul_zero,sub_zero,add_zero,zero_div,Explicit.l]
  rw [PositiveBT3.sortedSupport_diagonal hc]
  rw [fullSupport_pair (k θ) 1,fullSupport_pair 1 (k θ),fullSupport_pair (m θ) 1,
    pairNorm_symm 1 (k θ) 0,pairNorm_symm (m θ) 1 0]
  cases ep with
  | atA =>
    simp only [base,norms,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,Explicit.c,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,edgeWidth_zero,Real.cos_zero,
      Real.sin_zero,mul_zero,mul_one,add_zero,diagonalSupport]
    ring
  | atT =>
    simp only [base,norms,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,Explicit.c,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,TwoPositive.ASupport.charge_zero,
      mul_zero,add_zero,diagonalSupport]
    rw [edgeWidth_positive_formula (Explicit.frame_domain .low hθ)]
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
  have hD := r72_diag
  have hcoef := mul_le_mul_of_nonpos_right (sub_le_sub_right hD (1/2))
    (sub_nonpos.mpr (Real.cos_le_one θ))
  have hlower := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (show (0:ℝ)≤449607033/500000000-1/2 by norm_num)
  simp only [Certificate.lowA,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast,
    Certificate.K,Certificate.cbar]
  push_cast
  simp only [nonradical,Explicit.K]
  linarith

theorem norm_bound {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 3) :
    (Real.cos θ*norms θ i)^2≤aeval θ (Certificate.lowP i) := by
  have hf := Explicit.frame_domain .low hθ
  have hK : (pairNorm (k θ) 1 0)^2≤aeval θ (1+Certificate.lowK^2) := by
    rw [NonnegativeTotals.Analytic.norm_zero_square]
    simp only [map_add,map_one,map_pow,Certificate.lowK_eval]
    linarith
  have hM : (pairNorm 1 (m θ) 0)^2≤aeval θ (1+Certificate.lowM^2) := by
    rw [NonnegativeTotals.Analytic.norm_zero_square]
    simp only [map_add,map_one,map_pow,Certificate.lowM_eval]
    linarith
  obtain rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 := by revert i; decide
  · exact NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hK
  · exact NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hK
  · exact NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hM

/-- Both split endpoints are positive for the sorted-D stress. -/
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

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowEndpoints
