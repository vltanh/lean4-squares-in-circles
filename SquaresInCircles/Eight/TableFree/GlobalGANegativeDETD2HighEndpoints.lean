module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowEndpoints

/-!
# The four actual high negative-DE scalar endpoints

Uncompiled transfer of equations (64)--(67).  The high family uses the
full D-circle lower baseline.  The B cosine coefficient is enlarged to
the proved q-star bound, and the equal-angle D norm keeps the secant
until the actual cosine multiplication.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S11 C4 taylor_bounds pairNorm_nonneg num4_transfer)

private theorem r74_high {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ∈Icc ((left .high:ℚ):ℝ) ((right .high:ℚ):ℝ) := by
  simpa [left,right,PositiveTD.Certificate.L,PositiveTD.Certificate.h] using hθ

theorem high_H_scalar_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<highBase e θ 0+V R (Explicit.k .high θ) 1 θ := by
  have hn := ordinary_norm_bounds .high e (r74_high hθ)
  have ht := taylor_bounds (family_frame_domain .high (r74_high hθ))
  have hA : aeval θ (highB e+C10-1)≤highNonradical e θ+Real.cos θ-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [high_nonradical_lower e hθ,ht.2.2.2.2.1]
  have hp := num4_transfer
    (show 0<aeval θ (RG .high) from high_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RB .high e) from high_auxiliary_positive e 2 hθ)
    (show 0<aeval θ (RHminus .high) from high_auxiliary_positive e 4 hθ)
    (show 0<aeval θ (RD) from high_auxiliary_positive e 3 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hn.2.2.2.1 hA
    (by simpa only [NH,reduceCtorEq,↓reduceIte] using (high_numerators_positive e hθ).1)
  rw [high_H_identity]
  exact hp

theorem high_G_scalar_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<highBase e θ 0+V R (Explicit.k .high θ) (Explicit.l .high θ) θ := by
  have hn := ordinary_norm_bounds .high e (r74_high hθ)
  have ht := taylor_bounds (family_frame_domain .high (r74_high hθ))
  have hl := (split_positive .high e (r74_high hθ)).2.1
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 hl.le
  have hA : aeval θ (highB e+l .high*(C10-1))≤
      highNonradical e θ+Explicit.l .high θ*(Real.cos θ-1) := by
    simp only [map_add,map_mul,map_sub,map_one,l_eval]
    nlinarith only [high_nonradical_lower e hθ,hcos]
  have hp := num4_transfer
    (show 0<aeval θ (RH .high) from high_auxiliary_positive e 0 hθ)
    (show 0<aeval θ (RB .high e) from high_auxiliary_positive e 2 hθ)
    (show 0<aeval θ (RGminus) from high_auxiliary_positive e 5 hθ)
    (show 0<aeval θ (RD) from high_auxiliary_positive e 3 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.1 hA
    (high_numerators_positive e hθ).2.1
  rw [high_G_identity]
  exact hp

theorem high_B_scalar_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<highBase e θ 0+V R (min (Explicit.l .high θ) (Explicit.splitM .high e θ))
      (max (Explicit.l .high θ) (Explicit.splitM .high e θ)) θ := by
  have hn := ordinary_norm_bounds .high e (r74_high hθ)
  have ht := taylor_bounds (family_frame_domain .high (r74_high hθ))
  have hq := qStar_lower e hθ
  have hl := (split_positive .high e (r74_high hθ)).2.1
  have hqpos : 0≤aeval θ qStar :=
    (hl.le.trans (le_max_left _ _)).trans hq
  have h₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hqpos
  have h₂ := mul_le_mul_of_nonpos_right hq
    (sub_nonpos.mpr (Real.cos_le_one θ))
  have hA : aeval θ (highB e+qStar*(C10-1))≤highNonradical e θ+
      max (Explicit.l .high θ) (Explicit.splitM .high e θ)*(Real.cos θ-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [high_nonradical_lower e hθ]
  have hp := num4_transfer
    (show 0<aeval θ (RH .high) from high_auxiliary_positive e 0 hθ)
    (show 0<aeval θ (RG .high) from high_auxiliary_positive e 1 hθ)
    (show 0<aeval θ (RBminus e) from high_auxiliary_positive e 6 hθ)
    (show 0<aeval θ (RD) from high_auxiliary_positive e 3 hθ)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.2.1 hA
    (high_numerators_positive e hθ).2.2.1
  rw [high_B_identity]
  exact hp

theorem high_equal_nonradical (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    aeval θ (C10*(highB e-1)+1+C K*S11)≤
      Real.cos θ*(highNonradical e θ-1)+1+Explicit.K*Real.sin θ := by
  have ht := taylor_bounds (family_frame_domain .high (r74_high hθ))
  have hB : 0<aeval θ (highB e-1) := by
    simpa only [reduceCtorEq,↓reduceIte] using multiplied_baseline_positive .high e (r74_high hθ)
  have h₁ := mul_le_mul_of_nonneg_right ht.2.2.2.2.1 hB.le
  have hc : 0≤Real.cos θ := by linarith [(transport_trig (family_frame_domain .high (r74_high hθ))).1]
  have h₂ := mul_le_mul_of_nonneg_left (high_nonradical_lower e hθ) hc
  have hK : ((K:ℚ):ℝ)=Explicit.K := by norm_num [K,Explicit.K]
  simp only [map_sub,map_add,map_mul,map_one,aeval_C,eq_ratCast,hK] at h₁ ⊢
  have hK0 : 0≤Explicit.K := by norm_num [Explicit.K]
  have h₄ := mul_le_mul_of_nonneg_left ht.2.1 hK0
  linarith only [h₁,h₂,h₄]

theorem high_Z_scalar_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    0<highBase e θ θ := by
  have hn := ordinary_norm_bounds .high e (r74_high hθ)
  have hθ' := family_frame_domain .high (r74_high hθ)
  have hc : 0<Real.cos θ := by linarith [(transport_trig hθ').1]
  have hp := num4_transfer
    (show 0<aeval θ (C4*RH .high) from high_auxiliary_positive e 7 hθ)
    (show 0<aeval θ (C4*RG .high) from high_auxiliary_positive e 8 hθ)
    (show 0<aeval θ (C4*RB .high e) from high_auxiliary_positive e 9 hθ)
    (show 0<aeval θ (secantR) from high_auxiliary_positive e 10 hθ)
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (mul_nonneg hc.le (pairNorm_nonneg _ _ _))
    (scaled_norm_bound hθ' hn.1) (scaled_norm_bound hθ' hn.2.1)
    (scaled_norm_bound hθ' hn.2.2.1) (scaled_secant_norm_bound hθ)
    (high_equal_nonradical e hθ)
    (by simpa only [NZ,reduceCtorEq,↓reduceIte] using (high_numerators_positive e hθ).2.2.2)
  rw [←high_equal_identity e hθ] at hp
  exact (mul_pos_iff_of_pos_left hc).mp hp

theorem high_endpoints_positive (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (i : Fin 3) :
    0<highBase e θ 0+Explicit.V .high θ (Explicit.splitT e θ) i θ ∧
      0<highBase e θ θ := by
  refine ⟨?_,high_Z_scalar_positive e hθ⟩
  fin_cases i
  · simpa [Explicit.V,Explicit.p,Explicit.q] using high_H_scalar_positive e hθ
  · simpa [Explicit.V,Explicit.p,Explicit.q] using high_G_scalar_positive e hθ
  · simpa [Explicit.V,Explicit.p,Explicit.q,Explicit.splitM] using high_B_scalar_positive e hθ

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Certificate
