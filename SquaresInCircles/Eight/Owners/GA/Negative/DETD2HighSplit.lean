module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveScalar

/-!
# Eight squares: rejoining the original nonnegative A and positive-TD split

The coefficient family is fixed
at the original total angle.  Concavity in the actual A/TD split reduces
the pure and equal-angle expressions to the already proved endpoint
norm inequalities; the secant-D correction is independent of this split.
-/

section
/-!
## The four actual high negative-DE scalar endpoints

The high family uses the
full D-circle lower baseline.  The B cosine coefficient is enlarged to
the proved q-star bound, and the equal-angle D norm keeps the secant
until the actual cosine multiplication.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
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

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.HighSplit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SplitConcavityTools

private theorem r74_high {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ∈Icc ((Certificate.left .high:ℚ):ℝ) ((Certificate.right .high:ℚ):ℝ) := by
  simpa [Certificate.left,Certificate.right,PositiveTD.Certificate.L,
    PositiveTD.Certificate.h] using hθ

def zeroScalar (θ a : ℝ) : ℝ := Explicit.fullBaseline .high a (θ-a) 0
def pureScalar (θ : ℝ) (i : Fin 3) (a : ℝ) : ℝ :=
  zeroScalar θ a+Explicit.V .high θ (θ-a) i θ
def equalScalar (θ a : ℝ) : ℝ := Explicit.fullBaseline .high a (θ-a) θ
def correction (θ : ℝ) : ℝ :=
  clippedSupport 1 (Explicit.c .high θ)-fullSupport 1 (Explicit.c .high θ)

theorem zero_identity (θ a : ℝ) :
    zeroScalar θ a=TwoPositive.splitBase (Explicit.k .high θ) (Explicit.l .high θ)
      (Explicit.c .high θ) θ a+correction θ := by
  simp only [zeroScalar,Explicit.fullBaseline,Explicit.baseline,
    show a+(θ-a)=θ by ring,Explicit.secant,Real.cos_zero,Real.tan_zero,
    div_one,sub_self,mul_zero,add_zero,
    TwoPositive.splitBase,PositiveTD.baseline,correction]
  dsimp [Explicit.m,PositiveTD.tilted,Explicit.eta,PositiveTD.eta,
    Explicit.sigma,PositiveTD.sigma]
  ring

theorem equal_identity {θ a : ℝ} (hθ : θ∈Icc 0 frameCap) :
    equalScalar θ a=zeroScalar θ a+secantGain qCap (Explicit.c .high θ) θ := by
  rw [equalScalar,HighSecant.full_gain_identity .high a (θ-a) hθ]
  simp only [zeroScalar,show a+(θ-a)=θ by ring]

theorem coefficient_range {θ a : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (ha : a∈Icc 0 θ) :
    PositiveTD.tilted (Explicit.c .high θ) (θ-a)∈
      Icc (Explicit.c .high θ/2) ((23/20)*Explicit.l .high θ) := by
  have hz : θ-a∈Icc 0 θ := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hr := Explicit.high_ranges hθ
  have hm := Explicit.high_tilted hθ hz
  change Explicit.m .high θ (θ-a)∈Icc _ _
  exact ⟨by linarith [hm.1,hr.1,hr.2.2.2.2.2.1],by nlinarith [hm.2.1,hr.2.2.1]⟩

theorem base_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ)
      (TwoPositive.splitBase (Explicit.k .high θ) (Explicit.l .high θ) (Explicit.c .high θ) θ) := by
  have hp := Explicit.high_ranges hθ
  have hl : 0<Explicit.l .high θ := by linarith [hp.2.2.1]
  have hc : 0<Explicit.c .high θ := by linarith [hp.2.2.2.2.1]
  have hr := Explicit.high_ratios hθ
  have hh := TwoPositive.Split.high_increment_concave
    (k:=Explicit.k .high θ) (s:=0) (g:=0) (e:=0)
    hl hr.1.le (show Explicit.c .high θ≤(11/10)*Explicit.l .high θ by nlinarith [hr.2])
    (Certificate.family_frame_domain .high (r74_high hθ)) (by norm_num [frameCap])
    (show 0<Explicit.c .high θ/2 by positivity) le_rfl le_rfl (by simp)
    (fun a ha => coefficient_range hθ ha)
  simpa only [neg_zero,TwoPositive.Split.increment_zero,add_zero] using hh

theorem zero_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (zeroScalar θ) := by
  apply TwoPositive.Split.congr_on
    (TwoPositive.Split.add_constant (base_concave hθ) (correction θ))
  intro a _
  exact (zero_identity θ a).symm

theorem pure_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 θ) (pureScalar θ i) := by
  have hp := Explicit.high_ranges hθ
  have hl : 0<Explicit.l .high θ := by linarith [hp.2.2.1]
  have hc : 0<Explicit.c .high θ := by linarith [hp.2.2.2.2.1]
  have hr := Explicit.high_ratios hθ
  fin_cases i
  · exact TwoPositive.Split.add_constant (zero_concave hθ) (V R (Explicit.k .high θ) 1 θ)
  · exact TwoPositive.Split.add_constant (zero_concave hθ)
      (V R (Explicit.k .high θ) (Explicit.l .high θ) θ)
  · have hh := TwoPositive.Split.high_increment_concave
      (k:=Explicit.k .high θ) (s:=θ) (g:=0) (e:=Real.cos θ-1)
      hl hr.1.le (show Explicit.c .high θ≤(11/10)*Explicit.l .high θ by nlinarith [hr.2])
      (Certificate.family_frame_domain .high (r74_high hθ)) (Certificate.family_frame_domain .high (r74_high hθ))
      (show 0<Explicit.c .high θ/2 by positivity) le_rfl
      (sub_nonpos.mpr (Real.cos_le_one θ)) le_rfl (fun a ha => coefficient_range hθ ha)
    apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant hh (correction θ))
    intro a _
    rw [pureScalar,zero_identity,TwoPositive.Split.increment_V]
    dsimp [Explicit.V,Explicit.p,Explicit.q,Explicit.m,Explicit.eta,
      PositiveTD.tilted,PositiveTD.eta]
    ring

theorem equal_concave {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    ConcaveOn ℝ (Icc 0 θ) (equalScalar θ) := by
  apply TwoPositive.Split.congr_on (TwoPositive.Split.add_constant (zero_concave hθ)
    (secantGain qCap (Explicit.c .high θ) θ))
  intro a _
  exact (equal_identity (Certificate.family_frame_domain .high (r74_high hθ))).symm

theorem pure_positive {θ a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (ha : a∈Icc 0 θ) (i : Fin 3) : 0<pureScalar θ i a := by
  have hzero : 0<pureScalar θ i 0 := by
    have hh := (Certificate.high_endpoints_positive .atT hθ i).1
    simpa only [pureScalar,zeroScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,
      sub_zero] using hh
  have htotal : 0<pureScalar θ i θ := by
    have hh := (Certificate.high_endpoints_positive .atA hθ i).1
    simpa only [pureScalar,zeroScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,
      sub_self] using hh
  exact concave_gt_of_endpoints (pure_concave hθ i) ha hzero htotal

theorem equal_positive {θ a : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (ha : a∈Icc 0 θ) : 0<equalScalar θ a := by
  have hzero : 0<equalScalar θ 0 := by
    simpa only [equalScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,sub_zero]
      using Certificate.high_Z_scalar_positive .atT hθ
  have htotal : 0<equalScalar θ θ := by
    simpa only [equalScalar,Certificate.highBase,Explicit.splitA,Explicit.splitT,sub_self]
      using Certificate.high_Z_scalar_positive .atA hθ
  exact concave_gt_of_endpoints (equal_concave hθ) ha hzero htotal

theorem original_pure_at_zero_positive {a z : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z) (i : Fin 3) :
    0<Explicit.fullBaseline .high a z 0+Explicit.V .high (a+z) z i (a+z) := by
  have hh := pure_positive hθ (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩) i
  simpa only [pureScalar,zeroScalar,show a+z-a=z by ring] using hh

theorem original_equal_positive {a z : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z) :
    0<Explicit.fullBaseline .high a z (a+z) := by
  have hh := equal_positive hθ (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
  simpa only [equalScalar,show a+z-a=z by ring] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.HighSplit
end
end
end
