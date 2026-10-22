module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2NormBounds

/-!
# Positive actual H/G/B and equal-angle negative-A endpoints

Uncompiled transcription of the radical transfer in Sections 5, 6,
and 8 of the scalar companion. Every numerator and positive tangent
denominator has already been proved from its explicit polynomial.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
open Candidate Secondary Polynomial PositiveAngularEnvelope OrdinaryAngleConcavity Explicit
open PositiveTD.Certificate (C10 C12 S9 S11 C4 S5 Rbar cbar sigmabar etaQ h)

theorem zero_reduced_identity (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    reducedBaseline f true 0 z=nonradical f z-R*normSum f
      ![pairNorm (Explicit.k f z) 1 0,pairNorm (Explicit.k f z) (Explicit.l f z) 0,
        pairNorm (Explicit.l f z) (Explicit.m f z) 0,pairNorm (Explicit.c f z) 1 0] := by
  have hh := reduced_identity f true hz (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  simpa [secant,norms,lambdaG,lambdaB,Explicit.m] using hh

theorem reduced_zero_le (f : Family) {z : ℝ} :
    reducedBaseline f true 0 z≤PositiveTD.baseline (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z := by
  simpa only [baseline_zero] using reduced_le_baseline f true 0 z

theorem low_H_endpoint {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z+
      V R (Explicit.k .low z) 1 z := by
  have hn := ordinary_norm_bounds .low hz
  obtain ⟨_,hrG,hrB,_,hrH,_,_⟩ := ordinary_masses_positive .low hz
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .low hz)
  have hA : aeval z (elementary .low+C10-1)≤nonradical .low z+Real.cos z-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [elementary_lower .low hz,ht.2.2.2.2.1]
  have hN : 0<aeval z (PositiveTD.Certificate.num3 (elementary .low+C10-1)
      (PG .low) (PB .low) (PHminus .low) (RG .low) (RB .low) (RHminus .low)) := by
    simpa [NH] using (low_numerators_positive hz).1
  have hp := PositiveTD.Certificate.num3_transfer hrG hrB hrH
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hA hN
  have he := zero_reduced_identity .low hz
  have hl := reduced_zero_le (f:=Family.low) (z:=z)
  dsimp [normSum] at he
  dsimp [V]
  nlinarith only [hp,he,hl]

theorem high_H_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) 1 z := by
  have hn := ordinary_norm_bounds .high hz
  obtain ⟨_,hrG,hrB,hrD,hrH,_,_⟩ := ordinary_masses_positive .high hz
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .high hz)
  have hA : aeval z (elementary .high+C10-1)≤nonradical .high z+Real.cos z-1 := by
    simp only [map_add,map_sub,map_one]
    linarith [elementary_lower .high hz,ht.2.2.2.2.1]
  have hN : 0<aeval z (PositiveTD.Certificate.num4 (elementary .high+C10-1)
      (PG .high) (PB .high) (PHminus .high) (PD .high)
      (RG .high) (RB .high) (RHminus .high) (RD .high)) := by
    simpa [NH] using (high_numerators_positive hz).1
  have hp := PositiveTD.Certificate.num4_transfer hrG hrB hrH hrD
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hn.2.1 hn.2.2.1 hn.2.2.2.2.1 hn.2.2.2.1 hA hN
  have he := zero_reduced_identity .high hz
  have hl := reduced_zero_le (f:=Family.high) (z:=z)
  dsimp [normSum] at he
  dsimp [V]
  nlinarith only [hp,he,hl]

theorem high_G_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (Explicit.k .high z) (Explicit.l .high z) z := by
  have hn := ordinary_norm_bounds .high hz
  obtain ⟨hrH,_,hrB,hrD,_,hrG,_⟩ := ordinary_masses_positive .high hz
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .high hz)
  have hcos := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (family_positive .high hz).2.1.le
  have hA : aeval z (elementary .high+l .high*(C10-1))≤
      nonradical .high z+Explicit.l .high z*(Real.cos z-1) := by
    simp only [map_add,map_mul,map_sub,map_one,l_eval]
    linarith [elementary_lower .high hz]
  have hp := PositiveTD.Certificate.num4_transfer hrH hrB hrG hrD
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hn.1 hn.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.1 hA
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      (high_numerators_positive hz).2.1)
  have he := zero_reduced_identity .high hz
  have hl := reduced_zero_le (f:=Family.high) (z:=z)
  dsimp [normSum] at he
  dsimp [V]
  nlinarith only [hp,he,hl]

theorem high_B_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<PositiveTD.baseline (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z+
      V R (min (Explicit.l .high z) (Explicit.m .high z))
        (max (Explicit.l .high z) (Explicit.m .high z)) z := by
  have hn := ordinary_norm_bounds .high hz
  obtain ⟨hrH,hrG,_,hrD,_,_,hrB⟩ := ordinary_masses_positive .high hz
  have ht := PositiveTD.Certificate.taylor_bounds (family_frame_domain .high hz)
  have hq : max (Explicit.l .high z) (Explicit.m .high z)≤aeval z (qStar .high) := by
    simpa [qStar,h,frameCap] using high_tilted_envelope hz
  have hq0 : 0≤aeval z (qStar .high) :=
    ((family_positive .high hz).2.1.le.trans (le_max_left _ _)).trans hq
  have hcos₁ := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1) hq0
  have hcos₂ := mul_le_mul_of_nonpos_right hq (sub_nonpos.mpr (Real.cos_le_one z))
  have hA : aeval z (elementary .high+qStar .high*(C10-1))≤
      nonradical .high z+max (Explicit.l .high z) (Explicit.m .high z)*(Real.cos z-1) := by
    simp only [map_add,map_mul,map_sub,map_one]
    linarith [elementary_lower .high hz]
  have hp := PositiveTD.Certificate.num4_transfer hrH hrG hrB hrD
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hn.1 hn.2.1 hn.2.2.2.2.2.2 hn.2.2.2.1 hA
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      (high_numerators_positive hz).2.2.1)
  have he := zero_reduced_identity .high hz
  have hl := reduced_zero_le (f:=Family.high) (z:=z)
  dsimp [normSum] at he
  simp only [V,sorted_pair_norm]
  nlinarith only [hp,he,hl]

theorem equal_GA_endpoint (f : Family) {z : ℝ}
    (hz : z∈Icc (left f:ℝ) (right f:ℝ)) :
    0<baseline true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z := by
  have hz' := family_frame_domain f hz
  have hc : 0<Real.cos z := by linarith [(transport_trig hz').1]
  have hn := equal_GA_norm_bounds f hz
  have hr := equal_GA_masses_positive f hz
  have hnonneg := scaled_norms_nonnegative f true (z:=z) hz'
  have hA := equal_elementary_lower f hz
  have he := scaled_identity f true hz hz'
  have hp : 0<Real.cos z*reducedBaseline f true z z := by
    cases f
    · have hN : 0<aeval z (PositiveTD.Certificate.num3 (AZ .low)
          (equalGAP .low 0) (equalGAP .low 1) (equalGAP .low 2)
          (equalGAR .low 0) (equalGAR .low 1) (equalGAR .low 2)) := by
        simpa [NZ] using (low_numerators_positive hz).2.1
      have hh := PositiveTD.Certificate.num3_transfer (hr 0) (hr 1) (hr 2)
        (hnonneg 0) (hnonneg 1) (hnonneg 2) (hn 0) (hn 1) (hn 2) hA hN
      simpa only [he,normSum,↓reduceIte] using hh
    · have hN : 0<aeval z (PositiveTD.Certificate.num4 (AZ .high)
          (equalGAP .high 0) (equalGAP .high 1) (equalGAP .high 2) (equalGAP .high 3)
          (equalGAR .high 0) (equalGAR .high 1) (equalGAR .high 2) (equalGAR .high 3)) := by
        simpa [NZ] using (high_numerators_positive hz).2.2.2.1
      have hh := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
        (hnonneg 0) (hnonneg 1) (hnonneg 2) (hnonneg 3)
        (hn 0) (hn 1) (hn 2) (hn 3) hA hN
      simpa only [he,normSum,↓reduceIte] using hh
  have hb := (mul_pos_iff_of_pos_left hc).mp hp
  exact hb.trans_le (reduced_le_baseline f true z z)

theorem equal_AB_endpoint {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<baseline false (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z := by
  have hz' := family_frame_domain .high hz
  have hc : 0<Real.cos z := by linarith [(transport_trig hz').1]
  have hn := equal_AB_norm_bounds hz
  have hr := equal_AB_masses_positive hz
  have hnonneg := scaled_norms_nonnegative .high false (z:=z) hz'
  have hp := PositiveTD.Certificate.num4_transfer (hr 0) (hr 1) (hr 2) (hr 3)
    (hnonneg 0) (hnonneg 1) (hnonneg 2) (hnonneg 3)
    (hn 0) (hn 1) (hn 2) (hn 3) (equal_elementary_lower .high hz)
    (show 0<aeval z (PositiveTD.Certificate.num4 _ _ _ _ _ _ _ _ _) from
      (high_numerators_positive hz).2.2.2.2)
  have he := scaled_identity .high false hz hz'
  have hprod : 0<Real.cos z*reducedBaseline .high false z z := by
    simpa only [he,normSum,↓reduceIte] using hp
  exact ((mul_pos_iff_of_pos_left hc).mp hprod).trans_le
    (reduced_le_baseline .high false z z)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Certificate
