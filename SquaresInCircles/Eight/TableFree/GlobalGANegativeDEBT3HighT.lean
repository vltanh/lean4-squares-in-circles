module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighDerivative

/-!
# The complete high-T negative-DE interval

Uncompiled conclusion of Section 7. The original total and coefficients
are fixed while the DE magnitude varies through its whole closed
interval. The shared third-derivative theorem, now supplied with the
actual BT3 domain and right derivative, reduces the stress to the two
proved intrinsic endpoints. No shape or derivative premise remains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighT
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.SecantCoordinate

lemma pure_at_original {θ s : ℝ} (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    pure (Explicit.fullBaseline .high 0 θ 0) 1 (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ (Real.tan s)=
      Explicit.fullBaseline .high 0 θ s+Explicit.V .high θ i (θ-s) := by
  have hc := NegativeESecant.cos_pos hs
  have hn := normalized_arctan (Explicit.c .high θ θ) (Real.tan s)
  rw [arctan_tan hs] at hn
  have hg : SecantNormCurvature.normalized R (Explicit.c .high θ θ) s=
      secantGain qCap (Explicit.c .high θ θ) s := by
    rw [secantGain_eq_secant_expression qCap (Explicit.c .high θ θ) hc]
    dsimp [SecantNormCurvature.normalized,SecantNormCurvature.secant,SecantNormCurvature.supportNorm]
    rw [add_comm ((Explicit.c .high θ θ)^2) ((1/Real.cos s)^2),
      add_comm ((Explicit.c .high θ θ)^2) 1]
    ring
  dsimp [pure,Explicit.V]
  rw [arctan_tan hs,←hn,hg,Explicit.full_correction .high 0 θ hs]
  simp only [zero_add]
  ring

theorem endpoint_minimum {θ s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 θ) (i : Fin 3) :
    min (Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ i θ)
        (Explicit.fullBaseline .high 0 θ θ)≤
      Explicit.fullBaseline .high 0 θ s+Explicit.V .high θ i (θ-s) := by
  have hf := Explicit.frame_domain .high hθ
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans hf.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan θ) :=
    ⟨tan_nonnegative hsf,tan_monotone hsf hf hs.2⟩
  have hh := NegativeDEHighShape.pure_endpoint_minimum
    (B:=Explicit.fullBaseline .high 0 θ 0) true (HighShape.shape_domain hθ i) hx
    (HighDerivative.first_right_negative hθ i).le
  have h0 : pure (Explicit.fullBaseline .high 0 θ 0) 1 (Explicit.c .high θ θ)
      (Explicit.p .high θ i) (Explicit.q .high θ i) θ 0=
      Explicit.fullBaseline .high 0 θ 0+Explicit.V .high θ i θ := by
    simp [pure,Explicit.V]
  have h1 := pure_at_original (θ:=θ) hf i
  simp only [sub_self,Explicit.V,V_zero,add_zero] at h1
  rw [h0,h1,pure_at_original hsf i] at hh
  exact hh

/-- Complete continuous T-endpoint positivity, with all three original pairs. -/
theorem negative_positive {θ s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hs : s∈Icc 0 θ) (i : Fin 3) :
    0<Explicit.fullBaseline .high 0 θ s+Explicit.V .high θ i (θ-s) :=
  (lt_min (HighTransfer.zero_positive i hθ) (HighTransfer.equal_positive hθ)).trans_le
    (endpoint_minimum hθ hs i)

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.HighT
