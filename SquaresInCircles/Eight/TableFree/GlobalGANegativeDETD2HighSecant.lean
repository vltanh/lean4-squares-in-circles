module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighConcentration
public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveScalar

/-!
# The high negative-DE baseline and its positive-surplus branch

Uncompiled transcription of the full-D derivative reserve in Section 8.
The actual baseline is a constant plus the exact secant gain.  The
reserve .96 dominates every original positive ordinary slope, so the
positive-surplus branch reduces to the equal-angle endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.HighSecant
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

private theorem r74_high {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    θ∈Icc ((Certificate.left .high:ℚ):ℝ) ((Certificate.right .high:ℚ):ℝ) := by
  simpa [Certificate.left,Certificate.right,PositiveTD.Certificate.L,
    PositiveTD.Certificate.h] using hθ

theorem full_gain_identity (f : Family) (a z : ℝ) {s : ℝ}
    (hs : s∈Icc 0 frameCap) :
    Explicit.fullBaseline f a z s=Explicit.fullBaseline f a z 0+
      secantGain qCap (Explicit.c f (a+z)) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [secantGain_eq_secant_expression qCap (Explicit.c f (a+z)) hc]
  simp only [Explicit.fullBaseline,Explicit.baseline,fullSupport_pair,
    Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,sub_self,
    add_zero,sub_zero]
  simp only [pairNorm,Real.sin_zero,mul_zero,add_zero,one_pow]
  rw [show (Explicit.c f (a+z))^2+(1/Real.cos s)^2=
    (1/Real.cos s)^2+(Explicit.c f (a+z))^2 by ring,
    show (Explicit.c f (a+z))^2+1=1+(Explicit.c f (a+z))^2 by ring]
  dsimp [Explicit.K]
  ring

theorem full_derivative_lower {c s : ℝ} (hc : (43/50:ℝ)≤c)
    (hs : s∈Icc 0 frameCap) : (24/25:ℝ)<secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hcos : 0<Real.cos s := by linarith [ht.1]
  have hcoeff := NegativeAPositiveTD.SecantBaseline.coefficient_upper
    (r:=c) (s:=s) (r₀:=43/50) (c₀:=478/625) (D:=83/50)
    (by norm_num) (by norm_num) (by norm_num) hc (by linarith [ht.1])
    (by norm_num [qCap])
  have hm := mul_le_mul_of_nonneg_right hcoeff.le ht.2.2.1
  have he : R*Real.sin s/NegativeAPositiveTD.SecantBaseline.denominator c s=
      (R/NegativeAPositiveTD.SecantBaseline.denominator c s)*Real.sin s := by ring
  change (24/25:ℝ)<(13/12+Real.sin s-
    R*Real.sin s/NegativeAPositiveTD.SecantBaseline.denominator c s)/Real.cos s^2
  apply (lt_div_iff₀ (sq_pos_of_pos hcos)).2
  rw [he]
  nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s-11/32)]

theorem high_gain_derivative_lower {θ s : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hs : s∈Icc 0 frameCap) :
    (24/25:ℝ)<secantGainDeriv qCap (Explicit.c .high θ) s := by
  apply full_derivative_lower _ hs
  linarith [(Explicit.high_ranges hθ).2.2.2.2.1]

theorem positive_surplus_mono {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    MonotoneOn (fun s => secantGain qCap (Explicit.c .high θ) s+
      Explicit.U .high θ z i (s-θ)) (Icc θ frameCap) := by
  have hp := Explicit.high_pairs hθ hz i
  have hq := hp.1.trans_le hp.2.1
  have hqp : Explicit.q .high θ z i≤2*Explicit.p .high θ z i := by
    linarith [hp.2.2.1]
  have hd (s : ℝ) (hs : s∈Icc θ frameCap) :
      HasDerivAt (fun s => secantGain qCap (Explicit.c .high θ) s+
        Explicit.U .high θ z i (s-θ))
      (secantGainDeriv qCap (Explicit.c .high θ) s+
        NegativeAPositiveTD.PositiveSlope.Ud (Explicit.p .high θ z i) (Explicit.q .high θ z i) (s-θ)) s := by
    have hsf : s∈Icc 0 frameCap := ⟨by linarith [hθ.1,hs.1],hs.2⟩
    have hx : s-θ∈Icc 0 frameCap := ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩
    have hg := secantGain_hasDerivAt qCap (Explicit.c .high θ)
      (show Real.cos s≠0 by linarith [(transport_trig hsf).1])
    have hu : HasDerivAt (fun s => Explicit.U .high θ z i (s-θ))
        (NegativeAPositiveTD.PositiveSlope.Ud (Explicit.p .high θ z i)
          (Explicit.q .high θ z i) (s-θ)) s := by
      have hc := (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt hp.1 hq hx).comp s
        ((hasDerivAt_id s).sub_const θ)
      simpa only [Explicit.U,mul_one,Function.comp_def,id] using hc
    exact hg.add hu
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s (Ioo_subset_Icc_self hs))
  intro s hs
  have hsf : s∈Icc 0 frameCap := ⟨by linarith [hθ.1,hs.1],hs.2.le⟩
  have hx : s-θ∈Icc 0 frameCap :=
    ⟨by linarith [hs.1],by linarith [hs.2,hθ.1]⟩
  have hg := high_gain_derivative_lower hθ hsf
  have hu := OrdinarySlope.positive_derivative_whole hp.1 hp.2.1 hqp hx
  linarith [hp.2.2.2.2]

theorem high_equal_le_positive_surplus {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 (a+z))
    (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    Explicit.fullBaseline .high a z (a+z)≤Explicit.fullBaseline .high a z s+
      Explicit.U .high (a+z) z i (s-(a+z)) := by
  have hf := Certificate.family_frame_domain .high (r74_high hθ)
  have hsf : s∈Icc 0 frameCap := ⟨hf.1.trans hs.1,hs.2⟩
  have hh := positive_surplus_mono hθ hz i ⟨le_rfl,hf.2⟩ hs hs.1
  simp only [sub_self,Explicit.U,U_zero,add_zero] at hh
  rw [full_gain_identity .high a z hf,full_gain_identity .high a z hsf]
  dsimp only [Explicit.U]
  linarith

theorem pure_at_original {a z s : ℝ} (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    NegativeAPositiveTD.SecantCoordinate.pure (Explicit.fullBaseline .high a z 0) 1
      (Explicit.c .high (a+z)) (Explicit.p .high (a+z) z i)
      (Explicit.q .high (a+z) z i) (a+z) (Real.tan s)=
      Explicit.fullBaseline .high a z s+Explicit.V .high (a+z) z i (a+z-s) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hnorm := NegativeAPositiveTD.SecantCoordinate.normalized_arctan (Explicit.c .high (a+z)) (Real.tan s)
  rw [NegativeAPositiveTD.SecantCoordinate.arctan_tan hs] at hnorm
  have hg : SecantNormCurvature.normalized R (Explicit.c .high (a+z)) s=
      secantGain qCap (Explicit.c .high (a+z)) s := by
    rw [secantGain_eq_secant_expression qCap (Explicit.c .high (a+z)) hc]
    dsimp [SecantNormCurvature.normalized,SecantNormCurvature.secant,
      SecantNormCurvature.supportNorm]
    rw [add_comm ((Explicit.c .high (a+z))^2) ((1/Real.cos s)^2),
      add_comm ((Explicit.c .high (a+z))^2) 1]
    ring
  dsimp [NegativeAPositiveTD.SecantCoordinate.pure,Explicit.V]
  rw [NegativeAPositiveTD.SecantCoordinate.arctan_tan hs,←hnorm,hg,full_gain_identity .high a z hs]
  ring

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.HighSecant
