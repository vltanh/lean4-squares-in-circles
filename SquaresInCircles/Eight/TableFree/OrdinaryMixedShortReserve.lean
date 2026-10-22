module

public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeShortSlope

/-!
# The positive-surplus companion of the short same-block reserve

Uncompiled whole-interval proof of (17) in the far-low EH companion.
The positive angle may range up to the original frame cap; only the
common negative mass is bounded by .6. Monotonicity moves the positive
angle to the true cap before its trigonometric coefficients are bounded.
In particular no false separate lower bound for phi(P) is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OrdinaryMixedShortReserve
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeShortSlope

lemma constant_add {f : ℝ→ℝ} {l u : ℝ}
    (hf : ConcaveOn ℝ (Icc l u) f) (C : ℝ) :
    ConcaveOn ℝ (Icc l u) (fun t => C+f t) := by
  refine ⟨hf.1,?_⟩
  intro x hx y hy r v hr hv hrv
  have hh := hf.2 hx hy hr hv hrv
  have he := congrArg (fun w : ℝ => w*C) hrv
  simp only [smul_eq_mul] at hh ⊢
  nlinarith only [hh,he]

def phiD (t : ℝ) : ℝ := Real.cos t-Real.sin t

lemma phi_hasDerivAt (t : ℝ) : HasDerivAt phi (phiD t) t := by
  convert (Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t) using 1 <;>
    dsimp [phi,phiD] <;> ring

lemma phiD_hasDerivAt (t : ℝ) : HasDerivAt phiD (-phi t) t := by
  convert (Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t) using 1 <;>
    dsimp [phi,phiD] <;> ring

lemma phiD_antitone : AntitoneOn phiD (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t _ => (phiD_hasDerivAt t).continuousAt.continuousWithinAt)
    (fun t _ => phiD_hasDerivAt t)
  intro t ht
  have hh := transport_trig (Ioo_subset_Icc_self ht)
  dsimp [phi]
  linarith [hh.1,hh.2.2.1]

lemma phiD_cap : (3/25:ℝ)<phiD frameCap := by
  have hh := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  dsimp [phiD]
  linarith [hh.1,hh.2.2.2.1]

lemma short_half_angle {N : ℝ} (hN : N∈OrdinaryNegativeShortSlope.domain) :
    1-Real.cos N≤(31/100)*Real.sin N := by
  have hc := cosine_antitone (subset_frame hN)
    (show (3/5:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hN.2
  have hc0 : (33/40:ℝ)≤Real.cos N := by linarith [cap_trig.2.2]
  have hs := (trig_bounds hN).2.1
  have hs0 := (transport_trig (subset_frame hN)).2.2.1
  have hpaid := mul_nonneg hs0
    (show 0≤(31/100)*(1+Real.cos N)-Real.sin N by linarith)
  have hden : 0<1+Real.cos N := by linarith
  apply (mul_le_mul_right hden).mp
  nlinarith [Real.sin_sq_add_cos_sq N]

lemma shifted_phi_antitone {N : ℝ} (hN : N∈Icc 0 frameCap) :
    AntitoneOn (fun P => phi P-phi (P-N)) (Icc N frameCap) := by
  have hd (P : ℝ) : HasDerivAt (fun P => phi P-phi (P-N))
      (phiD P-phiD (P-N)) P := by
    convert (phi_hasDerivAt P).sub
      ((phi_hasDerivAt (P-N)).comp P ((hasDerivAt_id P).sub_const N)) using 1 <;> ring
  apply antiOn_of_hasDeriv_nonpos
    (fun P _ => (hd P).continuousAt.continuousWithinAt) (fun P _ => hd P)
  intro P hP
  have hp : P∈Icc 0 frameCap := ⟨hN.1.trans hP.1.le,hP.2.le⟩
  have hdiff : P-N∈Icc 0 frameCap := ⟨by linarith [hP.1],by linarith [hP.2,hN.1]⟩
  have hh := phiD_antitone hdiff hp (by linarith [hN.1])
  linarith

lemma cap_difference (N : ℝ) :
    phi frameCap-phi (frameCap-N)=
      phi frameCap*(1-Real.cos N)+phiD frameCap*Real.sin N := by
  dsimp [phi,phiD]
  rw [Real.cos_sub,Real.sin_sub]
  ring

lemma same_positive_difference (R p q P N : ℝ) :
    mixedBlock R p q P N-U R p q (P-N)=
      p*(phi P-phi (P-N))+q*(Real.cos N-1) := by
  dsimp [mixedBlock,U]
  ring

/-- This pays the extra charge on the removed common negative mass. -/
theorem same_positive_reserve {R p q P N : ℝ}
    (hp : (3/5:ℝ)≤p) (hqp : q≤(5/3)*p)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) (hNs : N≤3/5) :
    U R p q (P-N)+(1/50)*N≤mixedBlock R p q P N := by
  have hNd : N∈OrdinaryNegativeShortSlope.domain := ⟨hN,hNs⟩
  have hframe := subset_frame hNd
  have hh := shifted_phi_antitone hframe
    (show P∈Icc N frameCap from ⟨hNP,hP⟩)
    (show frameCap∈Icc N frameCap from ⟨hframe.2,le_rfl⟩) hP
  have hshift := mul_le_mul_of_nonneg_left hh (show 0≤p by linarith)
  have hqterm := mul_le_mul_of_nonpos_right hqp (sub_nonpos.mpr (Real.cos_le_one N))
  have hsN := (transport_trig hframe).2.2.1
  have hfirst := mul_le_mul_of_nonneg_right phi_cap_lower.le
    (sub_nonneg.mpr (Real.cos_le_one N))
  have hsecond := mul_le_mul_of_nonneg_right phiD_cap.le hsN
  have htan := mul_le_mul_of_nonpos_left (short_half_angle hNd)
    (by norm_num : (1409/1000:ℝ)-5/3≤0)
  have hlinear := mul_le_mul_of_nonneg_left (trig_bounds hNd).2.2
    (by norm_num : (0:ℝ)≤1/25)
  have hunit : (47/1250)*N≤phi frameCap-phi (frameCap-N)+
      (5/3)*(Real.cos N-1) := by
    rw [cap_difference]
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_left hunit (show 0≤p by linarith)
  have hscale := mul_nonneg (sub_nonneg.mpr hp) hN
  have he := same_positive_difference R p q P N
  nlinarith

end SquaresInCircles.Eight.TableFree.OrdinaryMixedShortReserve
