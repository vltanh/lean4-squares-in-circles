import SquaresInCircles.Six.Normalization.Complete
import SquaresInCircles.Six.Stress.CandidateRadiusConstants

/-!
# The exact candidate-radius interface for downstream stresses

The elementary constant algebra lives in CandidateRadiusConstants, independent
of normalization. This file contains only the actual-packing upgrade: the
already established E/N separator alternatives imply the sharper central box.
The normalization chain still needs its human-analytic conversion.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

lemma PinPacking.contained_at_candidate {R : ℝ} (P : PinPacking R) (hR : R^2 ≤ Six.qStar)
    (i : Fin 5) :
    (P.radial i+1/2)^2+(|P.transverse i|+1/2)^2 ≤ Six.qStar := by
  have h := (P.packing.phi_le i.succ).trans hR
  simpa [pinModel_succ,orientedSquare_alpha,orientedSquare_beta,phi,
    abs_of_nonneg (show 0 ≤ P.radial i by linarith [(P.contained i).half_le])] using h

private lemma own_east_at_sharp_radius {a cx cy t : ℝ}
    (ha : a ≤ rhoStar) (hx : cStar < cx) (hy0 : 0 ≤ cy) (hy : cy ≤ cx+1/10)
    (ht : |t| ≤ Real.pi/4) : centralMargin .own t a 0 cx cy < 0 := by
  have htr := east_quadrant_trig (abs_nonneg t) ht
  have hcx0 : 0 < cx := cStar_pos.trans hx
  have hA : rhoStar-1/2 < 1/2+cx := by dsimp [cStar] at hx; linarith
  have hf := east_linear_support_gt
    (A := 1/2+cx) (k := rhoStar-1/2) (c := Real.cos |t|) (s := Real.sin |t|)
    (by linarith [rhoStar_upper]) hA htr.1 htr.2.1 htr.2.2
    (by nlinarith [Real.sin_sq_add_cos_sq |t|])
  have hc : 0 ≤ Real.cos t := by
    have h := htr.1
    rw [Real.cos_abs] at h
    linarith
  rw [Real.cos_abs] at hf
  by_cases ht0 : 0 ≤ t
  · have hs : 0 ≤ Real.sin t := by simpa only [abs_of_nonneg ht0] using htr.2.1
    rw [abs_of_nonneg ht0] at hf
    have hp := mul_nonneg (show 0 ≤ cx+cy+1/10 by linarith) hs
    dsimp [centralMargin,centralNormal,angularWidth]
    rw [abs_of_nonneg hc,abs_of_nonneg hs]
    nlinarith
  · have htneg := lt_of_not_ge ht0
    have hs : Real.sin t ≤ 0 := by
      have h := htr.2.1
      rw [abs_of_neg htneg,Real.sin_neg] at h
      linarith
    rw [abs_of_neg htneg,Real.sin_neg] at hf
    have hp := mul_nonneg (show 0 ≤ cx-cy+1/10 by linarith)
      (show 0 ≤ -Real.sin t by linarith)
    dsimp [centralMargin,centralNormal,angularWidth]
    rw [abs_of_nonneg hc,abs_of_nonpos hs]
    nlinarith

lemma PinPacking.sharp_east_center {R : ℝ} (P : PinPacking R) (hR : R^2 ≤ Six.qStar) :
    P.center.1 ≤ cStar := by
  by_contra! hx
  have hc := P.contained_at_candidate hR 0
  have ha := sharp_coordinate_bound
    (show 0 ≤ P.radial 0 by linarith [(P.contained 0).half_le]) (abs_nonneg _) hc
  have hw := P.window 0
  norm_num [Certificates.phaseCenter,Certificates.windowLower,Certificates.windowUpper] at hw
  have ht : |P.phase 0| ≤ Real.pi/4 := by
    apply abs_le.mpr
    constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2]
  have hcy : P.center.2 ≤ P.center.1+1/10 := by
    have hb := P.box.2.2
    dsimp [cStar,c0] at hx hb
    linarith [rhoStar_gt_11_10,rho0_upper]
  obtain ⟨k,hk⟩ := P.separator 0
  have hallowed := P.allowed_separator 0 k hk
  have hcases : k=.own ∨ k=.east := by simpa [Certificates.allowed] using hallowed
  rcases hcases with rfl | rfl
  · have hn := own_east_at_sharp_radius ha hx P.box.2.1 hcy ht
    change 0 ≤ P.radial 0-1/2-centralNormal (P.phase 0) P.center.1 P.center.2-
      angularWidth (P.phase 0) at hk
    change P.radial 0-1/2-centralNormal (P.phase 0) P.center.1 P.center.2-
      angularWidth (P.phase 0) < 0 at hn
    linarith
  · have hP := sharp_projection_bound
      (show 0 ≤ P.radial 0 by linarith [(P.contained 0).half_le]) hc (t := P.phase 0)
    have hwidth := one_le_abs_cos_add_abs_sin (P.phase 0)
    dsimp [centralMargin,centerX,angularWidth] at hk
    dsimp [cStar] at hx
    linarith

/-- The exact candidate-radius box used in tight A2 stresses is derived, not assumed. -/
theorem PinPacking.sharp_central_box {R : ℝ} (P : PinPacking R) (hR : R^2 ≤ Six.qStar) :
    (0 ≤ P.center.1 ∧ P.center.1 ≤ cStar) ∧ (0 ≤ P.center.2 ∧ P.center.2 ≤ cStar) := by
  have hx := P.sharp_east_center hR
  have hy := P.mirror.sharp_east_center hR
  exact ⟨⟨P.box.1.1,hx⟩,⟨P.box.2.1,hy⟩⟩

/-- Exterior containment at the exact candidate radius for support applications. -/
lemma PinPacking.contained_in_candidate_disk {R : ℝ} (P : PinPacking R)
    (hR : R^2 ≤ Six.qStar) (i : Fin 5) :
    ∀ p, closedSquare (orientedSquare (P.phase i) (P.radial i) (P.transverse i)) p →
      inDisk (0,0) Six.radius p := by
  intro p hp
  have h := P.packing.2.1 i.succ p hp
  change normSq (sub p (0,0)) ≤ Six.radius^2
  rw [Six.radius_sq]
  exact h.trans hR

end SquaresInCircles.Six.Stress
