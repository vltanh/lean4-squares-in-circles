import SquaresInCircles.Six.Normalization.Complete
import SquaresInCircles.Six.Stress.ExactSupport

/-!
# The exact candidate-radius interface for downstream stresses

Normalization uses Q0. Tight A2/equality stresses use qStar and therefore need
the corresponding rho and central box, not a silent substitution of Q0's c0.
The upgrade below uses the already proved E/N separator alternatives and the
coarse strong box. It does not feed back into the normalization proof.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

/-- Exact candidate-radius center and central-cap constants. -/
def rhoStar : ℝ := rhoAt Six.radius
def cStar : ℝ := rhoStar-1

lemma radius_gt_three_halves : 3/2 < Six.radius := by
  have hs := Six.sStar_pos
  have hq : 5/2 < Six.qStar := by
    dsimp [Six.qStar]
    nlinarith [sq_nonneg Six.sStar]
  have hr := Six.radius_sq
  have hp := Six.radius_pos
  nlinarith

lemma radius_gt_half : 1/2 < Six.radius := by linarith [radius_gt_three_halves]

lemma rhoStar_identity : rhoStar^2+rhoStar+1/2=Six.qStar := by
  have hnonneg : 0 ≤ Six.radius^2-1/4 := by
    nlinarith [radius_gt_half,Six.radius_pos]
  have h := Real.sq_sqrt hnonneg
  dsimp [rhoStar,rhoAt]
  rw [← Six.radius_sq]
  nlinarith

lemma rhoStar_gt_11_10 : 11/10 < rhoStar := by
  have hs := Six.sStar_bounds.1
  have hp := mul_nonneg (show 0 ≤ Six.sStar-2/25 by linarith)
    (show 0 ≤ Six.sStar+2/25 by linarith [Six.sStar_pos])
  have hq : (8/5:ℝ)^2 < Six.radius^2-1/4 := by
    rw [Six.radius_sq]
    dsimp [Six.qStar]
    nlinarith
  have hroot := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ (8/5)^2) hq
  rw [Real.sqrt_sq (by norm_num)] at hroot
  dsimp [rhoStar,rhoAt]
  linarith

lemma rhoStar_lt_rho0 : rhoStar < rho0 := by
  have hroot := Real.sqrt_lt_sqrt
    (show 0 ≤ Six.radius^2-1/4 by nlinarith [radius_gt_half,Six.radius_pos])
    (show Six.radius^2-1/4 < Q0-1/4 by rw [Six.radius_sq]; linarith [Six.qStar_lt_Q0])
  dsimp [rhoStar,rhoAt,rho0]
  linarith

lemma rhoStar_upper : rhoStar < 1113/1000 := rhoStar_lt_rho0.trans rho0_upper
lemma cStar_pos : 0 < cStar := by dsimp [cStar]; linarith [rhoStar_gt_11_10]
lemma cStar_lt_c0 : cStar < c0 := by dsimp [cStar,c0]; linarith [rhoStar_lt_rho0]

lemma sharp_coordinate_bound {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hc : (a+1/2)^2+(u+1/2)^2 ≤ Six.qStar) : a ≤ rhoStar := by
  have hs : (a+1/2)^2 ≤ Six.radius^2-1/4 := by
    rw [Six.radius_sq]
    nlinarith [sq_nonneg u]
  have hh := Real.le_sqrt_of_sq_le hs
  dsimp [rhoStar,rhoAt]
  linarith

lemma sharp_center_radius {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hc : (a+1/2)^2+(u+1/2)^2 ≤ Six.qStar) : a^2+u^2 ≤ rhoStar^2 := by
  by_contra! h
  have hsum : a+u < rhoStar := by nlinarith [rhoStar_identity]
  have hp := mul_pos (sub_pos.mpr hsum)
    (show 0 < rhoStar+a+u by linarith [rhoStar_gt_11_10])
  nlinarith [mul_nonneg ha hu]

lemma sharp_projection_bound {a b t : ℝ}
    (ha : 0 ≤ a) (hc : (a+1/2)^2+(|b|+1/2)^2 ≤ Six.qStar) :
    a*Real.cos t-b*Real.sin t ≤ rhoStar := by
  have hn := sharp_center_radius ha (abs_nonneg b) hc
  rw [sq_abs] at hn
  have hid : (a*Real.cos t-b*Real.sin t)^2+
      (a*Real.sin t+b*Real.cos t)^2=a^2+b^2 := by
    linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq t)
  have hs : (a*Real.cos t-b*Real.sin t)^2 ≤ rhoStar^2 := by
    nlinarith [sq_nonneg (a*Real.sin t+b*Real.cos t)]
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < a*Real.cos t-b*Real.sin t+rhoStar by linarith [rhoStar_gt_11_10])
  nlinarith

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
