import SquaresInCircles.Six.Stress.CandidateRadius

/-!
# N26 at the exact candidate radius

The uploaded revision uses 4*cStar, not merely 4*c0. The two cardinal cap
hypotheses remain indispensable. This derives the sharper bound directly from
candidate-radius containment, without re-running normalization or assuming its
Q0 constants equal the candidate constants.

For small angles the exact cap support applies. Above 29/100 the universal
far-vertex bound suffices. The rational estimates prove strict loss on both
ranges; zero angles are handled separately. Compilation remains deferred.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

private lemma candidate_radius_upper : Six.radius < 1689 / 1000 := by
  have h : Six.radius < R0 := Real.sqrt_lt_sqrt Six.qStar_pos.le Six.qStar_lt_Q0
  exact h.trans R0_lt_1689_1000

private lemma candidate_radial_gap : -5 / 64 < rhoStar + 1 / 2 - Six.radius := by
  have hr : 8 / 5 < Six.radius := by
    nlinarith [rhoStar_identity, rhoStar_gt_11_10, Six.radius_sq, Six.radius_pos,
      sq_nonneg (rhoStar - 11 / 10)]
  have hid : Six.radius ^ 2 - (rhoStar + 1 / 2) ^ 2 = 1 / 4 := by
    nlinarith [rhoStar_identity, Six.radius_sq]
  by_contra! h
  have hp := mul_nonneg
    (show 0 ≤ Six.radius - (rhoStar + 1 / 2) - 5 / 64 by linarith)
    (show 0 ≤ Six.radius + (rhoStar + 1 / 2) by linarith [rhoStar_gt_11_10])
  nlinarith [rhoStar_gt_11_10]

lemma candidate_cap_tilt_strict {a b height t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 2 / 5)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Six.radius ^ 2)
    (hcap : height + (Real.cos t + Real.sin t) / 2 ≤
      |a| * Real.cos t + |b| * Real.sin t) :
    height < rhoStar - 1 / 2 - t / 2 := by
  have htr := small_cap_trig ht0.le ht
  have hc0 : 0 ≤ Real.cos t := by linarith [htr.1]
  have hs0 : 0 ≤ Real.sin t := htr.2.1
  have hunit : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  by_cases hlo : t ≤ 29 / 100
  · have hsin : Real.sin t ≤ 29 / 100 := (Real.sin_le ht0.le).trans hlo
    have hprod := mul_le_mul candidate_radius_upper.le hsin hs0 (by norm_num)
    have hswitch : 2 * Six.radius * Real.sin t ≤ 1 := by nlinarith
    have hsupp := ordered_center_support radius_gt_half hc0 hs0 hbox
    rw [orderedSupport, hunit, Real.sqrt_one, if_pos hswitch] at hsupp
    change |a| * Real.cos t + |b| * Real.sin t ≤ rhoStar * Real.cos t at hsupp
    have hcos := cos_le_one_sub_fifth_sq (t := t)
      (by rw [abs_of_pos ht0]; linarith [Real.pi_gt_d2])
    have hm := mul_le_mul_of_nonneg_left hcos
      (show 0 ≤ rhoStar - 1 / 2 by linarith [rhoStar_gt_11_10])
    have hsinLow := Real.sin_ge_sub_cube ht0.le
    have hcoef : 0 < (rhoStar - 1 / 2) / 5 - t / 12 := by
      linarith [rhoStar_gt_11_10]
    have hstrict := mul_pos (pow_pos ht0 2) hcoef
    nlinarith
  · have hround := dot_le_radius (v := (Real.cos t, Real.sin t))
      (p := (|a| + 1 / 2, |b| + 1 / 2)) Six.radius_pos.le hbox
    dsimp [dot, vectorLength, normSq] at hround
    rw [hunit, Real.sqrt_one, mul_one] at hround
    have hsq := mul_nonneg (sub_nonneg.mpr ht)
      (show 0 ≤ (2 : ℝ) / 5 + t by linarith)
    have hcoef : (41 : ℝ) / 150 ≤ 1 / 2 - t / 2 - t ^ 2 / 6 := by nlinarith
    have hm := mul_nonneg ht0.le (sub_nonneg.mpr hcoef)
    have hsin := Real.sin_ge_sub_cube ht0.le
    have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
    have htlo : 29 / 100 < t := lt_of_not_ge hlo
    nlinarith [candidate_radial_gap]

lemma candidate_cap_tilt_weak {a b height t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 / 5)
    (hbox : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Six.radius ^ 2)
    (hcap : height + (Real.cos t + Real.sin t) / 2 ≤
      |a| * Real.cos t + |b| * Real.sin t) :
    height ≤ rhoStar - 1 / 2 - t / 2 := by
  by_cases hz : t = 0
  · have hb : (|a| + 1 / 2) ^ 2 + (|b| + 1 / 2) ^ 2 ≤ Six.qStar := by
      simpa only [Six.radius_sq] using hbox
    have ha := sharp_coordinate_bound (abs_nonneg a) (abs_nonneg b) hb
    simp only [hz, Real.cos_zero, Real.sin_zero, add_zero, mul_one, mul_zero,
      zero_div, sub_zero] at hcap ⊢
    linarith
  · exact (candidate_cap_tilt_strict (lt_of_le_of_ne ht0 (Ne.symm hz)) ht hbox hcap).le

/-- Both the weak loss and its strict nonzero-angle form in the actual cap. -/
lemma PinPacking.cardinal_tilt_at_candidate {R : ℝ} (P : PinPacking R)
    (hR : R ^ 2 ≤ Six.qStar) (i : Fin 5)
    (hi : 0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i)
      (P.transverse i) P.center.1 P.center.2) :
    cardinalDepth P.center (matchingCardinal i) ≤ rhoStar - 1 / 2 -
        |P.phase i - cardinalCenter (matchingCardinal i)| / 2 ∧
      (0 < |P.phase i - cardinalCenter (matchingCardinal i)| →
        cardinalDepth P.center (matchingCardinal i) < rhoStar - 1 / 2 -
          |P.phase i - cardinalCenter (matchingCardinal i)| / 2) := by
  let z := P.phase i - cardinalCenter (matchingCardinal i)
  have ht : |z| < 2 / 5 := P.matching_cardinal_angle i hi
  have hc0 : 0 ≤ Real.cos z := (Real.cos_pos_of_mem_Ioo
    (show z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      have hb := abs_lt.mp ht
      constructor <;> linarith [Real.pi_gt_d2])).le
  have hbox : (|P.radial i| + 1 / 2) ^ 2 + (|P.transverse i| + 1 / 2) ^ 2 ≤ Six.radius ^ 2 := by
    have h := (P.packing.phi_le i.succ).trans hR
    simpa only [pinModel_succ, orientedSquare_alpha, orientedSquare_beta, phi,
      Six.radius_sq] using h
  have hm := hi
  rw [cardinal_margin_local _ (matchingCardinal_isCardinal i)] at hm
  change 0 ≤ centerX z (P.radial i) (P.transverse i) - angularWidth z -
    cardinalDepth P.center (matchingCardinal i) at hm
  dsimp [centerX, angularWidth] at hm
  rw [abs_of_nonneg hc0] at hm
  have hbs : -(P.transverse i * Real.sin z) ≤ |P.transverse i| * |Real.sin z| := by
    simpa only [abs_mul] using neg_le_abs (P.transverse i * Real.sin z)
  have hcap : cardinalDepth P.center (matchingCardinal i) +
      (Real.cos |z| + Real.sin |z|) / 2 ≤
      |P.radial i| * Real.cos |z| + |P.transverse i| * Real.sin |z| := by
    rw [Real.cos_abs, sin_abs_angle (by linarith [Real.pi_gt_d2] : |z| ≤ Real.pi),
      abs_of_nonneg (show 0 ≤ P.radial i by linarith [(P.contained i).half_le])]
    linarith
  exact ⟨candidate_cap_tilt_weak (abs_nonneg z) ht.le hbox hcap,
    fun hpos => candidate_cap_tilt_strict hpos ht.le hbox hcap⟩

private lemma opposite_budget_at_candidate {x e w : ℝ}
    (hE : 1 / 2 + x ≤ rhoStar - 1 / 2 - |e| / 2 ∧
      (0 < |e| → 1 / 2 + x < rhoStar - 1 / 2 - |e| / 2))
    (hW : 1 / 2 - x ≤ rhoStar - 1 / 2 - |w| / 2 ∧
      (0 < |w| → 1 / 2 - x < rhoStar - 1 / 2 - |w| / 2)) :
    |e| + |w| < 4 * cStar := by
  by_cases he : e = 0
  · by_cases hw : w = 0
    · rw [he, hw, abs_zero, zero_add]
      exact mul_pos (by norm_num) cStar_pos
    · have hs := hW.2 (abs_pos.mpr hw)
      dsimp [cStar]
      linarith [hE.1]
  · have hs := hE.2 (abs_pos.mpr he)
    dsimp [cStar]
    linarith [hW.1]

/-- Candidate-radius N26 for E/W, retaining BOTH cardinal hypotheses. -/
theorem PinPacking.east_west_budget_candidate {R : ℝ} (P : PinPacking R)
    (hR : R ^ 2 ≤ Six.qStar)
    (hE : 0 ≤ centralMargin .east (P.phase 0) (P.radial 0) (P.transverse 0) P.center.1 P.center.2)
    (hW : 0 ≤ centralMargin .west (P.phase 2) (P.radial 2) (P.transverse 2) P.center.1 P.center.2) :
    |P.phase 0| + |P.phase 2 - Real.pi| < 4 * cStar := by
  have he := P.cardinal_tilt_at_candidate hR 0 hE
  have hw := P.cardinal_tilt_at_candidate hR 2 hW
  simp only [matchingCardinal, cardinalCenter, cardinalDepth, sub_zero] at he hw
  exact opposite_budget_at_candidate he hw

/-- Candidate-radius N26 for N/S, retaining BOTH cardinal hypotheses. -/
theorem PinPacking.north_south_budget_candidate {R : ℝ} (P : PinPacking R)
    (hR : R ^ 2 ≤ Six.qStar)
    (hN : 0 ≤ centralMargin .north (P.phase 1) (P.radial 1) (P.transverse 1) P.center.1 P.center.2)
    (hS : 0 ≤ centralMargin .south (P.phase 4) (P.radial 4) (P.transverse 4) P.center.1 P.center.2) :
    |P.phase 1 - Real.pi / 2| + |P.phase 4 - 3 * Real.pi / 2| < 4 * cStar := by
  have hn := P.cardinal_tilt_at_candidate hR 1 hN
  have hs := P.cardinal_tilt_at_candidate hR 4 hS
  simp only [matchingCardinal, cardinalCenter, cardinalDepth] at hn hs
  exact opposite_budget_at_candidate hn hs

end SquaresInCircles.Six.Stress
