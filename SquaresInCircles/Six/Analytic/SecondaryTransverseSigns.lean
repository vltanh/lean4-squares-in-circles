module
public import SquaresInCircles.Six.Analytic.SecondaryPhaseRestrictions

@[expose] public section

/-!
# Signed transverse obstructions near a quarter-turn

For q in [pi/4,pi/4+2/5], the universal far-vertex support forces a
D-sourced edge's signed D coordinate above 113/1000. The width estimate is
sqrt(2) cos(q-pi/4), bounded by explicit rational Taylor inequalities.

A D transverse coordinate at least c0 prevents a small-gap S-wing separator;
a coordinate at most -c0 prevents a small-gap W-wing separator. These are
necessary restrictions, not a claim to have excluded the full mixed regions.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma quarter_band_width_lower {q : ℝ}
    (hq : Real.pi/4 ≤ q ∧ q ≤ Real.pi/4+2/5) :
    (651147:ℝ)/500000 ≤ Real.sin q+Real.cos q := by
  have hx0 : 0 ≤ q-Real.pi/4 := by linarith [hq.1]
  have hx1 : q-Real.pi/4 ≤ 2/5 := by linarith [hq.2]
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi hx0
    (show (2:ℝ)/5 ≤ Real.pi by linarith [Real.pi_gt_d2]) hx1
  have ht := Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)
  have hcos : 921/1000 ≤ Real.cos (q-Real.pi/4) := by nlinarith only [hm,ht]
  have hsqrt : (707:ℝ)/500 ≤ Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hp := mul_le_mul hsqrt hcos (by norm_num : (0:ℝ) ≤ 921/1000)
    (Real.sqrt_nonneg (2:ℝ))
  have hidentity : Real.sqrt 2*Real.cos (q-Real.pi/4)=Real.sin q+Real.cos q := by
    rw [Real.cos_sub,Real.cos_pi_div_four,Real.sin_pi_div_four]
    have hc := congrArg (fun z : ℝ => z*Real.cos q)
      (Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num))
    have hs := congrArg (fun z : ℝ => z*Real.sin q)
      (Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num))
    nlinarith only [hc,hs]
  rw [hidentity] at hp
  norm_num at hp ⊢
  exact hp

/-- Universal far-vertex support, not a guessed cap branch, forces this sign. -/
lemma secondary_forces_transverse_positive {a b z q : ℝ}
    (hc : ContainedChart a |b|)
    (hq : Real.pi/4 ≤ q ∧ q ≤ Real.pi/4+2/5)
    (hsep : 1/2+angularWidth q ≤ a*Real.sin q-b*Real.cos q+z) :
    113/1000 < z := by
  have hq0 : 0 ≤ q := by linarith [hq.1,Real.pi_pos]
  have hqhalf : q ≤ Real.pi/2 := by linarith [hq.2,Real.pi_gt_d2]
  have hcos : 0 ≤ Real.cos q := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],hqhalf⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hq0
    (by linarith [hqhalf,Real.pi_pos])
  have hbox : (a+1/2)^2+(|-b|+1/2)^2 ≤ Q0 := by
    simpa only [abs_neg] using hc.containment
  have hu := circle_support_unconstrained hbox hcos (Real.sin_sq_add_cos_sq q)
  rw [angularWidth,abs_of_nonneg hcos,abs_of_nonneg hsin] at hsep
  have hw := quarter_band_width_lower hq
  nlinarith [R0_lt_1689_1000]

/-- A cardinal W has a small enough total W/D gap for the sign bound above. -/
theorem cardinal_W_Dsecondary_positive_transverse {R : ℝ} (P : NormalizedPacking R)
    (hcard : P.ownBits 2=false)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    113/1000 < P.transverse 3 := by
  have hlow := (DW_Dsecondary_gap_gt_quarter P hsep).le
  have hw := (abs_lt.mp (P.cardinal_angle 2 hcard)).1
  have hWphase := P.phase_from_deviation 2
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hupper : P.phase 3-P.phase 2 ≤ Real.pi/4+2/5 := by
    rw [hWphase,hDphase]
    linarith [P.diagonal_angle_range.2]
  change Seven.SAT.threshold (P.square 2) (P.square 3) ≤
    frameY (P.square 3) (sub (P.square 3).center (P.square 2).center) at hsep
  rw [P.square_def 2,P.square_def 3,oriented_pair_threshold,pair_frameY_right] at hsep
  apply secondary_forces_transverse_positive (P.contained 2) ⟨hlow,hupper⟩
  linarith

lemma wing_secondary_small_gap_excluded {a b z q : ℝ}
    (ha : a ≤ rho0) (hb : b < 1/2) (hz : c0 ≤ z)
    (hq : 0 ≤ q ∧ q ≤ Real.pi/4) :
    b+a*Real.sin q-z*Real.cos q < 1/2+angularWidth q := by
  have ht := east_quadrant_trig hq.1 hq.2
  have hcos : 0 ≤ Real.cos q := by linarith [ht.1]
  have hsin := ht.2.1
  have horder : a-1/2 ≤ z+1/2 := by dsimp [c0] at hz; linarith
  have h1 := mul_nonneg (sub_nonneg.mpr horder) hsin
  have h2 := mul_nonneg (show 0 ≤ z+1/2 by linarith [c0_pos])
    (sub_nonneg.mpr ht.2.2)
  rw [angularWidth,abs_of_nonneg hcos,abs_of_nonneg hsin]
  nlinarith only [h1,h2,hb]

/-- Positive D transverse displacement forces the S-side gap past pi/4,
regardless of which of its two secondary sources was selected. -/
theorem positive_Dtransverse_south_gap {R : ℝ} (P : NormalizedPacking R)
    (hz : c0 ≤ P.transverse 3) : Real.pi/4 < P.phase 4-P.phase 3 := by
  by_contra! hsmall
  rcases south_secondary_choice P with hD | hS
  · linarith [DS_Dsecondary_gap_gt_quarter P hD]
  · have hq : 0 ≤ P.phase 4-P.phase 3 ∧ P.phase 4-P.phase 3 ≤ Real.pi/4 :=
      ⟨sub_nonneg.mpr P.primary_order.2.2.2.1.le,hsmall⟩
    have hb : P.transverse 4 < 1/2 :=
      (le_abs_self _).trans_lt ((P.contained 4).u_lt_half (P.avoidsCore 4))
    have hbound := wing_secondary_small_gap_excluded (P.contained 3).a_le_rho0 hb hz hq
    change Seven.SAT.threshold (P.square 3) (P.square 4) ≤
      frameY (P.square 4) (sub (P.square 4).center (P.square 3).center) at hS
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,pair_frameY_right] at hS
    linarith

/-- Thus a remaining cardinal-W noncandidate edge lies on BOTH strict sides
of the geometric phase wall. This is not a proof that the region is empty. -/
theorem cardinal_W_non_candidate_phase_wedge {R : ℝ} (P : NormalizedPacking R)
    (hcard : P.ownBits 2=false)
    (hsep : Seven.SAT.threshold (P.square 2) (P.square 3) ≤
      dot (normalY (P.square 3)) (sub (P.square 3).center (P.square 2).center)) :
    P.helperAngle 2 < P.diagonalAngle-Real.pi/4 ∧
      P.diagonalAngle-Real.pi/4 < P.helperAngle 4 := by
  refine ⟨DW_Dsecondary_west_of_wall P hsep,?_⟩
  have hb := cardinal_W_Dsecondary_positive_transverse P hcard hsep
  have hz : c0 ≤ P.transverse 3 := by dsimp [c0]; linarith [rho0_upper]
  have hgap := positive_Dtransverse_south_gap P hz
  have hSphase := P.phase_from_deviation 4
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [hSphase,hDphase] at hgap
  linarith

end SquaresInCircles.Six.Analytic
