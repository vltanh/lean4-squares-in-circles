import SquaresInCircles.Six.Analytic.RadialSecondarySupport
import SquaresInCircles.Six.Analytic.SecondaryCostFolded

/-!
# Depth reserves for the two mixed double-D-secondary cases

The OWN-W/cardinal-S case has a direct fourth-degree Taylor reserve on the
whole interval. The cardinal-W/OWN-S case minimizes the helper potential at
d or the original endpoint 2/3. Its first piece is concave; its second piece
is monotone. Only d=1/2 and d=2/3 require explicit endpoint fractions.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def southMixedDepth (d : ℝ) : ℝ :=
  (Real.cos d+Real.sin d)/2-(1113/1000)*southRadialLength d-(13/20)*d

def westMixedConstant : ℝ := 5/2-113/1000-91/125-(13/40)*Real.pi

def westMixedBase (d : ℝ) : ℝ :=
  westMixedConstant+(887/1000)*Real.cos d+(1113/1000)*Real.sin d-
    (1113/1000)*westRadialLength d

def westMixedDepth (d : ℝ) : ℝ :=
  (Real.cos d+Real.sin d)/2-(1113/1000)*westRadialLength d+(13/20)*d

lemma south_mixed_depth_lower {d : ℝ} (hd : 1/2≤d ∧ d≤Real.pi/4) :
    -(19/10)< southMixedDepth d := by
  have hd0 : 0≤d := by linarith [hd.1]
  have hd1 : d≤4/5 := by linarith [hd.2,Real.pi_lt_d2]
  have hc := Real.one_sub_sq_div_two_le_cos (x := d)
  have hs := Real.sin_ge_sub_cube hd0
  have hu := Seven.cos_upper_four (x := d/2) (by linarith)
  have hsq := mul_nonneg (sub_nonneg.mpr hd1) (show 0≤4/5+d by linarith)
  have hd2 : d^2≤16/25 := by nlinarith
  have hcube := mul_le_mul hd1 hd2 (sq_nonneg d) (by norm_num : (0:ℝ)≤4/5)
  have hfour := mul_nonneg (sub_nonneg.mpr hd2) (show 0≤16/25+d^2 by positivity)
  have hd3 : d^3≤64/125 := by nlinarith only [hcube]
  have hd4 : d^4≤256/625 := by nlinarith only [hfour]
  have hpoly : -(19/10)< -863/500-(3/20)*d+(113/4000)*d^2-d^3/12-(371/64000)*d^4 := by
    nlinarith [sq_nonneg d]
  dsimp [southMixedDepth,southRadialLength]
  nlinarith only [hc,hs,hu,hpoly]

private lemma west_mixed_base_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (2/3)) westMixedBase := by
  let f' : ℝ→ℝ := fun d => -(887/1000)*Real.sin d+(1113/1000)*Real.cos d-
    (1113/1000)*Real.sin (Real.pi/4-d/2)
  let f'' : ℝ→ℝ := fun d => -(887/1000)*Real.cos d-(1113/1000)*Real.sin d+
    (1113/2000)*Real.cos (Real.pi/4-d/2)
  have hu (d : ℝ) : HasDerivAt (fun x : ℝ => Real.pi/4-x/2) (-1/2) d :=
    (((hasDerivAt_id' d).div_const 2).const_sub (Real.pi/4)).congr_deriv (by norm_num)
  have hf (d : ℝ) : HasDerivAt westMixedBase (f' d) d := by
    convert ((((Real.hasDerivAt_cos d).const_mul (887/1000)).const_add westMixedConstant).fun_add
      ((Real.hasDerivAt_sin d).const_mul (1113/1000))).fun_sub
      (((Real.hasDerivAt_cos (Real.pi/4-d/2)).comp d (hu d)).const_mul (1113/500))
      using 1
    · funext y; dsimp [westMixedBase,westRadialLength]; ring
    · dsimp [f']; ring
  have hff (d : ℝ) : HasDerivAt f' (f'' d) d := by
    convert (((Real.hasDerivAt_sin d).const_mul (-(887/1000))).fun_add
      ((Real.hasDerivAt_cos d).const_mul (1113/1000))).fun_sub
      (((Real.hasDerivAt_sin (Real.pi/4-d/2)).comp d (hu d)).const_mul (1113/1000))
      using 1
    · funext y; dsimp [f']
    · dsimp [f'']; ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (2/3))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro d _; exact (hf d).hasDerivWithinAt
  · intro d _; exact (hff d).hasDerivWithinAt
  · intro d hd
    have hdc : d∈Set.Icc (1/2) (2/3) := interior_subset hd
    have hc := (helper_trig_bounds
      (abs_le.mpr ⟨by linarith [hdc.1],hdc.2⟩ : |d|≤2/3)).1
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := d)
      (by linarith [hdc.1]) (by linarith [hdc.2,Real.pi_gt_d2])
    dsimp [f'']
    linarith [Real.cos_le_one (Real.pi/4-d/2)]

private lemma west_cos_half_endpoint : Real.cos (Real.pi/4-1/4)≤861/1000 := by
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤107/200)
    (show Real.pi/4-1/4≤Real.pi by linarith [Real.pi_pos])
    (show (107:ℝ)/200≤Real.pi/4-1/4 by linarith [Real.pi_gt_d2])
  have hp := Seven.cos_upper_four (x := (107:ℝ)/200) (by norm_num)
  norm_num at hp
  linarith

private lemma west_cos_boundary_endpoint : Real.cos (Real.pi/4-1/3)≤9/10 := by
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤271/600)
    (show Real.pi/4-1/3≤Real.pi by linarith [Real.pi_pos])
    (show (271:ℝ)/600≤Real.pi/4-1/3 by linarith [Real.pi_gt_d2])
  have hp := Seven.cos_upper_four (x := (271:ℝ)/600) (by norm_num)
  norm_num at hp
  linarith

lemma west_mixed_base_half_positive : 0<westMixedBase (1/2) := by
  have he := west_cos_half_endpoint
  have hc := low_half_bracket.1
  have hs := low_half_bracket.2.2.1
  dsimp [westMixedBase,westMixedConstant,westRadialLength]
  norm_num
  linarith [Real.pi_lt_d2]

lemma west_mixed_base_boundary_positive : 0<westMixedBase (2/3) := by
  have he := west_cos_boundary_endpoint
  have hc := two_thirds_endpoint_bracket.1
  have hs := two_thirds_endpoint_bracket.2.2.1
  dsimp [westMixedBase,westMixedConstant,westRadialLength]
  norm_num
  linarith [Real.pi_lt_d2]

lemma west_mixed_base_positive {d : ℝ} (hd : 1/2≤d ∧ d≤2/3) :
    0<westMixedBase d :=
  positive_on_concave_interval west_mixed_base_concave hd
    west_mixed_base_half_positive west_mixed_base_boundary_positive

lemma west_mixed_depth_monotone :
    MonotoneOn westMixedDepth (Set.Icc (2/3) (Real.pi/4)) := by
  let f' : ℝ→ℝ := fun d => (Real.cos d-Real.sin d)/2-
    (1113/1000)*Real.sin (Real.pi/4-d/2)+13/20
  have hu (d : ℝ) : HasDerivAt (fun x : ℝ => Real.pi/4-x/2) (-1/2) d :=
    (((hasDerivAt_id' d).div_const 2).const_sub (Real.pi/4)).congr_deriv (by norm_num)
  have hD (d : ℝ) : HasDerivAt westMixedDepth (f' d) d := by
    convert ((((Real.hasDerivAt_cos d).fun_add (Real.hasDerivAt_sin d)).div_const 2).fun_sub
      (((Real.hasDerivAt_cos (Real.pi/4-d/2)).comp d (hu d)).const_mul (1113/500))).fun_add
      ((hasDerivAt_id d).const_mul (13/20)) using 1
    · funext y; dsimp [westMixedDepth,westRadialLength]; ring
    · dsimp [f']; ring
  apply Seven.monoOn_of_hasDeriv_nonneg (d := f')
    (fun x _ => (hD x).continuousAt.continuousWithinAt)
  · intro d _
    exact hD d
  · intro d hd
    have hc := (east_quadrant_trig (by linarith [hd.1]) hd.2.le).2.2
    have hu0 : 0≤Real.pi/4-d/2 := by linarith [hd.2,Real.pi_pos]
    have hs := Real.sin_le hu0
    have hu1 : Real.pi/4-d/2≤1/2 := by linarith [hd.1,Real.pi_lt_d2]
    dsimp [f']
    linarith

/-- The mixed cardinal-W/OWN-S bound after minimizing in the actual S range. -/
theorem west_cardinal_own_south_reserve {s d : ℝ}
    (hs : -5/8≤ s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    0<westMixedConstant+(Real.cos d+Real.sin d)/2-
      (1113/1000)*westRadialLength d+ownWingPotential s+(13/20)*|s-d| := by
  by_cases hsmall : d≤2/3
  · have hwing := own_wing_penalty_lower hs ⟨by linarith [hd.1],hd.2⟩
    have hp := west_mixed_base_positive ⟨hd.1,hsmall⟩
    dsimp [westMixedBase,positiveWing] at hp hwing
    linarith
  · have hwing := own_wing_penalty_endpoint hs (le_of_not_ge hsmall)
    have hdepth := west_mixed_depth_monotone
      (show (2:ℝ)/3∈Set.Icc (2/3) (Real.pi/4) by
        constructor <;> linarith [Real.pi_gt_d2])
      ⟨le_of_not_ge hsmall,hd.2⟩ (le_of_not_ge hsmall)
    have hp := west_mixed_base_boundary_positive
    dsimp [westMixedBase,positiveWing,westMixedDepth] at hp hwing hdepth
    linarith

end SquaresInCircles.Six.Analytic
