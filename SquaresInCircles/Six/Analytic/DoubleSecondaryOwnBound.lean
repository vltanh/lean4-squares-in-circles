module
public import SquaresInCircles.Six.Analytic.SecondaryCostBound
public import SquaresInCircles.Six.Analytic.HighDiagonalProfile

@[expose] public section

/-!
# Whole-domain double-D-secondary exclusion with OWN W and S

Use equal multipliers on C-W, C-S, W-D and D-S and zero multiplier on C-D.
The two D-secondary forces cancel exactly, so no D support is needed. The
remaining two exterior costs obey SecondaryCostBound. Their affine q terms
sum using qW+qS=pi/2+v+s and eliminate d altogether.

The central support is counted once. Its two components are nonnegative on
the original helper ranges, and its cost gives coefficients 387/1000 and
613/1000. A one-variable concavity bound and the sign s=0 finish the argument.
There is no 53-cell subdivision or generated stress table in this proof.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def ownWingCost (x : ℝ) : ℝ :=
  (387/1000)*Real.cos x+(613/1000)*Real.sin x-(13/20)*x

lemma ownWingCost_lower {x : ℝ} (hx : 0≤x ∧ x≤2/3) : 249/1000<ownWingCost x := by
  have ht := positive_trig_affine_concave
    (A := (387:ℝ)/1000) (B := (613:ℝ)/1000)
    (l := 0) (u := (2:ℝ)/3) (a := 1) (b := 0) (by norm_num) (by norm_num)
    (by intro t ht; constructor <;> linarith [ht.1,ht.2,Real.pi_gt_d2])
  have hl : ConcaveOn ℝ (Set.Icc 0 (2/3)) (fun t : ℝ => -(13/20)*t-249/1000) := by
    refine ⟨convex_Icc _ _,?_⟩
    intro p hp q hq a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith only [hab]
  have hconc := ht.add hl
  have hz : 0<(387/1000)*Real.cos 0+(613/1000)*Real.sin 0+(-(13/20)*0-249/1000) := by
    norm_num
  have he : 0<(387/1000)*Real.cos (2/3)+(613/1000)*Real.sin (2/3)+
      (-(13/20)*(2/3)-249/1000) := by
    linarith [two_thirds_endpoint_bracket.1,two_thirds_endpoint_bracket.2.2.1]
  have h := positive_on_concave_interval hconc hx hz he
  dsimp [ownWingCost]
  linarith

lemma helper_trig_bounds {x : ℝ} (hx : |x|≤2/3) :
    7/9≤Real.cos x ∧ |Real.sin x|≤2/3 := by
  have hsq := pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [sq_abs] at hsq
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hs := Real.sin_le (abs_nonneg x)
  rw [sin_abs_angle (hx.trans (by linarith [Real.pi_gt_d2] : (2:ℝ)/3≤Real.pi))] at hs
  exact ⟨by norm_num at hsq; linarith,hs.trans hx⟩

def doubleOwnSecondaryGap (v s d aw bw aS bS cx cy : ℝ) : ℝ :=
  2+angularWidth v+angularWidth s+angularWidth (d+v)+angularWidth (Real.pi/2+s-d)-
    ((1+Real.sin (d+v))*aw-Real.cos (d+v)*bw)-
    ((1+Real.sin (Real.pi/2+s-d))*aS+Real.cos (Real.pi/2+s-d)*bS)-
    ((Real.cos v-Real.sin s)*cx+(Real.cos s-Real.sin v)*cy)

/-- Strict positivity over the entire original OWN helper ranges. The
additional qS>=1/2 fact is proved geometrically from high D at the call site. -/
theorem double_own_secondary_gap_positive {v s d aw bw aS bS cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hs : -5/8≤s ∧ s≤2/3)
    (hd : 1/2≤d ∧ d≤Real.pi/4) (hqs : 1/2≤Real.pi/2+s-d)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleOwnSecondaryGap v s d aw bw aS bS cx cy := by
  have hW' : ContainedChart aw |-bw| := by simpa only [abs_neg] using hW
  have hqW : 1/2≤d+v ∧ d+v≤Real.pi-1/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hqS : 1/2≤Real.pi/2+s-d ∧ Real.pi/2+s-d≤Real.pi-1/2 := by
    exact ⟨hqs,by linarith [hs.2,hd.1,Real.pi_gt_d2]⟩
  have hcostW := secondary_cost_affine_lower hW' hqW
  have hcostS := secondary_cost_affine_lower hS hqS
  have hvabs : |v|≤2/3 := by simpa only [abs_of_nonneg hv.1] using hv.2
  have hsabs : |s|≤2/3 := abs_le.mpr ⟨by linarith [hs.1],hs.2⟩
  have htv := helper_trig_bounds hvabs
  have hts := helper_trig_bounds hsabs
  have hcosv : 0≤Real.cos v := by linarith [htv.1]
  have hcoss : 0≤Real.cos s := by linarith [hts.1]
  have hsinv := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hX : 0≤Real.cos v-Real.sin s := by linarith [(abs_le.mp hts.2).2,htv.1]
  have hY : 0≤Real.cos s-Real.sin v := by linarith [(abs_le.mp htv.2).2,hts.1]
  have hcentral := coarse_central_work hc hX hY le_rfl le_rfl
  have hvline := ownWingCost_lower hv
  by_cases hs0 : 0≤s
  · have hsins := Real.sin_nonneg_of_nonneg_of_le_pi hs0
      (by linarith [hs.2,Real.pi_gt_d2])
    have hsline := ownWingCost_lower ⟨hs0,hs.2⟩
    have hconstant : 0<2-182/125-(13/40)*Real.pi+2*(249/1000) := by
      linarith [Real.pi_lt_d2]
    dsimp [doubleOwnSecondaryGap]
    rw [show angularWidth v=(Real.cos v+Real.sin v)/2 by
      rw [angularWidth,abs_of_nonneg hcosv,abs_of_nonneg hsinv],
      show angularWidth s=(Real.cos s+Real.sin s)/2 by
      rw [angularWidth,abs_of_nonneg hcoss,abs_of_nonneg hsins]]
    dsimp [ownWingCost] at hvline hsline
    nlinarith only [hcostW,hcostS,hcentral,hvline,hsline,hconstant]
  · have hsneg : s<0 := lt_of_not_ge hs0
    have hsins : Real.sin s≤0 := by
      have h := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-s by linarith)
        (by linarith [hs.1,Real.pi_gt_d2])
      rw [Real.sin_neg] at h
      linarith
    have hsum := one_le_abs_cos_add_abs_sin s
    rw [abs_of_nonneg hcoss,abs_of_nonpos hsins] at hsum
    have hsline : 387/1000≤(387/1000)*(Real.cos s-Real.sin s)-(13/20)*s := by linarith
    have hconstant : 0<2-182/125-(13/40)*Real.pi+249/1000+387/1000 := by
      linarith [Real.pi_lt_d2]
    dsimp [doubleOwnSecondaryGap]
    rw [show angularWidth v=(Real.cos v+Real.sin v)/2 by
      rw [angularWidth,abs_of_nonneg hcosv,abs_of_nonneg hsinv],
      show angularWidth s=(Real.cos s-Real.sin s)/2 by
      rw [angularWidth,abs_of_nonneg hcoss,abs_of_nonpos hsins]; ring]
    dsimp [ownWingCost] at hvline
    nlinarith only [hcostW,hcostS,hcentral,hvline,hsline,hconstant]

end SquaresInCircles.Six.Analytic
