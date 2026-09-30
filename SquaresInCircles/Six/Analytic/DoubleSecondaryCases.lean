module
public import SquaresInCircles.Six.Analytic.DoubleSecondaryStress

@[expose] public section

/-!
# The three remaining double-D-secondary central-bit combinations

Both cardinal helpers use one cosine-sum radial bound. OWN W/cardinal S uses
the affine secondary cost and a whole-interval polynomial depth reserve.
Cardinal W/OWN S keeps the folded secondary cost, whose helper minimum is
proved analytically at d or the actual endpoint 2/3. Together with the earlier
OWN/OWN theorem this covers all four central choices without any stress table.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma double_cardinal_secondary_gap_positive {w s d aw bw aS bS cx cy : ℝ}
    (hw : |w|≤2/5) (hs : |s|≤2/5) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap false false w s d aw bw aS bS cx cy := by
  have hWwork := west_cardinal_secondary_work (w := w) hW hd
  have hSwork := south_cardinal_secondary_work (s := s) hS hd
  have hWwidth := cardinal_width_triangle hw hd
  have hSwidth := cardinal_width_triangle hs hd
  have hlength := radial_length_sum_bound d
  have hwidth := high_diagonal_width_lower hd
  have hcenter : cx+cy≤226/1000 := by
    have hx := hc.1.2
    have hy := hc.2.2
    dsimp [c0] at hx hy
    linarith [rho0_upper]
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [south_relative_width]
  rw [high_diagonal_width d hd] at hWwidth hSwidth
  nlinarith only [hWwork,hSwork,hWwidth,hSwidth,hlength,hwidth,hcenter]

lemma double_ownW_cardinalS_gap_positive {v s d aw bw aS bS cx cy : ℝ}
    (hv : 0≤v ∧ v≤2/3) (hs : |s|≤2/5) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap true false (-v) s d aw bw aS bS cx cy := by
  have hW' : ContainedChart aw |-bw| := by simpa only [abs_neg] using hW
  have hq : 1/2≤d+v ∧ d+v≤Real.pi-1/2 := by
    constructor <;> linarith [hv.1,hv.2,hd.1,hd.2,Real.pi_gt_d2]
  have hWcost := secondary_cost_affine_lower hW' hq
  have hSwork := south_cardinal_secondary_work (s := s) hS hd
  have hSwidth := cardinal_width_triangle hs hd
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show v∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hv.1
    (by linarith [hv.2,Real.pi_gt_d2])
  have hcentral := coarse_central_work hc hcos
    (show 0≤1-Real.sin v by linarith [Real.sin_le_one v]) le_rfl le_rfl
  have hwing := ownWingCost_lower hv
  have hdepth := south_mixed_depth_lower hd
  have hvwidth : angularWidth (-v)=(Real.cos v+Real.sin v)/2 := by
    simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin]
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [Real.cos_neg,Real.sin_neg,sub_neg_eq_add,hvwidth,south_relative_width]
  rw [high_diagonal_width d hd] at hSwidth
  dsimp [ownWingCost,southMixedDepth] at hwing hdepth
  nlinarith only [hWcost,hSwork,hSwidth,hcentral,hwing,hdepth]

lemma double_cardinalW_ownS_gap_positive {w s d aw bw aS bS cx cy : ℝ}
    (hw : |w|≤2/5) (hs : -5/8≤s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤Real.pi/4)
    (hqs : 1/2≤Real.pi/2+s-d)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart aS |bS|)
    (hc : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<doubleSecondaryGap false true w s d aw bw aS bS cx cy := by
  have hq : 1/2≤Real.pi/2+s-d ∧ Real.pi/2+s-d≤Real.pi-1/2 :=
    ⟨hqs,by linarith [hs.2,hd.1,Real.pi_gt_d2]⟩
  have hScost := secondary_cost_folded_lower hS hq
  have he : foldedSecondaryAngle (Real.pi/2+s-d)=Real.pi/2-|s-d| := by
    dsimp [foldedSecondaryAngle]
    congr 2
    ring
  rw [he] at hScost
  have hWwork := west_cardinal_secondary_work (w := w) hW hd
  have hWwidth := cardinal_width_triangle hw hd
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show s∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have hcentral := coarse_central_work hc
    (show 0≤1-Real.sin s by linarith [Real.sin_le_one s]) hcos le_rfl le_rfl
  have hreserve := west_cardinal_own_south_reserve hs hd
  have hswidth : angularWidth s=(Real.cos s+|Real.sin s|)/2 := by
    rw [angularWidth,abs_of_nonneg hcos]
  rw [high_diagonal_width d hd] at hWwidth
  dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  rw [hswidth]
  dsimp [westMixedConstant,ownWingPotential] at hreserve
  nlinarith only [hScost,hWwork,hWwidth,hcentral,hreserve]

end SquaresInCircles.Six.Analytic
