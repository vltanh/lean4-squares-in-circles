import SquaresInCircles.Six.Analytic.SmallDiagonalOwnStress

/-!
# Four endpoint inequalities for one frozen stress

These are the four vertices of [0,2/3] x [0,1/2], with the same multipliers
(3/2,2,1). Three vertices use the universal far-vertex support. The remaining
vertex uses a separately proved primary-cap slope condition. The explicit
rational lower reserves are respectively
  14131933/400000000,
  5447215319/96000000000,
  310413977071/39366000000000,
  2199927262319/163296000000000.
The polynomial and root comparisons below are ordinary Lean arithmetic, not
an interval search or an externally supplied success flag.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private lemma own_vertex_origin_positive :
    0<ownSmallDVertexMinorant 0 0 (90139/50000) := by
  norm_num [ownSmallDVertexMinorant,ownSmallDThreshold,ownSmallDCentralX,ownSmallDCentralY]

private lemma own_vertex_top_positive :
    0<ownSmallDVertexMinorant 0 (1/2) (8661/4000) := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤1/2) (by linarith [Real.pi_gt_d2] : (1:ℝ)/2≤Real.pi)
  have hy : 0≤ownSmallDCentralY 0 (1/2) := by
    dsimp [ownSmallDCentralY]
    simp only [Real.sin_zero,mul_zero,sub_zero]
    linarith
  have hs := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  have hc := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  rw [ownSmallDVertexMinorant,max_eq_left hy]
  norm_num [ownSmallDThreshold,ownSmallDCentralX,ownSmallDCentralY]
  nlinarith only [hs,hc]

private lemma own_vertex_far_bottom_positive :
    0<ownSmallDVertexMinorant (2/3) 0 (112973/50000) := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤2/3) (by linarith [Real.pi_gt_d2] : (2:ℝ)/3≤Real.pi)
  have hy : ownSmallDCentralY (2/3) 0≤0 := by
    dsimp [ownSmallDCentralY]
    simp only [Real.sin_zero,mul_zero,zero_sub]
    linarith
  have hs := Seven.sin_lower_seven (x := (2:ℝ)/3) (by norm_num)
  have hc := Seven.cos_lower_six (x := (2:ℝ)/3) (by norm_num)
  rw [ownSmallDVertexMinorant,max_eq_right hy]
  norm_num [ownSmallDThreshold,ownSmallDCentralX,ownSmallDCentralY]
  nlinarith only [hs,hc]

private lemma own_cap_far_top_positive : 0<ownSmallDCapMinorant (2/3) (1/2) := by
  have hsvL := Seven.sin_lower_seven (x := (2:ℝ)/3) (by norm_num)
  have hsvU := Seven.sin_upper_five (x := (2:ℝ)/3) (by norm_num)
  have hcvL := Seven.cos_lower_six (x := (2:ℝ)/3) (by norm_num)
  have hsdL := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  have hcdL := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hsqU := Seven.sin_upper_five (x := (7:ℝ)/6) (by norm_num)
  have hcqL := Seven.cos_lower_six (x := (7:ℝ)/6) (by norm_num)
  have hy : 0≤ownSmallDCentralY (2/3) (1/2) := by
    dsimp [ownSmallDCentralY]
    nlinarith only [hsdL,hsvU]
  rw [ownSmallDCapMinorant,max_eq_left hy]
  norm_num [ownSmallDThreshold,ownSmallDCentralX,ownSmallDCentralY]
  nlinarith only [hsvL,hcvL,hsdL,hcdL,hsqU,hcqL]

private lemma own_top_root :
    (3/2+Real.sin ((1:ℝ)/2))^2+(Real.cos ((1:ℝ)/2))^2≤(8661/4000)^2 := by
  have h := Seven.sin_upper_five (x := (1:ℝ)/2) (by norm_num)
  nlinarith only [h,Real.sin_sq_add_cos_sq ((1:ℝ)/2)]

private lemma own_far_root :
    (3/2+Real.sin ((2:ℝ)/3))^2+(Real.cos ((2:ℝ)/3))^2≤(112973/50000)^2 := by
  have h := Seven.sin_upper_five (x := (2:ℝ)/3) (by norm_num)
  nlinarith only [h,Real.sin_sq_add_cos_sq ((2:ℝ)/3)]

private lemma own_far_cap_slope :
    2*(rho0+1/2)*Real.cos ((7:ℝ)/6)≤3/2+Real.sin ((7:ℝ)/6) := by
  have ht := small_secondary_trig (q := (7:ℝ)/6) (by constructor <;> norm_num)
  have hcos := Seven.cos_upper_four (x := (7:ℝ)/6) (by norm_num)
  have hc : Real.cos ((7:ℝ)/6)≤2/5 := by nlinarith only [hcos]
  have hp := mul_le_mul (show rho0+1/2≤1613/1000 by linarith [rho0_upper]) hc ht.1
    (by norm_num : (0:ℝ)≤1613/1000)
  nlinarith only [hp,ht.2.1]

/-- The same fixed centers are admissible for the four support comparisons:
containment depends on their local coordinates, not the trial angles. -/
theorem ownSmallD_endpoints {aw bw ad bd cx cy : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0)) :
    0<ownSmallDStress aw bw ad bd cx cy 0 0 ∧
      0<ownSmallDStress aw bw ad bd cx cy 0 (1/2) ∧
      0<ownSmallDStress aw bw ad bd cx cy (2/3) 0 ∧
      0<ownSmallDStress aw bw ad bd cx cy (2/3) (1/2) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact own_vertex_origin_positive.trans_le
      (ownSmallD_above_vertex hW hD hC (by constructor <;> norm_num)
        (by constructor <;> norm_num) (by norm_num) (by norm_num))
  · exact own_vertex_top_positive.trans_le
      (ownSmallD_above_vertex hW hD hC (by constructor <;> norm_num)
        (by constructor <;> norm_num) (by norm_num)
        (by simpa only [zero_add] using own_top_root))
  · exact own_vertex_far_bottom_positive.trans_le
      (ownSmallD_above_vertex hW hD hC (by constructor <;> norm_num)
        (by constructor <;> norm_num) (by norm_num)
        (by simpa only [add_zero] using own_far_root))
  · exact own_cap_far_top_positive.trans_le
      (ownSmallD_above_cap hW hD hC (by constructor <;> norm_num)
        (by constructor <;> norm_num) (by norm_num; exact own_far_cap_slope))

/-- Full rectangle positivity follows by two concavity steps, not subdivision. -/
theorem ownSmallD_positive {aw bw ad bd cx cy v d : ℝ}
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hb : |bw|≤1/2) (hC : (0≤cx ∧ cx≤c0) ∧ (0≤cy ∧ cy≤c0))
    (hv : 0≤v ∧ v≤2/3) (hd : 0≤d ∧ d≤1/2) :
    0<ownSmallDStress aw bw ad bd cx cy v d := by
  have he := ownSmallD_endpoints hW hD hC
  exact positive_on_separately_concave_rectangle hv hd
    (fun y hy => ownSmallD_concave_v hW hb hC hy)
    (ownSmallD_concave_d hW hb hC (by constructor <;> norm_num))
    (ownSmallD_concave_d hW hb hC (by constructor <;> norm_num))
    he.1 he.2.1 he.2.2.1 he.2.2.2

end SquaresInCircles.Six.Analytic
