module

public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars

/-!
# Eight squares: the strengthened original endpoint charge

The new coefficient is 41/40 and the strict reserve
is 27/160000. The signed rotation estimate retains a 13/280 reserve.
For the short positive remainder, two proved support choices overlap:
one fixed weight controls the neighborhood of zero and the previous
optimized weight gains the exact coefficient difference. Their overlap
is proved algebraically without a sampled angle partition.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.StrongerEndpointScalars
open EndpointBudgetScalars PositiveAngularEnvelope

def charge : ℝ := 41/40
def epsilon : ℝ := 27/160000
def defect (l d : ℝ) : ℝ := EndpointRotationPenalty.defect l d-
  (charge-EndpointRotationPenalty.charge)*d

theorem defect_upper {l d : ℝ} (hl : l∈Icc (4/5:ℝ) 2) (hd : |d|≤frameCap) :
    defect l d≤ -(13/280)*|d| := by
  have hh := EndpointRotationPenalty.defect_upper hl hd
  have hn := neg_le_abs d
  dsimp [defect,charge,EndpointRotationPenalty.charge]
  linarith

theorem rotated_baseline : baseline (7/6)+S0<2-epsilon := by
  have hN := fixed_norm_bounds.1
  have hS := radical_bounds.2.2.2
  dsimp [baseline,epsilon]
  linarith

theorem gain_linear {s : ℝ} (hs : s∈Icc 0 (1/2:ℝ)) :
    positiveGain s≤(26/25)*s := by
  have hsin := Real.sin_le hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 := mul_le_mul_of_nonneg_left hs.2 hs.1
  have hk := radical_bounds
  have hm := mul_le_mul_of_nonneg_left hsin (show 0≤k0 by linarith [hk.1])
  have hm' := mul_le_mul_of_nonneg_right hk.2.1.le hs.1
  dsimp [positiveGain]
  linarith [hs.1,hs.2]

theorem positive_short_choice {s : ℝ} (hs : s∈Icc 0 (1/2:ℝ)) :
    ∃ l∈Icc (4/5:ℝ) 2,baseline l+l*positiveGain s-charge*s+S0<2-epsilon := by
  by_cases hfixed : baseline (7/6)+(7/6)*positiveGain s-charge*s+S0<2-epsilon
  · exact ⟨7/6,by norm_num,hfixed⟩
  have hN := fixed_norm_bounds.1
  have hS := radical_bounds.2.2.2
  have hgain := gain_linear hs
  have hrough : baseline (7/6)+(7/6)*positiveGain s-charge*s+S0<
      2-1/500+(113/600)*s := by
    dsimp [baseline,charge]
    linarith
  have hopt := EndpointBudgetScalars.positive_short hs
  refine ⟨weight s,weight_bounds hs,?_⟩
  dsimp [charge,epsilon,EndpointRotationPenalty.charge,EndpointBudgetScalars.epsilon] at *
  have hfixed' := le_of_not_gt hfixed
  linarith

theorem positive_long {s : ℝ} (hs : s∈Icc (1/2:ℝ) frameCap) :
    baseline (4/5)+(4/5)*((41/40)*s)-charge*s+S0<2-epsilon := by
  have hN := fixed_norm_bounds.2.2
  have hS := radical_bounds.2.2.2
  dsimp [baseline,charge,epsilon]
  linarith [hs.1]

theorem negative_short {s : ℝ} (hs : s∈Icc 0 (6/25:ℝ)) :
    baseline (7/6)+(7/6)*negativeGain (183/200) s+charge*s+S0<2-epsilon := by
  have hN := fixed_norm_bounds.1
  have hS := radical_bounds.2.2.2
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 : s^2≤(6/25:ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hs3 := mul_le_mul_of_nonneg_right hs2 hs.1
  have hshort := mul_nonneg hs.1 (show 0≤6/25-s by linarith [hs.2])
  dsimp [baseline,negativeGain,K,charge,epsilon]
  linarith [hs.1,hs.2]

theorem negative_long {s : ℝ} (hs : s∈Icc (6/25:ℝ) frameCap) :
    baseline (7/4)+(7/4)*negativeGain (4/5) s+charge*s+S0<2-epsilon := by
  have hN := fixed_norm_bounds.2.1
  have hS := radical_bounds.2.2.2
  have hsinL := sin_lower_seven (show (0:ℝ)≤6/25 by norm_num)
  have hcosL := cos_lower_six (show (0:ℝ)≤6/25 by norm_num)
  have hsinH := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
  have hcosH := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
  norm_num [frameCap] at hsinL hcosL hsinH hcosH
  have htrig :
      2*(9971/2500:ℝ)-3*(7/4)-1+(7/4)*(4/5)+52/125-2+epsilon<
        -charge*s+((7/4)*K)*Real.sin s+((7/4)*(4/5))*Real.cos s := by
    apply trig_concave_gt (by norm_num [K]) (by norm_num) (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hs
    · dsimp [K,charge,epsilon]
      linarith
    · dsimp [K,charge,epsilon,frameCap]
      linarith
  dsimp [baseline,negativeGain]
  linarith

end SquaresInCircles.Eight.StrongerEndpointScalars
