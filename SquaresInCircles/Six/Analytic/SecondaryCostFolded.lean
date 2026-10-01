import SquaresInCircles.Six.Analytic.SecondaryCostBound
import SquaresInCircles.Six.Analytic.DoubleSecondaryOwnBound

/-!
# The folded cost and the penalty of an own wing

With the folded angle `π/2 - |q - π/2|` in place of `q`, the bound of
`SecondaryCostBound` holds on all of `[1/2, π - 1/2]`: beyond `π/2` it is the
bound at `π - q`. In the mixed cases the folded angle brings in a penalty
`(13/20) |s - d|`. For `-5/8 ≤ s ≤ 2/3` and `0 ≤ d ≤ π/4` the potential
`G s = (387/1000) cos s + |sin s|/2 + (113/1000) sin s` plus this penalty is
smallest at `s = d`: on `[0, π/4]` the derivative of `G` lies between
`-387/1000` and `613/1000`, and on `[-5/8, 0]` we have `G s ≥ 387/1000 = G 0`.
For `d ≥ 2/3` it is smallest at `s = 2/3`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def foldedSecondaryAngle (q : ℝ) : ℝ := Real.pi/2-|q-Real.pi/2|

lemma secondary_cost_folded_lower {a b q : ℝ} (hc : ContainedChart a |b|)
    (hq : 1/2≤q ∧ q≤Real.pi-1/2) :
    -91/125-(13/20)*foldedSecondaryAngle q<
      angularWidth q-((1+Real.sin q)*a+Real.cos q*b) := by
  by_cases hhalf : q≤Real.pi/2
  · have hh := secondary_cost_first_quadrant hc ⟨hq.1,hhalf⟩
    have he : foldedSecondaryAngle q=q := by
      rw [foldedSecondaryAngle,abs_of_nonpos (by linarith)]
      ring
    simpa only [he] using hh
  · have hc' : ContainedChart a |-b| := by simpa only [abs_neg] using hc
    have hh := secondary_cost_first_quadrant hc'
      (q := Real.pi-q) ⟨by linarith [hq.2],by linarith⟩
    have he : foldedSecondaryAngle q=Real.pi-q := by
      rw [foldedSecondaryAngle,abs_of_nonneg (by linarith)]
      ring
    simp only [angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg] at hh ⊢
    rw [he]
    nlinarith only [hh]

def ownWingPotential (s : ℝ) : ℝ :=
  (387/1000)*Real.cos s+|Real.sin s|/2+(113/1000)*Real.sin s

def positiveWing (s : ℝ) : ℝ := (387/1000)*Real.cos s+(613/1000)*Real.sin s

lemma ownWingPotential_nonnegative_angle {s : ℝ} (hs : 0≤ s ∧ s≤Real.pi/4) :
    ownWingPotential s=positiveWing s := by
  have ht := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_pos])
  rw [ownWingPotential,abs_of_nonneg ht,positiveWing]
  ring

lemma ownWingPotential_negative_lower {s : ℝ} (hs : -5/8≤ s ∧ s≤0) :
    387/1000≤ownWingPotential s := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show s∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hs.1,hs.2,Real.pi_gt_d2])
  have ht := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤-s by linarith [hs.2]) (by linarith [hs.1,Real.pi_gt_d2])
  rw [Real.sin_neg] at ht
  have hw := one_le_abs_cos_add_abs_sin s
  rw [abs_of_nonneg hc,abs_of_nonpos (by linarith)] at hw
  rw [ownWingPotential,abs_of_nonpos (by linarith)]
  linarith

lemma positiveWing_minus_antitone :
    AntitoneOn (fun x : ℝ => positiveWing x-(13/20)*x) (Set.Icc 0 (Real.pi/4)) := by
  apply Seven.antiOn_of_hasDeriv_nonpos (by dsimp [positiveWing]; fun_prop)
  · intro x _
    exact (((Real.hasDerivAt_cos x).const_mul (387/1000)).fun_add
      ((Real.hasDerivAt_sin x).const_mul (613/1000))).fun_sub
      ((hasDerivAt_id' x).const_mul (13/20))
  · intro x hx
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le
      (by linarith [hx.2,Real.pi_pos])
    linarith [Real.cos_le_one x]

lemma positiveWing_plus_monotone :
    MonotoneOn (fun x : ℝ => positiveWing x+(13/20)*x) (Set.Icc 0 (Real.pi/4)) := by
  apply Seven.monoOn_of_hasDeriv_nonneg (by dsimp [positiveWing]; fun_prop)
  · intro x _
    exact (((Real.hasDerivAt_cos x).const_mul (387/1000)).fun_add
      ((Real.hasDerivAt_sin x).const_mul (613/1000))).fun_add
      ((hasDerivAt_id' x).const_mul (13/20))
  · intro x hx
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    linarith [Real.sin_le_one x]

/-- `G s + (13/20) |s - d|` is at least `G d`, for `0 ≤ d ≤ π/4`. -/
lemma own_wing_penalty_lower {s d : ℝ}
    (hs : -5/8≤ s ∧ s≤2/3) (hd : 0≤d ∧ d≤Real.pi/4) :
    positiveWing d≤ownWingPotential s+(13/20)*|s-d| := by
  by_cases hs0 : 0≤ s
  · have hspi : s≤Real.pi/4 := by linarith [hs.2,Real.pi_gt_d2]
    rw [ownWingPotential_nonnegative_angle ⟨hs0,hspi⟩]
    rcases le_total s d with hsd | hds
    · have hh := positiveWing_minus_antitone ⟨hs0,hspi⟩ hd hsd
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh := positiveWing_plus_monotone hd ⟨hs0,hspi⟩ hds
      rw [abs_of_nonneg (by linarith)]
      linarith
  · have hh := positiveWing_minus_antitone
      (show (0:ℝ)∈Set.Icc 0 (Real.pi/4) by constructor <;> linarith [Real.pi_pos]) hd hd.1
    have hp := ownWingPotential_negative_lower ⟨hs.1,(lt_of_not_ge hs0).le⟩
    norm_num [positiveWing] at hh
    rw [abs_of_nonpos (by linarith [hd.1]),positiveWing]
    linarith [lt_of_not_ge hs0]

/-- For `d ≥ 2/3`, `G s + (13/20) |s - d|` is at least its value at
`s = 2/3`. -/
lemma own_wing_penalty_endpoint {s d : ℝ}
    (hs : -5/8≤ s ∧ s≤2/3) (hd : 2/3≤d) :
    positiveWing (2/3)+(13/20)*(d-2/3)≤ownWingPotential s+(13/20)*|s-d| := by
  have hb := own_wing_penalty_lower hs
    (d := (2:ℝ)/3) ⟨by norm_num,by linarith [Real.pi_gt_d2]⟩
  rw [abs_of_nonpos (by linarith [hs.2])] at hb
  rw [abs_of_nonpos (by linarith [hs.2])]
  linarith

end SquaresInCircles.Six.Analytic
