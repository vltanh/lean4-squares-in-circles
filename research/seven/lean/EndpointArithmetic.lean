import research.seven.lean.EndpointComparison

/-!
J: one derived endpoint, not a list of approximate state/angle enclosures.
The angle below is endTheta at the comparison corner fixed by geometry.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

def endAlpha : ℝ := 2351/3744

lemma end_alpha_value : endTheta (131/117) (7/24) (31/40)=endAlpha := by
  norm_num [endTheta,endAlpha]

lemma end_alpha_increment : endAlpha-5/8=(11 : ℝ)/3744 := by norm_num [endAlpha]

lemma end_alpha_range : (5 : ℝ)/8 ≤ endAlpha ∧ endAlpha < 63/100 := by
  norm_num [endAlpha]

lemma endpoint_cos_band {y : ℝ} (hy : 5/8 ≤ y ∧ y ≤ endAlpha) :
    (4 : ℝ)/5 ≤ Real.cos y ∧ Real.cos y ≤ 13/16 := by
  have hlo : 0 ≤ y := by linarith [hy.1]
  have hhi : y < (63 : ℝ)/100 := hy.2.trans_lt end_alpha_range.2
  have hy2 : y^2 ≤ (63/100 : ℝ)^2 := by nlinarith
  have hl := Real.one_sub_sq_div_two_le_cos (x := y)
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi
    (x := (5/8 : ℝ)) (y := y) (by norm_num)
    (by linarith [pi_lower]) hy.1
  have hu := Seven.cos_upper_four (show (0 : ℝ) ≤ 5/8 by norm_num)
  constructor <;> nlinarith

lemma endpoint_alpha_sine :
    (37 : ℝ)/63 < Real.sin endAlpha ∧ Real.sin endAlpha < 47/80 := by
  have hmono : MonotoneOn (fun y : ℝ => Real.sin y-(4/5)*y)
      (Icc (5/8) endAlpha) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (d := fun y => Real.cos y-4/5)
    · fun_prop
    · intro y _
      exact (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).const_mul (4/5))
    · intro y hy
      linarith [(endpoint_cos_band ⟨hy.1.le,hy.2.le⟩).1]
  have hanti : AntitoneOn (fun y : ℝ => Real.sin y-(13/16)*y)
      (Icc (5/8) endAlpha) := by
    apply Seven.antiOn_of_hasDeriv_nonpos (d := fun y => Real.cos y-13/16)
    · fun_prop
    · intro y _
      exact (Real.hasDerivAt_sin y).sub ((hasDerivAt_id y).const_mul (13/16))
    · intro y hy
      linarith [(endpoint_cos_band ⟨hy.1.le,hy.2.le⟩).2]
  have hl := hmono ⟨le_rfl,end_alpha_range.1⟩
    ⟨end_alpha_range.1,le_rfl⟩ end_alpha_range.1
  have hu := hanti ⟨le_rfl,end_alpha_range.1⟩
    ⟨end_alpha_range.1,le_rfl⟩ end_alpha_range.1
  have hS7 := Seven.sin_lower_seven (show (0 : ℝ) ≤ 5/8 by norm_num)
  have hS5 := Seven.sin_upper_five (show (0 : ℝ) ≤ 5/8 by norm_num)
  have hleft : (37 : ℝ)/63 <
      (5/8 : ℝ)-(5/8 : ℝ)^3/6+(5/8 : ℝ)^5/120-(5/8 : ℝ)^7/5040+
      (4/5)*(11/3744) := by norm_num
  have hright : (5/8 : ℝ)-(5/8 : ℝ)^3/6+(5/8 : ℝ)^5/120+
      (13/16)*(11/3744) < (47 : ℝ)/80 := by norm_num
  constructor <;> linarith [end_alpha_increment]

lemma endpoint_alpha_cosine :
    (123 : ℝ)/152 < Real.cos endAlpha ∧ Real.cos endAlpha < 17/21 := by
  have hs := endpoint_alpha_sine
  have hc := endpoint_cos_band ⟨end_alpha_range.1,le_rfl⟩
  have hs0 : 0 ≤ Real.sin endAlpha := by linarith [hs.1]
  have hsU := pow_le_pow_left₀ hs0 hs.2.le 2
  have hsL := pow_le_pow_left₀ (show (0 : ℝ) ≤ 37/63 by norm_num) hs.1.le 2
  have hunit := Real.sin_sq_add_cos_sq endAlpha
  constructor <;> nlinarith

lemma endU_rational_corner : endU (131/117) (7/24) (31/40) =
    -11/40-(145/234)*Real.sin endAlpha+(19/24)*Real.cos endAlpha := by
  dsimp [endU,endH]
  rw [end_alpha_value]
  ring

lemma endV_rational_corner : endV (131/117) (7/24) (31/40) =
    (145/234)*Real.cos endAlpha+(19/24)*Real.sin endAlpha-12/13 := by
  dsimp [endV,endK]
  rw [end_alpha_value]
  ring

lemma rational_endpoint_margins :
    (1 : ℝ)/640 < endU (131/117) (7/24) (31/40) ∧
    endV (131/117) (7/24) (31/40) < 7/160 := by
  rw [endU_rational_corner,endV_rational_corner]
  have hs := endpoint_alpha_sine
  have hc := endpoint_alpha_cosine
  constructor <;> linarith [hs.1,hs.2,hc.1,hc.2]

lemma correlated_endpoint_margins {u r : ℝ}
    (hu : (29 : ℝ)/100 ≤ u ∧ u ≤ 7/24)
    (hr : (17 : ℝ)/22 ≤ r ∧ r ≤ 31/40) :
    (1 : ℝ)/640 < endU (correlatedA u) u r ∧
    0 < endV (correlatedA u) u r ∧ endV (correlatedA u) u r < 7/160 := by
  have hc := endpoint_corner_compare hu hr
  have hv := rational_endpoint_margins
  exact ⟨hv.1.trans_le hc.1,hc.2.1,hc.2.2.trans_lt hv.2⟩

end SquaresInCircles.Seven.Human
