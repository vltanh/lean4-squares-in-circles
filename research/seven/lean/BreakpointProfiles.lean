import research.seven.lean.CoarseBoundary
import research.seven.lean.TurnProfiles

/-! G: scalar replacements for the optional breakpoint simplifications. -/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

def sideJ (d : ℝ) : ℝ :=
  (23/18-14*Real.pi/135+(44/45)*d)*Real.cos d+
    ((6/5)*d-Real.pi/5)*Real.sin d

def sideJD (d : ℝ) : ℝ :=
  (44/45+(6/5)*d-Real.pi/5)*Real.cos d+
    (6/5-(23/18-14*Real.pi/135)-(44/45)*d)*Real.sin d

lemma sideJ_hasDeriv (d : ℝ) : HasDerivAt sideJ (sideJD d) d := by
  have hd : DifferentiableAt ℝ sideJ d := by unfold sideJ; fun_prop
  convert hd.hasDerivAt using 1 <;>
    simp (disch := fun_prop) [sideJ,sideJD] <;> ring

lemma sideJD_positive {d : ℝ} (hd : Real.pi/12 ≤ d ∧ d ≤ 7/10) :
    (1 : ℝ)/10 < sideJD d := by
  have hd0 : 0 ≤ d := by linarith [hd.1,Real.pi_pos]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd0
    (by linarith [hd.2,pi_lower])
  have hs1 : Real.sin d ≤ (7 : ℝ)/10 := (Real.sin_le hd0).trans hd.2
  have hc : (3 : ℝ)/4 < Real.cos d := by
    have ht := Real.one_sub_sq_div_two_le_cos (x := d)
    have hd2 : d^2 ≤ (7/10 : ℝ)^2 := by nlinarith
    nlinarith
  have hb1 : (3 : ℝ)/5 < 44/45+(6/5)*d-Real.pi/5 := by
    linarith [hd.1,pi_upper]
  have hb2 : -(1/2 : ℝ) < 6/5-(23/18-14*Real.pi/135)-(44/45)*d := by
    linarith [hd.2,pi_lower]
  have hm1 := mul_le_mul_of_nonneg_right hb1.le (show 0 ≤ Real.cos d by linarith)
  have hm2 := mul_le_mul_of_nonneg_right hb2.le hs0
  dsimp [sideJD]
  nlinarith

lemma sideJ_left : (1196 : ℝ)/1125 < sideJ (Real.pi/12) := by
  have hx : 0 ≤ Real.pi/12 ∧ Real.pi/12 < (4 : ℝ)/15 := by
    constructor <;> linarith [Real.pi_pos,pi_upper]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos])
  have hs : Real.sin (Real.pi/12) < (4 : ℝ)/15 := (Real.sin_le hx.1).trans_lt hx.2
  have hc : (24 : ℝ)/25 < Real.cos (Real.pi/12) := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := Real.pi/12)
    have hsq : (Real.pi/12)^2 ≤ (4/15 : ℝ)^2 := by nlinarith [hx.1,hx.2]
    nlinarith
  have hb : (6 : ℝ)/5 < 23/18-Real.pi/45 := by linarith [pi_upper]
  have hp : Real.pi/10 < (1 : ℝ)/3 := by linarith [pi_upper]
  have hm1 := mul_le_mul_of_nonneg_right hb.le (show 0 ≤ Real.cos (Real.pi/12) by linarith)
  have hm2 := mul_le_mul_of_nonneg_right hp.le hs0
  have hid : sideJ (Real.pi/12) =
      (23/18-Real.pi/45)*Real.cos (Real.pi/12)-(Real.pi/10)*Real.sin (Real.pi/12) := by
    dsimp [sideJ]
    ring
  rw [hid]
  nlinarith

lemma sideJ_gt_one {d : ℝ} (hd : Real.pi/12 ≤ d ∧ d ≤ 7/10) : 1 < sideJ d := by
  have hm : MonotoneOn sideJ (Icc (Real.pi/12) (7/10)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg (d := sideJD)
    · unfold sideJ; fun_prop
    · intro x _; exact sideJ_hasDeriv x
    · intro x hx; linarith [sideJD_positive ⟨hx.1.le,hx.2.le⟩]
  have hh := hm ⟨le_rfl,hd.1.trans hd.2⟩ hd hd.1
  linarith [sideJ_left]

/-- The private production targetH at source label zero, stated explicitly. -/
theorem side_target_zero_gt_one {A v : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) :
    1 < (A+1/2)*Real.cos (gap-label A v)+
      (1/2-v)*Real.sin (gap-label A v) := by
  let s := label A v
  let d := gap-s
  have ht := side_selected_label_gt h hT
  have hq := h.label_le_quarter
  have hd : Real.pi/12 ≤ d ∧ d ≤ 7/10 := by
    dsimp [d,s,gap]
    constructor <;> linarith [pi_upper]
  have hd0 : 0 ≤ d := by linarith [hd.1,Real.pi_pos]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [hd.2,pi_lower])
  have hc0 := Real.cos_nonneg_of_mem_Icc
    (show d ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,pi_lower])
  have he := side_line hT
  have hu := h.label_le_axial
  dsimp [axial] at hu
  have hA : 23/18-14*Real.pi/135+(44/45)*d ≤ A+1/2 := by
    dsimp [d,s,gap]
    linarith
  have hv : (6/5)*d-Real.pi/5 ≤ 1/2-v := by
    have hh := side_identity_transverse A v
    rw [← hT] at hh
    dsimp [d,s,gap]
    linarith [h.remainder_nonneg]
  have hm1 := mul_le_mul_of_nonneg_right hA hc0
  have hm2 := mul_le_mul_of_nonneg_right hv hs0
  have hp := sideJ_gt_one hd
  dsimp [sideJ] at hp
  change 1 < (A+1/2)*Real.cos d+(1/2-v)*Real.sin d
  linarith

def clearanceSwitch : ℝ := Real.pi/2-5/4+1/68
def clearanceQ (z : ℝ) : ℝ := 1/170+z/15-z^2/4

def farProfile (z : ℝ) : ℝ :=
  1/2-Real.pi/5+(6/5)*z-(Real.sqrt 3-1)*Real.sin z-(1/2)*(1-Real.cos z)

lemma clearance_switch_bounds : (1 : ℝ)/3 < clearanceSwitch ∧ clearanceSwitch < 40/119 := by
  dsimp [clearanceSwitch]
  constructor <;> linarith [pi_lower,pi_upper]

lemma clearance_crossing (z : ℝ) :
    (1/170+(4/5)*z)-(1/2-Real.pi/5+(6/5)*z)=(2/5)*(clearanceSwitch-z) := by
  dsimp [clearanceSwitch]
  ring

lemma clearanceQ_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 40/119) : 0 < clearanceQ z := by
  apply Seven.positive_of_second_nonpos
    (f := clearanceQ) (d := fun z => 1/15-z/2) (dd := fun _ => -(1/2 : ℝ)) hz
  · unfold clearanceQ; fun_prop
  · fun_prop
  · intro y _
    have hd : DifferentiableAt ℝ clearanceQ y := by unfold clearanceQ; fun_prop
    convert hd.hasDerivAt using 1 <;>
      simp (disch := fun_prop) [clearanceQ] <;> ring
  · intro y _
    convert (hasDerivAt_const y (1/15 : ℝ)).sub ((hasDerivAt_id y).div_const 2) using 1 <;> norm_num
  · intro _ _; norm_num
  · norm_num [clearanceQ]
  · norm_num [clearanceQ]

lemma farProfile_pos {z : ℝ} (hz : (1 : ℝ)/3 ≤ z ∧ z ≤ 7/10) : 0 < farProfile z := by
  have hm : MonotoneOn farProfile (Icc (1/3) (7/10)) := by
    apply Seven.monoOn_of_hasDeriv_nonneg
      (d := fun x => 6/5-(Real.sqrt 3-1)*Real.cos x-(1/2)*Real.sin x)
    · unfold farProfile; fun_prop
    · intro x _
      have hd : DifferentiableAt ℝ farProfile x := by unfold farProfile; fun_prop
      convert hd.hasDerivAt using 1 <;>
        simp (disch := fun_prop) [farProfile] <;> ring
    · intro x _; linarith [opposite_derivative_vector x]
  have hb : 0 < farProfile (1/3) := by
    have hs := Seven.sin_upper_five (show (0 : ℝ) ≤ 1/3 by norm_num)
    have hc := Real.one_sub_sq_div_two_le_cos (x := (1/3 : ℝ))
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi
      (show (0 : ℝ) ≤ 1/3 by norm_num) (by linarith [pi_lower])
    have hr : Real.sqrt 3-1 < (11 : ℝ)/15 := by linarith [sqrt_three_coarse.2]
    have hp := mul_le_mul_of_nonneg_right hr.le hs0
    dsimp [farProfile]
    nlinarith [pi_upper]
  exact hb.trans_le (hm (by constructor <;> norm_num) hz hz.1)

lemma clearance_support_pos {z w : ℝ} (hz : 0 ≤ z ∧ z ≤ 7/10)
    (h1 : 1/170+(4/5)*z ≤ w) (h2 : 1/2-Real.pi/5+(6/5)*z ≤ w) :
    0 < w-(Real.sqrt 3-1)*Real.sin z-(1/2)*(1-Real.cos z) := by
  by_cases hs : z ≤ clearanceSwitch
  · have hq := clearanceQ_pos ⟨hz.1,hs.trans clearance_switch_bounds.2.le⟩
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,pi_lower])
    have hr : Real.sqrt 3-1 ≤ (11 : ℝ)/15 := by linarith [sqrt_three_coarse.2]
    have hp := mul_le_mul_of_nonneg_right hr hsin0
    have hsin := Real.sin_le hz.1
    have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
    dsimp [clearanceQ] at hq
    nlinarith
  · have hzlo : (1 : ℝ)/3 ≤ z := by linarith [clearance_switch_bounds.1]
    have hp := farProfile_pos ⟨hzlo,hz.2⟩
    dsimp [farProfile] at hp
    linarith

lemma coarse_forward_positive {t u T : ℝ}
    (ht : (3 : ℝ)/10 ≤ t) (hu : (4/5)*t ≤ u) (hT : -(37/50 : ℝ) < T) :
    0 < 1/2+u+T := by linarith

lemma retained_marker_reserve {t : ℝ} (ht : t ≤ (2 : ℝ)/5) :
    (1 : ℝ)/1050 < 1/2-2*Real.pi/15-t/5 := by linarith [pi_upper]

end SquaresInCircles.Seven.Human
