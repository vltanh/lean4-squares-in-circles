import SquaresInCircles.Seven.Pair.LabelSegments

/-!
# Seven squares: profiles along the boundary of the label regions

The transition profile is positive by a curvature bound and its value and slope
at the diagonal corner, where `X = Y` and `X/Z = 12/13`; the diagonal profile by
monotonicity. The values at the diagonal corner come from rational brackets of
`π`, of the transition state and of the corner, and from Taylor bounds of `sin`
and `cos`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def diagonalAngle : ℝ := td+s0-Real.pi/6
def diagonalValue : ℝ := 1/2-rd-(a0-1/2)*Real.sin diagonalAngle+Y0*Real.cos diagonalAngle

lemma diagonal_angle_bounds : (0.6246:ℝ) < diagonalAngle ∧ diagonalAngle < 0.6248 := by
  have hp := transition_bounds
  have hr := rd_bounds
  dsimp [diagonalAngle,td,s0]
  constructor <;> linarith

lemma diagonal_value_pos : 0 < diagonalValue := by
  have hr := rd_bounds
  have ha := transition_bounds
  have hd := diagonal_angle_bounds
  have hb := trig_bracket (l := 0.6246) (u := 0.6248) (x := diagonalAngle)
    (by norm_num) (by linarith [Real.pi_gt_d2]) ⟨hd.1.le,hd.2.le⟩
  norm_num at hb
  have hY0 : 0.79136 < Y0 := by dsimp [u0] at ha; linarith
  have h1 := mul_le_mul_of_nonneg_right (show a0-1/2 ≤ 0.6198 by linarith)
    (show 0 ≤ Real.sin diagonalAngle by linarith)
  have h2 := mul_le_mul_of_nonneg_right hY0.le (show 0 ≤ Real.cos diagonalAngle by linarith)
  dsimp only [diagonalValue]
  linarith

def transitionAngle (t : ℝ) : ℝ := gap-t+s0
def transitionF (t : ℝ) : ℝ :=
  1-Y t-(a0-1/2)*Real.sin (transitionAngle t)+Y0*Real.cos (transitionAngle t)
def transitionFD (t : ℝ) : ℝ :=
  -X t/Z t+(a0-1/2)*Real.cos (transitionAngle t)+Y0*Real.sin (transitionAngle t)
def transitionFDD (t : ℝ) : ℝ :=
  (3/4)*targetSq/(Z t)^3+(a0-1/2)*Real.sin (transitionAngle t)-Y0*Real.cos (transitionAngle t)

private lemma angle_derivative (t : ℝ) : HasDerivAt transitionAngle (-1) t := by
  convert (((hasDerivAt_const t gap).sub (hasDerivAt_id t)).add_const s0) using 1
  · rfl
  · ring

lemma hasDerivAt_transitionF {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt transitionF (transitionFD t) t := by
  have hd := (((hasDerivAt_Y ht).const_sub 1).sub
    ((angle_derivative t).sin.const_mul (a0-1/2))).add
    ((angle_derivative t).cos.const_mul Y0)
  convert hd using 1
  · rfl
  · dsimp [transitionFD]; ring

lemma hasDerivAt_transitionFD {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt transitionFD (transitionFDD t) t := by
  have hd := (((hasDerivAt_Y_prime ht).neg).add
    ((angle_derivative t).cos.const_mul (a0-1/2))).add
    ((angle_derivative t).sin.const_mul Y0)
  convert hd using 1
  · funext y; dsimp [transitionFD]; ring
  · dsimp [transitionFDD]; ring

/-- At the diagonal corner the angle of the transition profile lies in
`(0.6272, 0.6273)`. -/
lemma corner_angle_bounds :
    (0.6272:ℝ) < transitionAngle td ∧ transitionAngle td < 0.6273 := by
  have hp := transition_bounds
  have hr := rd_bounds
  dsimp [transitionAngle,gap,td,s0]
  constructor <;> linarith [Real.pi_gt_d4,Real.pi_lt_d4]

/-- The value and the slope of the transition profile at the diagonal corner, where
`1 - Y = 1/2 - r_d` and `X/Z = 12/13`. -/
lemma corner_point :
    0.002 < transitionF td ∧ 0 < transitionFD td ∧ transitionFD td < 0.044 := by
  have ht : s0 ≤ td ∧ td ≤ td :=
    ⟨by linarith [transition_coarse.2.2.2.2.2,td_bounds.1],le_rfl⟩
  obtain ⟨hX,hY⟩ := side_at_diagonal
  dsimp [sideA,sideU] at hX hY
  have hq : X td/Z td = 12/13 := by
    have hp : 0 < rd+1/2 := by linarith [rd_bounds.1]
    rw [← (circle_identities ht).2.2,show X td = rd+1/2 by linarith,
      show Y td = rd+1/2 by linarith,div_eq_iff (by linarith)]
    ring
  have ha := corner_angle_bounds
  have hb := trig_bracket (l := 0.6272) (u := 0.6273) (x := transitionAngle td)
    (by norm_num) (by linarith [Real.pi_gt_d2]) ⟨ha.1.le,ha.2.le⟩
  norm_num at hb
  have hr := rd_bounds
  have h0 := transition_bounds
  have hY0 : 0.79136 < Y0 ∧ Y0 < 0.79137 := by
    dsimp [u0] at h0
    constructor <;> linarith
  have hs0 : 0 ≤ Real.sin (transitionAngle td) := by linarith
  have hc0 : 0 ≤ Real.cos (transitionAngle td) := by linarith
  have h1 := mul_le_mul_of_nonneg_right (show a0-1/2 ≤ 0.6198 by linarith) hs0
  have h2 := mul_le_mul_of_nonneg_right (show a0-1/2 ≤ 0.6198 by linarith) hc0
  have h3 := mul_le_mul_of_nonneg_right (show 0.61979 ≤ a0-1/2 by linarith) hc0
  have h4 := mul_le_mul_of_nonneg_right hY0.1.le hc0
  have h5 := mul_le_mul_of_nonneg_right hY0.1.le hs0
  have h6 := mul_le_mul_of_nonneg_right hY0.2.le hs0
  refine ⟨by dsimp only [transitionF]; linarith,?_,?_⟩ <;>
    dsimp only [transitionFD] <;> rw [neg_div,hq] <;> linarith

/-- `F'' > 1/2` on `[2/5, t_d]`: there `Z < 7/5`, and the angle lies between its
value at the corner, above `0.6272`, and `π/3`, so its sine is at least `1/2` and its
cosine below `0.81`. -/
lemma transition_curvature {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ td) :
    (1:ℝ)/2 < transitionFDD t := by
  have hs := transition_coarse
  have ht' : s0 ≤ t ∧ t ≤ td := ⟨by linarith,ht.2⟩
  have hb := circle_bounds ht'
  have hZ0 : 0 < Z t := by linarith [hb.2.2.2.2.2.1]
  have hZ3 : (Z t)^3 < (7/5:ℝ)^3 := by gcongr; exact hb.2.2.2.2.2.2
  have hlead : (7:ℝ)/8 < (3/4)*targetSq/(Z t)^3 := by
    apply (lt_div_iff₀ (pow_pos hZ0 3)).mpr
    dsimp [targetSq]
    linarith
  have h1 : (0.6272:ℝ) ≤ transitionAngle t := by
    have hc := corner_angle_bounds.1
    dsimp [transitionAngle] at hc ⊢
    linarith [ht.2]
  have hangle : Real.pi/6 < transitionAngle t ∧ transitionAngle t < Real.pi/2 := by
    constructor
    · linarith [pi_lt_22_over_7]
    · dsimp [transitionAngle,gap]
      linarith [ht.1,Real.pi_pos]
  have hsin : 1/2 ≤ Real.sin (transitionAngle t) := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      hangle.2.le hangle.1.le
    simpa only [Real.sin_pi_div_six] using hh
  have hc0 : 0 ≤ Real.cos (transitionAngle t) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hangle.1,Real.pi_pos],hangle.2.le⟩
  have hcos : Real.cos (transitionAngle t) < 0.81 := by
    have hc := (Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num)
      (by linarith [hangle.2,Real.pi_pos]) h1).trans (cos_upper_four (by norm_num))
    norm_num at hc
    linarith
  have hlow : (3:ℝ)/10 < (a0-1/2)*Real.sin (transitionAngle t) := by
    have ha : (3:ℝ)/5 < a0-1/2 := by linarith
    linarith [mul_nonneg (sub_nonneg.mpr hsin) (show 0 ≤ a0-1/2 by linarith)]
  have hu : Y0*Real.cos (transitionAngle t) ≤ (4/5)*0.81 := by
    have hy : Y0 < 4/5 := by dsimp [u0] at hs; linarith
    have hh := mul_le_mul_of_nonneg_right hy.le hc0
    linarith
  dsimp [transitionFDD]
  linarith

/-- The transition profile is positive on `[2/5, t_d]`: it lies above its tangent
parabola of curvature `1/2` at the diagonal corner, where `F'² < F`. -/
lemma transitionF_pos {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ td) : 0 < transitionF t := by
  have hs := transition_coarse
  have sub (x : ℝ) (hx : x ∈ Icc (2/5) td) : x ∈ Icc s0 td := ⟨by linarith [hx.1],hx.2⟩
  obtain ⟨hv,hd0,hd1⟩ := corner_point
  have hd2 := pow_lt_pow_left₀ hd1 hd0.le two_ne_zero
  exact positive_of_curvature (κ := 1/2) (by norm_num) ht ⟨by linarith [td_bounds.1],le_rfl⟩
    (fun x hx => hasDerivAt_transitionF (sub x hx))
    (fun x hx => hasDerivAt_transitionFD (sub x hx))
    (fun x hx => (transition_curvature hx).le)
    (by norm_num at hd2 ⊢; linarith)

def transitionDiagonalF (t : ℝ) : ℝ :=
  1/2-diagonal t-(a0-1/2)*Real.sin (transitionAngle t)+Y0*Real.cos (transitionAngle t)

lemma transitionDiagonalF_pos {t : ℝ} (ht : td ≤ t ∧ t ≤ Real.pi/4) :
    0 < transitionDiagonalF t := by
  have hs := transition_coarse
  have hmono : MonotoneOn transitionDiagonalF (Icc td (Real.pi/4)) := by
    apply monoOn_of_hasDeriv_nonneg
    · unfold transitionDiagonalF diagonal transitionAngle; fun_prop
    · intro x hx
      have ha := angle_derivative x
      have hdiag : HasDerivAt diagonal (-(12/5)) x := by
        convert ((((hasDerivAt_const x (2*Real.pi+7)).sub
          ((hasDerivAt_id x).const_mul 12))).div_const 5) using 1
        · rfl
        · ring
      convert (((hdiag.const_sub (1/2)).sub (ha.sin.const_mul (a0-1/2))).add
        (ha.cos.const_mul Y0)) using 1
      rfl
    · intro x hx
      have hang : 0 ≤ transitionAngle x ∧ transitionAngle x ≤ Real.pi/2 := by
        dsimp [transitionAngle,gap]
        constructor <;> linarith [hx.1,hx.2,td_bounds.1,pi_lt_22_over_7,Real.pi_gt_d2]
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hang.1 (by linarith [hang.2,Real.pi_pos])
      have hcos := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hang.1,Real.pi_pos],hang.2⟩
      have hy0 : 0 ≤ Y0 := by dsimp [u0] at hs; linarith
      have ha0 : 0 ≤ a0-1/2 := by linarith
      linarith [mul_nonneg ha0 hcos,mul_nonneg hy0 hsin]
  have he : transitionDiagonalF td=transitionF td := by
    have hh := side_at_diagonal.2
    dsimp [sideU] at hh
    dsimp [transitionDiagonalF,transitionF,diagonal,td] at *
    linarith
  have hbase : 0 < transitionDiagonalF td := by
    rw [he]
    linarith [corner_point.1]
  exact hbase.trans_le (hmono ⟨le_rfl,td_bounds.2.le⟩ ht ht.1)

lemma transition_actual_pos {a u : ℝ} (h : Admissible a u)
    (hT : label a u=side a u) (ht : 2/5 ≤ label a u) :
    0 < 1/2-u-(a0-1/2)*Real.sin (gap-label a u+s0)+Y0*Real.cos (gap-label a u+s0) := by
  have htop := (side_segment h hT).2.1
  by_cases hc : label a u ≤ td
  · have hp := transitionF_pos ⟨ht,hc⟩
    simp only [sideTopU,ite_eq_left hc] at htop
    dsimp [transitionF,transitionAngle,sideU] at hp htop
    linarith
  · have hp := transitionDiagonalF_pos ⟨(lt_of_not_ge hc).le,h.label_le_quarter⟩
    simp only [sideTopU,ite_eq_right hc] at htop
    dsimp [transitionDiagonalF,transitionAngle] at hp
    linarith

def diagonalK (t : ℝ) : ℝ :=
  (6/5)*(Real.pi/6-t)+(51/40)*Real.cos (7*Real.pi/12-t)-
    (11/40)*Real.sin (7*Real.pi/12-t)

/-- `(51/40) sin x + (11/40) cos x > 6/5` on `[π/3, 7π/12 - 2/5]`: it is concave
there, it is `(51√3 + 11)/80` at `π/3`, and at the right end `π/2 - ε`, with
`0 < ε < 3/20`, its sine is `cos ε > 16/17`. -/
lemma diagonalSlope_gt {x : ℝ} (hx : Real.pi/3 ≤ x ∧ x ≤ 7*Real.pi/12-2/5) :
    (6:ℝ)/5 < (51/40)*Real.sin x+(11/40)*Real.cos x := by
  have h := trig_concave_gt (α := 0) (A := 51/40) (B := 11/40) (m := 6/5) (by norm_num)
    (by norm_num) (by linarith [Real.pi_pos]) (by linarith [pi_lt_22_over_7]) hx
    (by rw [Real.sin_pi_div_three,Real.cos_pi_div_three]; linarith [sqrt_three_bounds.1])
    (by
      have he : 0 < 2/5-Real.pi/12 ∧ 2/5-Real.pi/12 < 3/20 := by
        constructor <;> linarith [Real.pi_gt_three,pi_lt_22_over_7]
      rw [show 7*Real.pi/12-2/5 = Real.pi/2-(2/5-Real.pi/12) by ring,
        Real.sin_pi_div_two_sub,Real.cos_pi_div_two_sub]
      have hc := Real.one_sub_sq_div_two_le_cos (x := 2/5-Real.pi/12)
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi he.1.le (by linarith [Real.pi_gt_three])
      have he2 : (2/5-Real.pi/12)^2 < 2/17 := by nlinarith
      linarith)
  linarith

/-- The diagonal profile is positive on `[2/5, π/4]`: it is nondecreasing there by
`diagonalSlope_gt`, and at `2/5`, where the angle is `π/2 - ε` with
`11/80 < ε < 3/20`, the term in `sin ε ≥ ε - ε³/6 > 2/15` makes it positive. -/
lemma diagonalK_pos {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4) : 0 < diagonalK t := by
  have hm : MonotoneOn diagonalK (Icc (2/5) (Real.pi/4)) := by
    apply monoOn_of_hasDeriv_nonneg
    · unfold diagonalK; fun_prop
    · intro x hx
      have ha : HasDerivAt (fun y : ℝ => 7*Real.pi/12-y) (-1) x := by
        convert (hasDerivAt_const x (7*Real.pi/12)).sub (hasDerivAt_id x) using 1
        · rfl
        · ring
      convert (((((hasDerivAt_const x (Real.pi/6)).sub (hasDerivAt_id x)).const_mul (6/5)).add
        (ha.cos.const_mul (51/40))).sub (ha.sin.const_mul (11/40))) using 1
      rfl
    · intro x hx
      have hh := diagonalSlope_gt
        (x := 7*Real.pi/12-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
      linarith
  have hbase : 0 < diagonalK (2/5) := by
    let e := 2/5-Real.pi/12
    have he : 11/80 < e ∧ e < 3/20 := by
      dsimp [e]
      constructor <;> linarith [Real.pi_gt_three,Real.pi_lt_d2]
    have hs := Real.sin_ge_sub_cube (show 0 ≤ e by linarith)
    have he3 : e^3 < (3/20:ℝ)^3 := pow_lt_pow_left₀ he.2 (by linarith) three_ne_zero
    have hid : Real.cos (7*Real.pi/12-2/5)=Real.sin e := by
      rw [show 7*Real.pi/12-2/5=Real.pi/2-e by dsimp [e]; ring,
        Real.cos_pi_div_two_sub]
    dsimp [diagonalK]
    rw [hid]
    linarith [Real.sin_le_one (7*Real.pi/12-2/5),Real.pi_gt_three]
  exact hbase.trans_le (hm ⟨le_rfl,by linarith [Real.pi_gt_d2]⟩ ht ht.1)

end Boundary
end SquaresInCircles.Seven
