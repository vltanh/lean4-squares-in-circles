import SquaresInCircles.Seven.BoundarySegments

/-!
# Profiles along the boundary of the label regions

The transition profile is positive by a curvature bound and one fixed value, the
diagonal profile by monotonicity. The fixed values at the label `18/25` and at
the diagonal corner come from rational brackets of `π`, of the transition state
and of the circle, and from Taylor bounds of `sin` and `cos`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def testLabel : ℝ := 18/25
def testAngle : ℝ := gap-testLabel+s0
def testValue : ℝ := 1-Y testLabel-(a0-1/2)*Real.sin testAngle+Y0*Real.cos testAngle
def testSlope : ℝ := -X testLabel/Z testLabel+(a0-1/2)*Real.cos testAngle+Y0*Real.sin testAngle

def diagonalAngle : ℝ := td+s0-Real.pi/6
def diagonalValue : ℝ := 1/2-rd-(a0-1/2)*Real.sin diagonalAngle+Y0*Real.cos diagonalAngle

lemma test_mem : testLabel ∈ Icc s0 td := by
  have hs := transition_coarse
  have ht := td_bounds
  dsimp [testLabel]
  constructor <;> linarith

lemma test_point : 1/10000 < testValue ∧ |testSlope| < 1/150 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have ht := transition_bounds
  have hD : 59525/100000 < D testLabel ∧ D testLabel < 59527/100000 := by
    dsimp only [D,testLabel]
    constructor <;> linarith
  have hZ : 13545/10000 < Z testLabel ∧ Z testLabel < 13547/10000 := by
    have hs := Z_sq test_mem
    have hz := Z_pos test_mem
    dsimp only [N,targetSq] at hs
    constructor <;> nlinarith [mul_pos (sub_pos.mpr hD.1) (sub_pos.mpr hD.2)]
  have hX : 13330/10000 < X testLabel ∧ X testLabel < 13332/10000 := by
    unfold X N
    constructor <;> linarith
  have hY : Y testLabel < 12138/10000 := by
    unfold Y N
    linarith
  have hb := trig_bracket (l := 6913/10000) (u := 6915/10000) (x := testAngle) (by norm_num)
    (by linarith) (by dsimp [testAngle,gap,testLabel,s0]; constructor <;> linarith)
  norm_num at hb
  have hY0 : 79136/100000 < Y0 ∧ Y0 < 79137/100000 := by
    dsimp [u0] at ht
    constructor <;> linarith
  have hq1 : 13330/13547 < X testLabel/Z testLabel := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have hq2 : X testLabel/Z testLabel < 13332/13545 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sin testAngle := by linarith
  have hc0 : 0 ≤ Real.cos testAngle := by linarith
  have ha1 := mul_le_mul_of_nonneg_right (show a0-1/2 ≤ 61980/100000 by linarith) hs0
  have ha2 := mul_le_mul_of_nonneg_right (show a0-1/2 ≤ 61980/100000 by linarith) hc0
  have ha3 := mul_le_mul_of_nonneg_right (show 61979/100000 ≤ a0-1/2 by linarith) hc0
  have hy1 := mul_le_mul_of_nonneg_right hY0.1.le hc0
  have hy2 := mul_le_mul_of_nonneg_right hY0.1.le hs0
  have hy3 := mul_le_mul_of_nonneg_right hY0.2.le hs0
  refine ⟨by dsimp only [testValue]; linarith,abs_lt.mpr ⟨?_,?_⟩⟩ <;>
    dsimp only [testSlope] <;> rw [neg_div] <;> linarith

lemma diagonal_angle_bounds : 6246/10000 < diagonalAngle ∧ diagonalAngle < 6248/10000 := by
  have hp := transition_bounds
  have hr := rd_bounds
  dsimp [diagonalAngle,td,s0]
  constructor <;> linarith

lemma diagonal_value_pos : 0 < diagonalValue := by
  have hr := rd_bounds
  have ha := transition_bounds
  have hd := diagonal_angle_bounds
  have hb := trig_bracket (l := 6246/10000) (u := 6248/10000) (x := diagonalAngle)
    (by norm_num) (by linarith [Real.pi_gt_d2]) ⟨hd.1.le,hd.2.le⟩
  norm_num at hb
  have hY0 : 79136/100000 < Y0 := by dsimp [u0] at ha; linarith
  have h1 := mul_le_mul_of_nonneg_right (show a0-1/2 ≤ 61980/100000 by linarith)
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

lemma transition_curvature {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ td) :
    (3:ℝ)/8 < transitionFDD t := by
  have hs := transition_coarse
  have ht' : s0 ≤ t ∧ t ≤ td := ⟨by linarith,ht.2⟩
  have hb := circle_bounds ht'
  have hZ0 : 0 < Z t := by linarith [hb.2.2.2.2.2.1]
  have hZ3 : (Z t)^3 < (7/5:ℝ)^3 := by gcongr; exact hb.2.2.2.2.2.2
  have hlead : (7:ℝ)/8 < (3/4)*targetSq/(Z t)^3 := by
    apply (lt_div_iff₀ (pow_pos hZ0 3)).mpr
    dsimp [targetSq]
    linarith
  have hangle : Real.pi/6 < transitionAngle t ∧ transitionAngle t < Real.pi/2 := by
    dsimp [transitionAngle,gap]
    constructor <;> linarith [ht.1,ht.2,td_bounds.2,pi_lt_22_over_7,Real.pi_gt_d2]
  have hsin : 1/2 ≤ Real.sin (transitionAngle t) := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      hangle.2.le hangle.1.le
    simpa only [Real.sin_pi_div_six] using hh
  have hc0 : 0 ≤ Real.cos (transitionAngle t) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hangle.1,Real.pi_pos],hangle.2.le⟩
  have hlow : (3:ℝ)/10 < (a0-1/2)*Real.sin (transitionAngle t) := by
    have ha : (3:ℝ)/5 < a0-1/2 := by linarith
    linarith [mul_nonneg (sub_nonneg.mpr hsin) (show 0 ≤ a0-1/2 by linarith)]
  have hu : Y0*Real.cos (transitionAngle t) < (4:ℝ)/5 := by
    have hy : 0 ≤ Y0 ∧ Y0 < 4/5 := by dsimp [u0] at hs; constructor <;> linarith
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one (transitionAngle t)) hy.1
    linarith
  dsimp [transitionFDD]
  linarith

lemma transitionF_pos {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ td) : 0 < transitionF t := by
  have hs := transition_coarse
  have sub (x : ℝ) (hx : x ∈ Icc (2/5) td) : x ∈ Icc s0 td := ⟨by linarith [hx.1],hx.2⟩
  have htest : testLabel ∈ Icc (2/5) td := by
    dsimp [testLabel]
    exact ⟨by norm_num,td_bounds.1.le⟩
  obtain ⟨hv,hd⟩ := test_point
  have hd2 := sq_lt_sq' (abs_lt.mp hd).1 (abs_lt.mp hd).2
  exact positive_of_curvature (κ := 3/8) (by norm_num) ht htest
    (fun x hx => hasDerivAt_transitionF (sub x hx))
    (fun x hx => hasDerivAt_transitionFD (sub x hx))
    (fun x hx => (transition_curvature hx).le)
    (by dsimp [transitionF,transitionFD,transitionAngle,testValue,testSlope,testAngle] at *
        nlinarith)

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
    exact transitionF_pos ⟨by linarith [td_bounds.1],le_rfl⟩
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

lemma diagonalSlope_gt {x : ℝ} (hx : Real.pi/3 ≤ x ∧ x ≤ 7*Real.pi/12-2/5) :
    (6:ℝ)/5 < (51/40)*Real.sin x+(11/40)*Real.cos x := by
  have h := trig_concave_gt (α := 0) (A := 51/40) (B := 11/40) (m := 6/5) (by norm_num)
    (by norm_num) (by linarith [Real.pi_pos]) (by linarith [pi_lt_22_over_7]) hx
    (by rw [Real.sin_pi_div_three,Real.cos_pi_div_three]; linarith [sqrt_three_bounds.1])
    (by
      have hz : 7/5 < 7*Real.pi/12-2/5 ∧ 7*Real.pi/12-2/5 < Real.pi/2 := by
        constructor <;> linarith [Real.pi_gt_d2,pi_lt_22_over_7]
      have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        hz.2.le hz.1.le
      have hlow := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 7/5 by norm_num)
      have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hz.1,Real.pi_pos],hz.2.le⟩
      linarith)
  linarith

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
    have he : 27/200 < e ∧ e < 3/20 := by dsimp [e]; constructor <;> linarith [Real.pi_gt_d2,pi_lt_22_over_7]
    have hs := Real.sin_ge_sub_cube (show 0 ≤ e by linarith)
    have he3 : e^3 ≤ (3/20:ℝ)^3 := pow_le_pow_left₀ (by linarith [he.1]) he.2.le 3
    have heL : 29/210 ≤ e := by dsimp [e]; linarith [pi_lt_22_over_7]
    have hsL : 27/200 < Real.sin e := by linarith
    have hid : Real.cos (7*Real.pi/12-2/5)=Real.sin e := by
      rw [show 7*Real.pi/12-2/5=Real.pi/2-e by dsimp [e]; ring,
        Real.cos_pi_div_two_sub]
    dsimp [diagonalK]
    rw [hid]
    linarith [Real.sin_le_one (7*Real.pi/12-2/5),Real.pi_gt_d2]
  exact hbase.trans_le (hm ⟨le_rfl,by linarith [Real.pi_gt_d2]⟩ ht ht.1)

end Boundary
end SquaresInCircles.Seven
