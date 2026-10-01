import research.seven.lean.SideCircle
import research.seven.lean.EndpointArithmetic
import SquaresInCircles.Seven.BoundaryProfiles

/-!
J: completed endpoint proof. No production test_point, transitionF_pos,
diagonal_value_pos, transition_bounds, or diagonal_angle_bounds is applied.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human
open Boundary

lemma transition_angle_hasDeriv (t : ℝ) : HasDerivAt transitionAngle (-1) t := by
  convert (((hasDerivAt_const t gap).sub (hasDerivAt_id t)).add_const s0) using 1 <;>
    first | rfl | ring

lemma transitionF_hasDeriv {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt transitionF (transitionFD t) t := by
  have hd := (((side_Y_hasDeriv ht).const_sub 1).sub
    ((transition_angle_hasDeriv t).sin.const_mul (a0-1/2))).add
    ((transition_angle_hasDeriv t).cos.const_mul Y0)
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [transitionF]; ring) |
      (dsimp [transitionFD]; ring)

lemma transitionFD_hasDeriv {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt transitionFD (transitionFDD t) t := by
  have hd := (((side_Yprime_hasDeriv ht).neg).add
    ((transition_angle_hasDeriv t).cos.const_mul (a0-1/2))).add
    ((transition_angle_hasDeriv t).sin.const_mul Y0)
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [transitionFD]; ring) |
      (dsimp [transitionFDD,targetSq]; ring)

lemma transition_endpoint_theta : transitionAngle td=endTheta a0 u0 rd := by
  have hl := transition_state_line
  dsimp [transitionAngle,gap,td,s0,endTheta]
  linarith

lemma transition_endpoint_identities :
    transitionF td=endU a0 u0 rd ∧ transitionFD td=endV a0 u0 rd := by
  have hc := side_diagonal_coordinates
  have hY : u0+1/2=Y0 := by dsimp [u0]; ring
  have hq : rd+1/2 ≠ 0 := by linarith [diagonal_radius_coarse.1]
  constructor
  · dsimp only [transitionF]
    rw [hc.2.1,transition_endpoint_theta]
    dsimp [endU,endH]
    rw [hY]
    ring
  · dsimp only [transitionFD]
    rw [hc.1,hc.2.2,transition_endpoint_theta]
    dsimp [endV,endK]
    rw [hY]
    field_simp [hq]
    ring

lemma transition_diagonal_endpoint :
    (1 : ℝ)/640 < transitionF td ∧
    0 < transitionFD td ∧ transitionFD td < 7/160 := by
  have hu := transition_coarse_geometric
  have hr := diagonal_radius_coarse
  have hm := correlated_endpoint_margins
    (u := u0) (r := rd)
    ⟨hu.2.2.1.le,hu.2.2.2.1.le⟩
    ⟨by linarith [hr.1],hr.2.le⟩
  rw [correlated_at_transition] at hm
  rw [transition_endpoint_identities.1,transition_endpoint_identities.2]
  exact hm

lemma transition_curvature_gt_five_eighths {t : ℝ}
    (ht : (2 : ℝ)/5 ≤ t ∧ t ≤ td) : (5 : ℝ)/8 < transitionFDD t := by
  have hcoarse := transition_coarse_geometric
  have hsub : s0 ≤ t ∧ t ≤ td := ⟨by linarith [hcoarse.2.2.2.2.2],ht.2⟩
  have hc := side_circle_data hsub
  let q : ℝ := rd+1/2
  have hq2 : q^2=(13 : ℝ)/8 := diagonal_square
  have hq0 : 0 < q := by dsimp [q]; linarith [diagonal_radius_coarse.1]
  have hqhi : q < (51 : ℝ)/40 := by dsimp [q]; linarith [diagonal_radius_coarse.2]
  have hq3 : q^3=(13/8 : ℝ)*q := by
    calc
      q^3 = q*q^2 := by ring
      _ = _ := by rw [hq2]; ring
  have hz3 : (Z t)^3 ≤ (28561/13824 : ℝ)*q := by
    calc
      (Z t)^3 ≤ ((13/12)*q)^3 := pow_le_pow_left₀ hc.z_pos.le hc.z_diagonal 3
      _ = (2197/1728 : ℝ)*q^3 := by ring
      _ = _ := by rw [hq3]; ring
  have hlead : (37 : ℝ)/40 < (3/4)*targetSq/(Z t)^3 := by
    apply (lt_div_iff₀ (pow_pos hc.z_pos 3)).mpr
    dsimp [targetSq]
    nlinarith
  have hθ : (31 : ℝ)/50 < transitionAngle t ∧ transitionAngle t < Real.pi/2 := by
    have he := transition_endpoint_angle
    dsimp [transitionAngle,gap]
    constructor <;> linarith [ht.1,ht.2,he.1,hcoarse.2.2.2.2.2,Real.pi_pos]
  have hs : (29 : ℝ)/50 < Real.sin (transitionAngle t) := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := (31/50 : ℝ)) (y := transitionAngle t)
      (by linarith [pi_lower]) hθ.2.le hθ.1.le
    have hT := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 31/50 by norm_num)
    linarith
  have hcos : Real.cos (transitionAngle t) < (57 : ℝ)/70 := by
    have hm := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := (31/50 : ℝ)) (y := transitionAngle t) (by norm_num)
      (by linarith [hθ.2,Real.pi_pos]) hθ.1.le
    have hT := Seven.cos_upper_four (show (0 : ℝ) ≤ 31/50 by norm_num)
    linarith
  have hs0 : 0 ≤ Real.sin (transitionAngle t) := by linarith
  have hc0 : 0 ≤ Real.cos (transitionAngle t) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.le⟩
  have hxy := transition_xy_bounds
  have hprod1 := mul_le_mul_of_nonneg_right
    (show (3 : ℝ)/5 ≤ a0-1/2 by linarith [hcoarse.1]) hs0
  have hprod2 := mul_le_mul_of_nonneg_left hcos.le
    (show 0 ≤ Y0 by linarith [hxy.2.2.1])
  dsimp [transitionFDD]
  nlinarith [hxy.2.2.2]

/-- The diagonal endpoint supplies a uniform reserve on the entire profile. -/
theorem transition_profile_reserve {t : ℝ} (ht : (2 : ℝ)/5 ≤ t ∧ t ≤ td) :
    (1 : ℝ)/32000 < transitionF t := by
  have hc := transition_coarse_geometric
  have hsub (y : ℝ) (hy : y ∈ Icc (2/5 : ℝ) td) : s0 ≤ y ∧ y ≤ td :=
    ⟨by linarith [hy.1,hc.2.2.2.2.2],hy.2⟩
  have he := transition_diagonal_endpoint
  exact positive_from_endpoint_reserve (F := transitionF) (d := transitionFD)
    (dd := transitionFDD) ht
    (fun y hy => transitionF_hasDeriv (hsub y hy))
    (fun y hy => transitionFD_hasDeriv (hsub y hy))
    (fun y hy => (transition_curvature_gt_five_eighths hy).le)
    he.1 he.2

theorem transitionF_pos {t : ℝ} (ht : (2 : ℝ)/5 ≤ t ∧ t ≤ td) :
    0 < transitionF t := by linarith [transition_profile_reserve ht]

def cornerWave (θ : ℝ) : ℝ := -(a0-1/2)*Real.sin θ+Y0*Real.cos θ

lemma cornerWave_hasDeriv (θ : ℝ) : HasDerivAt cornerWave
    (-(a0-1/2)*Real.cos θ-Y0*Real.sin θ) θ := by
  have hd := (((Real.hasDerivAt_sin θ).const_mul (a0-1/2)).neg).add
    ((Real.hasDerivAt_cos θ).const_mul Y0)
  convert hd using 1 <;>
    first | rfl | (funext y; dsimp [cornerWave]; ring) | ring

lemma cornerWave_antitone : AntitoneOn cornerWave (Icc 0 (Real.pi/2)) := by
  apply Seven.antiOn_of_hasDeriv_nonpos
    (d := fun θ => -(a0-1/2)*Real.cos θ-Y0*Real.sin θ)
  · unfold cornerWave; fun_prop
  · intro θ _; exact cornerWave_hasDeriv θ
  · intro θ hθ
    have hb := transition_coarse_geometric
    have hy := transition_coordinates_positive
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le
      (by linarith [hθ.2,Real.pi_pos])
    have hc := Real.cos_nonneg_of_mem_Icc
      (show θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [hθ.1,hθ.2,Real.pi_pos])
    have h1 := mul_nonneg (show 0 ≤ a0-1/2 by linarith [hb.1]) hc
    have h2 := mul_nonneg hy.2.1.le hs
    nlinarith

lemma diagonal_value_reserve : (1 : ℝ)/640 < diagonalValue := by
  have hψ := diagonal_angle_coarse
  have hθ := transition_endpoint_angle
  have htd := diagonal_label_coarse
  have hψdom : diagonalAngle ∈ Icc 0 (Real.pi/2) := by
    dsimp [diagonalAngle]
    constructor <;> linarith [hψ.1,hψ.2,pi_lower]
  have hθdom : transitionAngle td ∈ Icc 0 (Real.pi/2) := by
    dsimp [transitionAngle,gap]
    constructor <;> linarith [hθ.1,hθ.2,pi_lower]
  have horder : diagonalAngle ≤ transitionAngle td := by
    dsimp [diagonalAngle,transitionAngle,gap]
    linarith [htd.2]
  have hm := cornerWave_antitone hψdom hθdom horder
  have hf : transitionF td=1/2-rd+cornerWave (transitionAngle td) := by
    dsimp [transitionF,cornerWave]
    rw [side_diagonal_coordinates.2.1]
    ring
  have hd : diagonalValue=1/2-rd+cornerWave diagonalAngle := by
    dsimp [diagonalValue,cornerWave]
    ring
  have he := transition_diagonal_endpoint.1
  rw [hf] at he
  rw [hd]
  linarith

theorem diagonal_value_pos : 0 < diagonalValue := by linarith [diagonal_value_reserve]

end SquaresInCircles.Seven.Human
