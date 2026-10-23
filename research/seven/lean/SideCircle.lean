import research.seven.lean.CoarseBoundary

/-!
Circle geometry for J. All bounds are reconstructed from L and the defining
radicals. In particular no production transition_bounds, rd_bounds,
circle_bounds, test_point, or profile-positivity theorem is used.
-/
noncomputable section
namespace SquaresInCircles.Seven.Human
open Boundary

lemma diagonal_square : (rd+1/2)^2=(13 : ℝ)/8 := by
  dsimp [rd]
  rw [sub_add_cancel,Real.sq_sqrt (show (0 : ℝ) ≤ 13/8 by norm_num)]

lemma D_diagonal : D td=(5/12)*(rd+1/2) := by
  dsimp [D,td]
  ring

lemma D_transition : D s0=(3/4)*X0-Y0/3 := by
  have hl := transition_state_line
  dsimp [D,s0,a0,u0] at *
  linarith

lemma side_D_bounds {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    (1 : ℝ)/2 < D t ∧ D t < 1 := by
  have hr := diagonal_radius_coarse
  have hu := transition_u_bounds
  dsimp [D,td,s0] at *
  constructor <;> linarith [pi_lower,pi_upper]

lemma side_radicand_pos {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    0 < N*targetSq-(D t)^2 := by
  have hd := side_D_bounds ht
  dsimp [N,targetSq]
  nlinarith

lemma side_Z_pos {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) : 0 < Z t :=
  Real.sqrt_pos.mpr (side_radicand_pos ht)

lemma side_Z_sq {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    (Z t)^2=N*targetSq-(D t)^2 := Real.sq_sqrt (side_radicand_pos ht).le

lemma side_circle_identities {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    (X t)^2+(Y t)^2=(13 : ℝ)/4 ∧
    (3/4)*X t-Y t/3=D t ∧ X t/3+(3/4)*Y t=Z t := by
  have hz := side_Z_sq ht
  have hid : (X t)^2+(Y t)^2=((D t)^2+(Z t)^2)/N := by
    dsimp [X,Y,N]
    ring
  refine ⟨?_,?_,?_⟩
  · rw [hid]
    dsimp [N,targetSq] at *
    nlinarith
  · dsimp [X,Y,N]; ring
  · dsimp [X,Y,N]; ring

lemma side_transition_coordinates : X s0=X0 ∧ Y s0=Y0 := by
  have hc := transition_circle_exact
  have hp := transition_coordinates_positive
  have hs := transition_coarse_geometric
  have ht : s0 ≤ s0 ∧ s0 ≤ td :=
    ⟨le_rfl,by linarith [diagonal_label_coarse.1]⟩
  have hz := side_Z_sq ht
  have hz0 := side_Z_pos ht
  have hZ : Z s0=X0/3+(3/4)*Y0 := by
    rw [D_transition] at hz
    dsimp [N,targetSq] at hz
    nlinarith [hp.1,hp.2.1]
  dsimp [X,Y]
  rw [D_transition,hZ]
  norm_num [N]
  constructor <;> ring

lemma side_diagonal_coordinates :
    X td=rd+1/2 ∧ Y td=rd+1/2 ∧ Z td=(13/12)*(rd+1/2) := by
  have hr := diagonal_radius_coarse
  have hs := diagonal_square
  have hc := transition_coarse_geometric
  have ht : s0 ≤ td ∧ td ≤ td :=
    ⟨by linarith [diagonal_label_coarse.1],le_rfl⟩
  have hz := side_Z_sq ht
  have hp := side_Z_pos ht
  rw [D_diagonal] at hz
  have hZ : Z td=(13/12)*(rd+1/2) := by
    dsimp [N,targetSq] at hz
    nlinarith
  refine ⟨?_,?_,hZ⟩ <;> dsimp [X,Y] <;>
    rw [D_diagonal,hZ] <;> norm_num [N] <;> ring

lemma side_Z_order {s t : ℝ} (hs : s0 ≤ s ∧ s ≤ td)
    (ht : s0 ≤ t ∧ t ≤ td) (hst : s ≤ t) : Z s ≤ Z t := by
  have hds := side_D_bounds hs
  have hdt := side_D_bounds ht
  have hD : D t ≤ D s := by dsimp [D]; linarith
  unfold Z
  apply Real.sqrt_le_sqrt
  nlinarith [hds.1,hdt.1]

structure SideCircleData (t : ℝ) : Prop where
  d_pos : 0 < D t
  z_pos : 0 < Z t
  y_pos : 0 < Y t
  y_lower : Y0 ≤ Y t
  y_le_x : Y t ≤ X t
  x_lower : (5 : ℝ)/4 < X t
  x_upper : X t ≤ X0
  z_lower : (1 : ℝ) < Z t
  z_upper : Z t < (7 : ℝ)/5
  z_diagonal : Z t ≤ (13/12)*(rd+1/2)
  norm_sq : (X t)^2+(Y t)^2=(13 : ℝ)/4
  projection : (3/4)*X t-Y t/3=D t
  perpendicular : X t/3+(3/4)*Y t=Z t

lemma side_circle_data {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) : SideCircleData t := by
  have hd := side_D_bounds ht
  have hz := side_Z_sq ht
  have hz0 := side_Z_pos ht
  have hc := side_circle_identities ht
  have hbase := side_transition_coordinates
  have hdiag := side_diagonal_coordinates
  have hxy0 := transition_xy_bounds
  have hp0 := transition_coordinates_positive
  have hr := diagonal_radius_coarse
  have hD : D t ≤ D s0 := by dsimp [D]; linarith [ht.1]
  have hDZ : D td ≤ D t := by dsimp [D]; linarith [ht.2]
  have hzlo := side_Z_order ⟨le_rfl,ht.1.trans ht.2⟩ ht ht.1
  have hzhi := side_Z_order ht ⟨ht.1.trans ht.2,le_rfl⟩ ht.2
  have hy : Y0 ≤ Y t := by
    have hh : Y s0 ≤ Y t := by dsimp [Y,N]; linarith
    simpa only [hbase.2] using hh
  have hy0 : 0 < Y t := hp0.2.1.trans_le hy
  have hx0 : 0 < X t := by dsimp [X,N]; positivity
  have hyx : Y t ≤ X t := by
    have hrsq := diagonal_square
    rw [D_diagonal] at hDZ
    have hm := mul_nonneg (sub_nonneg.mpr hDZ)
      (show 0 ≤ D t+(5/12)*(rd+1/2) by linarith [hd.1])
    have hcomp : 5*Z t ≤ 13*D t := by
      dsimp [N,targetSq] at hz
      nlinarith [hd.1]
    dsimp [X,Y,N]
    linarith
  have hxlo : (5 : ℝ)/4 < X t := by
    have hm := mul_nonneg (sub_nonneg.mpr hyx)
      (show 0 ≤ X t+Y t by linarith)
    nlinarith [hc.1]
  have hxhi : X t ≤ X0 := by
    have hm := mul_nonneg (sub_nonneg.mpr hy)
      (show 0 ≤ Y t+Y0 by linarith [hp0.2.1])
    nlinarith [hc.1,transition_circle_exact,hp0.1]
  have hzlower : (1 : ℝ) < Z t := by
    linarith [hc.2.2,hxy0.2.2.1]
  have hzdiag : Z t ≤ (13/12)*(rd+1/2) := by simpa only [hdiag.2.2] using hzhi
  have hzupper : Z t < (7 : ℝ)/5 := by linarith [hr.2]
  exact ⟨by linarith,hz0,hy0,hy,hyx,hxlo,hxhi,hzlower,hzupper,hzdiag,
    hc.1,hc.2.1,hc.2.2⟩

lemma side_D_hasDeriv (t : ℝ) : HasDerivAt D (-1) t := by
  convert (hasDerivAt_const t (Real.pi/6+19/24)).sub (hasDerivAt_id t) using 1 <;>
    first | rfl | ring

lemma side_Z_hasDeriv {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt Z (D t/Z t) t := by
  have hp := side_radicand_pos ht
  have hz := side_Z_pos ht
  have hd := ((hasDerivAt_const t (N*targetSq)).sub
    ((side_D_hasDeriv t).pow 2)).sqrt (ne_of_gt hp)
  convert hd using 1
  · rfl
  · change D t/Z t = (0-2*D t*(-1))/(2*Z t)
    field_simp
    ring

lemma side_X_hasDeriv {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt X (-Y t/Z t) t := by
  have hd := (((side_D_hasDeriv t).const_mul (3/4)).add
    ((side_Z_hasDeriv ht).div_const 3)).div_const N
  convert hd using 1
  · rfl
  · dsimp [Y,N]
    field_simp [ne_of_gt (side_Z_pos ht)]
    ring

lemma side_Y_hasDeriv {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt Y (X t/Z t) t := by
  have hd := (((side_D_hasDeriv t).neg.div_const 3).add
    ((side_Z_hasDeriv ht).const_mul (3/4))).div_const N
  convert hd using 1
  · rfl
  · dsimp [X,N]
    field_simp [ne_of_gt (side_Z_pos ht)]
    ring

lemma side_Yprime_hasDeriv {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt (fun y => X y/Z y) (-(39/16 : ℝ)/(Z t)^3) t := by
  have hc := side_circle_data ht
  have hcancel : Y t*Z t+X t*D t=(39 : ℝ)/16 := by
    rw [← hc.projection,← hc.perpendicular]
    nlinarith [hc.norm_sq]
  have hd := (side_X_hasDeriv ht).div (side_Z_hasDeriv ht) (ne_of_gt hc.z_pos)
  convert hd using 1
  · rfl
  · field_simp [ne_of_gt hc.z_pos]
    nlinarith

end SquaresInCircles.Seven.Human
