module

public import SquaresInCircles.Eight.Owners.GA.Target.OuterData

/-!
# Eight squares: whole-feasible-interval curvature of the outer target scalar

The polynomial N is decreasing on the one displayed interval, and its
single right endpoint gives the complete positive curvature reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Outer
open FramePair FrameCircleArc

theorem D_bounds {u : ℝ} (hu : Domain u) :
    K u-1∈Icc (3/10:ℝ) (183/200) := by
  have hk := (K_bounds hu.1).1
  have ha := FrameLowArc.a0_bounds.2
  exact ⟨by linarith,by linarith [hu.2]⟩

theorem N_hasDerivAt (d : ℝ) :
    HasDerivAt N (-(4*d+1)*(Q0-(d+1)^2)) d := by
  have h1 : HasDerivAt (fun x : ℝ => Q0*(2*x^2+x)) (Q0*(2*(2*d)+1)) d := by
    have := ((((hasDerivAt_id' d).fun_pow 2).const_mul 2).fun_add (hasDerivAt_id' d)).const_mul Q0
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => x*(x+1)^3) ((d+1)^3+d*(3*(d+1)^2)) d := by
    have := (hasDerivAt_id' d).fun_mul (((hasDerivAt_id' d).add_const 1).fun_pow 3)
    exact this.congr_deriv (by ring)
  have h := (h1.const_sub (Q0*(1+P^2))).fun_add h2
  exact h.congr_deriv (by ring)

theorem N_derivative_negative {d : ℝ} (hd : d∈Icc (3/10:ℝ) (183/200)) :
    -(4*d+1)*(Q0-(d+1)^2)<0 := by
  have hrad : 0<Q0-(d+1)^2 := by
    have hh := pow_le_pow_left₀ (by linarith [hd.1] : 0≤d+1)
      (by linarith [hd.2] : d+1≤383/200) 2
    norm_num [Q0] at hh ⊢
    linarith
  exact mul_neg_of_neg_of_pos (by linarith [hd.1]) hrad

theorem N_antitone : AntitoneOn N (Icc (3/10:ℝ) (183/200)) :=
  antiOn_of_hasDeriv_nonpos
    (fun d _ => (N_hasDerivAt d).continuousAt.continuousWithinAt)
    (fun d _ => N_hasDerivAt d)
    (fun d hd => (N_derivative_negative (Ioo_subset_Icc_self hd)).le)

theorem N_endpoint : (2:ℝ)<N (183/200) := by
  have hp := P_bounds.1
  have hp2 : (49/100:ℝ)<P^2 := by nlinarith
  dsimp [N,Q0]
  nlinarith

theorem N_lower {u : ℝ} (hu : Domain u) : (2:ℝ)<N (K u-1) := by
  have hd := D_bounds hu
  exact N_endpoint.trans_le (N_antitone hd (by norm_num) hd.2)

theorem sine_cosine_upper (u : ℝ) : Real.sin u+Real.cos u<(71/50:ℝ) := by
  have hh := FrameCoreArc.projection_lt (a:=(1:ℝ)) (b:=(1:ℝ))
    (by norm_num : (0:ℝ)<71/50) (by norm_num) u
  simpa using hh

theorem curvature_lower {u : ℝ} (hu : Domain u) : (1/3:ℝ)<Jdd u := by
  have hy := Y_pos hu
  have hy3 := pow_lt_pow_left₀ (Y_bounds hu).2 hy.le (by norm_num : (3:ℕ)≠0)
  have hn := N_lower hu
  have hquot : (2/(3/2)^3:ℝ)<N (K u-1)/Y u^3 := by
    apply (div_lt_div_iff₀ (by norm_num) (pow_pos hy 3)).2
    nlinarith
  have hprod := mul_lt_mul_of_pos_left hquot (by norm_num [m] : 0 < m)
  have htr := sine_cosine_upper u
  dsimp [Jdd,m] at *
  norm_num at hprod
  rw [mul_div_assoc]
  linarith

end SquaresInCircles.Eight.GlobalGA.Target.Outer
