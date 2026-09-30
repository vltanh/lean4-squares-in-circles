module
public import SquaresInCircles.Six.Analytic.DiagonalCoreBounds
public import SquaresInCircles.Six.Analytic.EndpointReduction

@[expose] public section

/-!
# An affine transverse bound on the full high-diagonal interval

The scalar obstruction is concave: after the identity
(cos d+sin d)^2=1+sin(2d), its second derivative is a negative combination of
cos d+sin d and sin(2d), plus the small constant 2(17/100)^2. Thus only the
actual endpoints 1/2 and pi/4 are needed. Their strict reserves follow from
Taylor bounds and sqrt(2)>707/500, pi<22/7.

The result |bD|<31/100-17d/100 is a consequence of the actual OWN separator and
containment. It is not an extra hypothesis on the normalized model.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def highDepthCircle (d : ℝ) : ℝ :=
  1+(387/1000)^2-Q0+2*(387/1000)*(Real.cos d+Real.sin d)+
    (387/1000)^2*Real.sin (2*d)+(81/100-(17/100)*d)^2

private lemma highDepthCircle_identity (d : ℝ) : highDepthCircle d =
    (1+(387/1000)*(Real.cos d+Real.sin d))^2+(81/100-(17/100)*d)^2-Q0 := by
  dsimp [highDepthCircle]
  rw [Real.sin_two_mul]
  nlinarith only [Real.sin_sq_add_cos_sq d]

private lemma highDepthCircle_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) highDepthCircle := by
  let f' : ℝ → ℝ := fun x => 2*(387/1000)*(Real.cos x-Real.sin x)+
    2*(387/1000)^2*Real.cos (2*x)-2*(17/100)*(81/100-(17/100)*x)
  let f'' : ℝ → ℝ := fun x => -2*(387/1000)*(Real.sin x+Real.cos x)-
    4*(387/1000)^2*Real.sin (2*x)+2*(17/100)^2
  have hf (x : ℝ) : HasDerivAt highDepthCircle (f' x) x := by
    have htr := ((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul (2*(387/1000))
    have htwo := (((hasDerivAt_id x).const_mul 2).sin).const_mul ((387/1000)^2)
    have hsq := ((hasDerivAt_const x (81/100)).sub
      ((hasDerivAt_id x).const_mul (17/100))).pow 2
    convert ((htr.const_add (1+(387/1000)^2-Q0)).add htwo).add hsq using 1 <;>
      dsimp [highDepthCircle,f'] <;> ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have htr := ((Real.hasDerivAt_cos x).sub (Real.hasDerivAt_sin x)).const_mul (2*(387/1000))
    have htwo := (((hasDerivAt_id x).const_mul 2).cos).const_mul (2*(387/1000)^2)
    have hlin := ((hasDerivAt_const x (81/100)).sub
      ((hasDerivAt_id x).const_mul (17/100))).const_mul (-2*(17/100))
    convert (htr.add htwo).add hlin using 1 <;> dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/2) (Real.pi/4))
    (f' := f') (f'' := f'') (by dsimp [highDepthCircle]; fun_prop)
  · intro x _; exact (hf x).hasDerivWithinAt
  · intro x _; exact (hff x).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [h.1,h.2,Real.pi_pos])
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [h.1]) (by linarith [h.2,Real.pi_pos])
    have hs2 := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ 2*x by linarith [h.1]) (show 2*x ≤ Real.pi by linarith [h.2,Real.pi_pos])
    have hw := one_le_abs_cos_add_abs_sin x
    rw [abs_of_nonneg hc,abs_of_nonneg hs] at hw
    dsimp [f'']
    linarith

private lemma highDepthCircle_left : 0 < highDepthCircle (1/2) := by
  have hc := Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)
  have hs := Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)
  let L : ℝ := 1+(387/1000)*
    ((1-(1/2)^2/2+(1/2)^4/24-(1/2)^6/720)+
     ((1/2)-(1/2)^3/6+(1/2)^5/120-(1/2)^7/5040))
  have hL0 : 0 < L := by norm_num [L]
  have hL : L ≤ 1+(387/1000)*(Real.cos (1/2)+Real.sin (1/2)) := by
    dsimp [L]
    nlinarith only [hc,hs]
  have hprod := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ 1+(387/1000)*(Real.cos (1/2)+Real.sin (1/2))+L by linarith)
  rw [highDepthCircle_identity]
  norm_num [L,Q0] at hprod ⊢
  nlinarith only [hprod]

private lemma highDepthCircle_right : 0 < highDepthCircle (Real.pi/4) := by
  have hroot : (707:ℝ)/500 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hpi : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  let L : ℝ := 1+(387/1000)*(707/500)
  let T : ℝ := 81/100-(17/100)*(11/14)
  have hL0 : 0 < L := by norm_num [L]
  have hT0 : 0 < T := by norm_num [T]
  have hL : L ≤ 1+(387/1000)*Real.sqrt 2 := by dsimp [L]; linarith
  have hT : T ≤ 81/100-(17/100)*(Real.pi/4) := by dsimp [T]; linarith
  have hLs := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ 1+(387/1000)*Real.sqrt 2+L by linarith)
  have hTs := mul_nonneg (sub_nonneg.mpr hT)
    (show 0 ≤ 81/100-(17/100)*(Real.pi/4)+T by linarith)
  rw [highDepthCircle_identity,Real.cos_pi_div_four,Real.sin_pi_div_four]
  norm_num [L,T,Q0] at hLs hTs ⊢
  nlinarith only [hLs,hTs]

/-- One concavity argument covers the whole physical diagonal interval. -/
lemma high_diagonal_profile_circle {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    Q0 < (1+(387/1000)*(Real.cos d+Real.sin d))^2+(81/100-(17/100)*d)^2 := by
  have h := positive_on_concave_interval highDepthCircle_concave hd
    highDepthCircle_left highDepthCircle_right
  rw [highDepthCircle_identity] at h
  linarith

lemma high_diagonal_transverse_of_profile {a b d : ℝ}
    (hc : ContainedChart a |b|) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hprofile : 1+(387/1000)*(Real.cos d+Real.sin d) ≤ a+1/2) :
    |b| < 31/100-(17/100)*d := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hA0 : 0 ≤ 1+(387/1000)*(Real.cos d+Real.sin d) := by positivity
  have hB0 : 0 ≤ 81/100-(17/100)*d := by linarith [hd.2,Real.pi_lt_d2]
  by_contra! hb
  have hB : 81/100-(17/100)*d ≤ |b|+1/2 := by linarith
  have hAsq := mul_nonneg (sub_nonneg.mpr hprofile)
    (show 0 ≤ a+1/2+(1+(387/1000)*(Real.cos d+Real.sin d)) by linarith [hc.half_le])
  have hBsq := mul_nonneg (sub_nonneg.mpr hB)
    (show 0 ≤ |b|+1/2+(81/100-(17/100)*d) by linarith [abs_nonneg b])
  nlinarith [hc.containment,high_diagonal_profile_circle hd]

/-- A stronger consequence of the actual high-D OWN constraint. -/
theorem normalized_diagonal_transverse_affine {R : ℝ} (P : NormalizedPacking R) :
    |P.transverse 3| < 31/100-(17/100)*P.diagonalAngle := by
  have hd : 1/2 ≤ P.diagonalAngle ∧ P.diagonalAngle ≤ Real.pi/4 :=
    ⟨(normalized_diagonal_gt_half P).le,P.diagonal_angle_range.2⟩
  apply high_diagonal_transverse_of_profile (P.contained 3) hd
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show P.diagonalAngle∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  have hx : 387/1000 ≤ 1/2-P.center.1 := by
    have h := P.box.1.2
    dsimp [c0] at h
    linarith [rho0_upper]
  have hy : 387/1000 ≤ 1/2-P.center.2 := by
    have h := P.box.2.2
    dsimp [c0] at h
    linarith [rho0_upper]
  have hX := mul_nonneg (show 0 ≤ 1/2-P.center.1-387/1000 by linarith) hcos
  have hY := mul_nonneg (show 0 ≤ 1/2-P.center.2-387/1000 by linarith) hsin
  have hown := P.own_separator 3 P.diagonal_own
  have hphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  rw [hphase] at hown
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_add,Real.sin_pi_add,
    abs_neg,abs_of_nonneg hcos,abs_of_nonneg hsin] at hown
  nlinarith only [hown,hX,hY]

lemma normalized_diagonal_transverse_lt_nine_fortieths {R : ℝ} (P : NormalizedPacking R) :
    |P.transverse 3| < 9/40 := by
  have h := normalized_diagonal_transverse_affine P
  linarith [normalized_diagonal_gt_half P]

end SquaresInCircles.Six.Analytic
