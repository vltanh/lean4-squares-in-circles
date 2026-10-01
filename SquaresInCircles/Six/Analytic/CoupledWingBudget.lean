import SquaresInCircles.Six.Analytic.CanonicalWestSign
import SquaresInCircles.Six.Analytic.EndpointReduction

/-!
# The angles of W and S on their own axes

If W and S are both separated from C along their own axes, at angles `w` and
`s`, then `s - w < 1`. The two separating inequalities share the centre of C,
and their sum gives
`a_W + a_S ≥ 1 + (387/1000)(cos v + cos s) + (61/100)(sin v + sin s)` with
`v = -w ≥ 0`. If `v + s ≥ 1`, both angles lie in `[1/3, 2/3]`, where the concave
function `1/2 + (387/1000) cos x + (61/100) sin x` exceeds `47/50 + (9/25) x`, by
its values at the ends; then `a_W + a_S > 2ρ0`, against `a_W, a_S ≤ ρ0`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def wingLineGap (x : ℝ) : ℝ :=
  1/2+(387/1000)*Real.cos x+(61/100)*Real.sin x-(47/50+(9/25)*x)

private lemma wingLineGap_concave :
    ConcaveOn ℝ (Set.Icc (1/3) (2/3)) wingLineGap := by
  let f' : ℝ → ℝ := fun x => -(387/1000)*Real.sin x+(61/100)*Real.cos x-9/25
  let f'' : ℝ → ℝ := fun x => -(387/1000)*Real.cos x-(61/100)*Real.sin x
  have hf (x : ℝ) : HasDerivAt wingLineGap (f' x) x := by
    have h := ((((Real.hasDerivAt_cos x).const_mul (387/1000)).add
      ((Real.hasDerivAt_sin x).const_mul (61/100))).const_add (1/2)).sub
      (((hasDerivAt_id x).const_mul (9/25)).const_add (47/50))
    convert h using 1
    · funext y; simp only [wingLineGap,Pi.sub_apply,Pi.add_apply,id]; ring
    · dsimp only [f']; ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    convert ((((Real.hasDerivAt_sin x).const_mul (-(387/1000))).add
      ((Real.hasDerivAt_cos x).const_mul (61/100))).sub_const (9/25)) using 1
    dsimp [f',f'']
    ring
  have hcont : ContinuousOn wingLineGap (Set.Icc (1/3) (2/3)) :=
    fun x _ => (hf x).continuousAt.continuousWithinAt
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (1/3) (2/3))
    (f' := f') (f'' := f'') hcont
  · intro x _; exact (hf x).hasDerivWithinAt
  · intro x _; exact (hff x).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [h.1,Real.pi_pos],by linarith [h.2,Real.pi_gt_d2]⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ x by linarith [h.1]) (by linarith [h.2,Real.pi_gt_d2])
    dsimp [f'']
    linarith

private lemma wingLineGap_endpoints : 0 < wingLineGap (1/3) ∧ 0 < wingLineGap (2/3) := by
  constructor
  · have hc := Seven.cos_lower_six (x := (1:ℝ)/3) (by norm_num)
    have hs := Seven.sin_lower_seven (x := (1:ℝ)/3) (by norm_num)
    dsimp [wingLineGap]
    nlinarith only [hc,hs]
  · have hc := Seven.cos_lower_six (x := (2:ℝ)/3) (by norm_num)
    have hs := Seven.sin_lower_seven (x := (2:ℝ)/3) (by norm_num)
    dsimp [wingLineGap]
    nlinarith only [hc,hs]

/-- On `[1/3, 2/3]` the radial profile of a wing lies above `47/50 + (9/25) x`. -/
lemma coupled_wing_affine_profile {x : ℝ} (hx : 1/3 ≤ x ∧ x ≤ 2/3) :
    47/50+(9/25)*x < 1/2+(387/1000)*Real.cos x+(61/100)*Real.sin x := by
  have h := positive_on_concave_interval wingLineGap_concave hx
    wingLineGap_endpoints.1 wingLineGap_endpoints.2
  dsimp [wingLineGap] at h
  linarith

private lemma wing_small_trig {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2/3) :
    7/9 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 2/3 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0 ≤ (2:ℝ)/3+x by linarith [hx.1])
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_d2])
  exact ⟨by nlinarith,hsin,(Real.sin_le hx.1).trans hx.2⟩

/-- The sum of the separating inequalities of W and S along their own axes, which
share the centre of C, bounds `a_W + a_S` below. -/
lemma coupled_own_wing_radial_sum {v s aw bw aS bS cx cy : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 2/3) (hs : 0 ≤ s ∧ s ≤ 2/3)
    (hx : cx ≤ c0) (hy : cy ≤ c0)
    (hW : 0 ≤ centralMargin .own (Real.pi-v) aw bw cx cy)
    (hS : 0 ≤ centralMargin .own (3*Real.pi/2+s) aS bS cx cy) :
    1+(387/1000)*(Real.cos v+Real.cos s)+(61/100)*(Real.sin v+Real.sin s) ≤ aw+aS := by
  obtain ⟨hcv,hsv0,hsv⟩ := wing_small_trig hv
  obtain ⟨hcs,hss0,hss⟩ := wing_small_trig hs
  have hcv0 : 0 ≤ Real.cos v := by linarith
  have hcs0 : 0 ≤ Real.cos s := by linarith
  have hX := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ Real.cos v-Real.sin s by linarith)
  have hY := mul_nonneg (sub_nonneg.mpr hy)
    (show 0 ≤ Real.cos s-Real.sin v by linarith)
  have hL : 387/1000 ≤ 1/2-c0 := by dsimp [c0]; linarith [rho0_upper]
  have hU : 61/100 ≤ 1/2+c0 := by dsimp [c0]; linarith [rho0_lower]
  have hC := mul_nonneg (sub_nonneg.mpr hL)
    (show 0 ≤ Real.cos v+Real.cos s by linarith)
  have hT := mul_nonneg (sub_nonneg.mpr hU) (add_nonneg hsv0 hss0)
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_sub,Real.sin_pi_sub,
    abs_neg,abs_of_nonneg hcv0,abs_of_nonneg hsv0] at hW
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
    south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,neg_neg,add_zero,abs_neg,
    abs_of_nonneg hcs0,abs_of_nonneg hss0] at hS
  nlinarith only [hW,hS,hX,hY,hC,hT]

/-- If W and S are both separated from C along their own axes, then
`s - w < 1`. -/
theorem normalized_own_wing_angle_sum {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    P.helperAngle 4-P.helperAngle 2 < 1 := by
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  have hv : 0 ≤ v ∧ v ≤ 2/3 := by
    have hneg := canonical_own_west_negative P hW
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hsupper : s ≤ 2/3 := P.helper_windows.2.2.2.2.le
  by_contra! hlarge
  have hsum : 1 ≤ v+s := by dsimp [v,s]; linarith
  have hvsmall : 1/3 ≤ v ∧ v ≤ 2/3 := ⟨by linarith,hv.2⟩
  have hssmall : 1/3 ≤ s ∧ s ≤ 2/3 := ⟨by linarith,hsupper⟩
  have hWphase : P.phase 2=Real.pi-v := by
    have hc : cardinalCenter (matchingCardinal 2)=Real.pi := rfl
    rw [P.phase_from_deviation 2,hc]; dsimp [v]; ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hrad := coupled_own_wing_radial_sum hv ⟨by linarith [hssmall.1],hsupper⟩
    P.box.1.2 P.box.2.2
    (by simpa only [hWphase] using P.own_separator 2 hW)
    (by simpa only [hSphase] using P.own_separator 4 hS)
  have hleft := coupled_wing_affine_profile hvsmall
  have hright := coupled_wing_affine_profile hssmall
  nlinarith [(P.contained 2).a_le_rho0,(P.contained 4).a_le_rho0,rho0_upper]

end SquaresInCircles.Six.Analytic
