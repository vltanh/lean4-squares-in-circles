import SquaresInCircles.Six.Analytic.CoupledWingBudget

/-!
# A sharper bound on the angles of W and S on their own axes

If W and S are both separated from C along their own axes, then `s - w < 24/25`.
With `v = -w`, if `v + s ≥ 24/25`, the windows `v, s ≤ 2/3` put both angles in
`[22/75, 2/3]`. There the concave function
`1/2 + (387/1000) cos x + (61/100) sin x` exceeds `941/1000 + (9/25) x`, by the
Taylor bounds at the ends, and the sum of the two separating inequalities
forces `a_W + a_S > 2ρ0`, against `a_W, a_S ≤ ρ0`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

private def coupledSharpGap (x : ℝ) : ℝ :=
  1/2+(387/1000)*Real.cos x+(61/100)*Real.sin x-
    (941/1000+(9/25)*x)

private lemma coupledSharpGap_concave :
    ConcaveOn ℝ (Set.Icc (22/75) (2/3)) coupledSharpGap := by
  let f' : ℝ → ℝ := fun x => -(387/1000)*Real.sin x+(61/100)*Real.cos x-9/25
  let f'' : ℝ → ℝ := fun x => -(387/1000)*Real.cos x-(61/100)*Real.sin x
  have hf (x : ℝ) : HasDerivAt coupledSharpGap (f' x) x := by
    have h := ((((Real.hasDerivAt_cos x).const_mul (387/1000)).add
      ((Real.hasDerivAt_sin x).const_mul (61/100))).const_add (1/2)).sub
      (((hasDerivAt_id x).const_mul (9/25)).const_add (941/1000))
    convert h using 1
    · funext y; simp only [coupledSharpGap,Pi.sub_apply,Pi.add_apply,id]; ring
    · dsimp only [f']; ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    convert ((((Real.hasDerivAt_sin x).const_mul (-(387/1000))).add
      ((Real.hasDerivAt_cos x).const_mul (61/100))).sub_const (9/25)) using 1
    dsimp [f',f'']
    ring
  have hcont : ContinuousOn coupledSharpGap (Set.Icc (22/75) (2/3)) :=
    fun x _ => (hf x).continuousAt.continuousWithinAt
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (22/75) (2/3))
    (f' := f') (f'' := f'') hcont
  · intro x _
    exact (hf x).hasDerivWithinAt
  · intro x _
    exact (hff x).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [h.1,Real.pi_pos],by linarith [h.2,Real.pi_gt_d2]⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ x by linarith [h.1]) (by linarith [h.2,Real.pi_gt_d2])
    dsimp [f'']
    linarith

private lemma coupledSharpGap_endpoints :
    0 < coupledSharpGap (22/75) ∧ 0 < coupledSharpGap (2/3) := by
  constructor
  · have hc := Seven.cos_lower_six (x := (22:ℝ)/75) (by norm_num)
    have hs := Seven.sin_lower_seven (x := (22:ℝ)/75) (by norm_num)
    dsimp [coupledSharpGap]
    nlinarith only [hc,hs]
  · have hc := Seven.cos_lower_six (x := (2:ℝ)/3) (by norm_num)
    have hs := Seven.sin_lower_seven (x := (2:ℝ)/3) (by norm_num)
    dsimp [coupledSharpGap]
    nlinarith only [hc,hs]

/-- On `[22/75, 2/3]` the radial profile of a wing lies above
`941/1000 + (9/25) x`. -/
lemma coupled_wing_sharp_affine_profile {x : ℝ}
    (hx : 22/75 ≤ x ∧ x ≤ 2/3) :
    941/1000+(9/25)*x <
      1/2+(387/1000)*Real.cos x+(61/100)*Real.sin x := by
  have h := positive_on_concave_interval coupledSharpGap_concave hx
    coupledSharpGap_endpoints.1 coupledSharpGap_endpoints.2
  dsimp [coupledSharpGap] at h
  linarith

/-- If W and S are both separated from C along their own axes, then
`s - w < 24/25`. -/
theorem normalized_own_wing_angle_sum_lt_twenty_four_twenty_fifths
    {R : ℝ} (P : NormalizedPacking R)
    (hW : P.ownBits 2=true) (hS : P.ownBits 4=true) :
    P.helperAngle 4-P.helperAngle 2 < 24/25 := by
  let v := -P.helperAngle 2
  let s := P.helperAngle 4
  have hv : 0 ≤ v ∧ v ≤ 2/3 := by
    have hneg := canonical_own_west_negative P hW
    dsimp [v]
    constructor <;> linarith [P.helper_windows.2.2.1.1]
  have hsupper : s ≤ 2/3 := P.helper_windows.2.2.2.2.le
  by_contra! hlarge
  have hsum : 24/25 ≤ v+s := by dsimp [v,s]; linarith
  have hvsmall : 22/75 ≤ v ∧ v ≤ 2/3 := ⟨by linarith,hv.2⟩
  have hssmall : 22/75 ≤ s ∧ s ≤ 2/3 := ⟨by linarith,hsupper⟩
  have hWphase : P.phase 2=Real.pi-v := by
    have hc : cardinalCenter (matchingCardinal 2)=Real.pi := rfl
    rw [P.phase_from_deviation 2,hc]
    dsimp [v]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+s := P.phase_from_deviation 4
  have hrad := coupled_own_wing_radial_sum hv ⟨by linarith [hssmall.1],hsupper⟩
    P.box.1.2 P.box.2.2
    (by simpa only [hWphase] using P.own_separator 2 hW)
    (by simpa only [hSphase] using P.own_separator 4 hS)
  have hleft := coupled_wing_sharp_affine_profile hvsmall
  have hright := coupled_wing_sharp_affine_profile hssmall
  have hWrad := (P.contained 2).a_le_rho0
  have hSrad := (P.contained 4).a_le_rho0
  linarith only [hrad,hleft,hright,hWrad,hSrad,rho0_upper,hsum]

end SquaresInCircles.Six.Analytic
