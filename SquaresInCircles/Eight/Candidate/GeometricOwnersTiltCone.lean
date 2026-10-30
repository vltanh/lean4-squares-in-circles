module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersDouble

/-!
# Eight squares: a forbidden `D` direction bounds the negative tilt

A forbidden `D → E` axis at mismatch at most `3/200` forces `a_E ≥ 39/40`; with the cone
`b_H ≥ a_H/2` of `H`, no axis of `E` separates `E → H` when `sin t ≤ -9/20` for the tilt `t`
(`forbidden_D_negative_tilt_bound`). With the large transverse coordinate of `A`
(`double_forbidden_transverse_bound`), this excludes the `G` axis `3` under two forbidden quarter
directions (`G_axis_three_double_forbidden_excluded`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

/-- On the closed half-angle chart `|z| ≤ 3/8`, the tilt `t = 2 arctan z` has `cos t ≥ 3/4`. -/
theorem half_angle_cos_three_quarters {z t : ℝ} (hz : |z| ≤ 3/8)
    (ht : t=2*Real.arctan z) : 3/4 ≤ Real.cos t := by
  have hid := half_angle_identities z
  have hd : 0 < 1+z^2 := by positivity
  have hzsq := pow_le_pow_left₀ (abs_nonneg z) hz 2
  rw [sq_abs] at hzsq
  rw [ht,hid.2]
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- On the closed box `39/40 ≤ a_E ≤ 283/200`, `b_E ≥ 0`, `1/2 ≤ a_H ≤ 283/200`, `b_H ≥ a_H/2`,
`3/4 ≤ c ≤ 1`, `9/20 ≤ r ≤ 1`, each of the four projections of `E → H` at the nominal angle, with
`c = cos t` and `r = -sin t`, is below `(1 + c + r)/2 - 3/100`. -/
theorem negative_E_axis_upper {aE bE aH bH c r : ℝ}
    (hEa : 39/40 ≤ aE) (hEu : aE ≤ 283/200) (hEb : 0 ≤ bE)
    (hHa : 1/2 ≤ aH) (hHu : aH ≤ 283/200) (hHb : aH/2 ≤ bH)
    (hcL : 3/4 ≤ c) (hcU : c ≤ 1) (hrL : 9/20 ≤ r) (hrU : r ≤ 1)
    (j : Fin 4) :
    ![aH*c-bH*r-bE,
      aH-aE*r-bE*c,
      aE*c-bE*r-bH,
      aE-aH*r-bH*c] j < (1+c+r)/2-3/100 := by
  have hc0 : 0 ≤ c := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hHb' : 1/4 ≤ bH := by linarith
  fin_cases j
  · have hprod := mul_le_mul_of_nonneg_right hHu (by linarith : 0 ≤ c-r/2)
    have hratio := mul_le_mul_of_nonneg_right hHb hr0
    norm_num
    nlinarith
  · have hprod := mul_le_mul_of_nonneg_right hEa hr0
    have hsign := mul_nonneg hEb hc0
    norm_num
    nlinarith
  · have hprod := mul_le_mul_of_nonneg_right hEu hc0
    have hsign := mul_nonneg hEb hr0
    norm_num
    nlinarith
  · have hprodA := mul_le_mul_of_nonneg_right hHa hr0
    have hprodB := mul_le_mul_of_nonneg_right hHb' hc0
    norm_num
    nlinarith

theorem nominal_E_negative_projection_formula {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) (j : Fin 4) :
    actualProjection C E j (nominalPhase t E) =
      ![C.a H*Real.cos t-C.b H*(-Real.sin t)-C.b E,
        C.a H-C.a E*(-Real.sin t)-C.b E*Real.cos t,
        C.a E*Real.cos t-C.b E*(-Real.sin t)-C.b H,
        C.a E-C.a H*(-Real.sin t)-C.b H*Real.cos t] j := by
  have hs := hc.signed_coordinates
  fin_cases j <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, E, H, G, hs, Dual.signs,
      Real.sin_add, Real.cos_add] <;> ring

/-- A forbidden `D → E` axis at mismatch at most `3/200` gives `sin t > -9/20` for the tilt `t`,
whatever the axis of `E`. The only error spent on `E → H` is its projection loss `2S`. -/
theorem forbidden_D_negative_tilt_bound {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C)
    (hS : mismatch F.theta ≤ 3/200)
    {jD : Fin 4} (hD : jD ∉ quarterOwners)
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) :
    -(9/20:ℝ) < Real.sin (tilt F.theta) := by
  by_contra! hsin
  have hDp := aligned_projection_loss F hq (by norm_num [D, charged]) jD hDsep
  rw [nominal_D_forbidden_projection hc _ hD] at hDp
  have hDloss := (delta_le_mismatch F.theta (i := D) (by norm_num [D, charged])).trans hS
  have hEa : 39/40 ≤ C.a E := by linarith [C.b_nonneg D]
  obtain ⟨p,hp⟩ := F.choose_owners
  have hEp := mixed_E_projection F hq (p E) (hp E)
    (ε := mismatch F.theta) hS le_rfl
  rw [nominal_E_negative_projection_formula hc] at hEp
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := by linarith
  have hs0 : Real.sin (tilt F.theta) ≤ 0 := by linarith
  have hwidth : pairWidth (nominalPhase (tilt F.theta) E) =
      (1+Real.cos (tilt F.theta)+(-Real.sin (tilt F.theta)))/2 := by
    simp [pairWidth, nominalPhase, E, G, zeroEdges, otherQuarterEdges,
      Real.sin_add, Real.cos_add, abs_of_nonneg hc0, abs_of_nonpos hs0]
  rw [hwidth] at hEp
  have hHb := (hc.cones hq H).2.2.1
  norm_num [Dual.lowerRatio, H] at hHb
  have hHb' : C.a H/2 ≤ C.b H := by
    simp only [H]
    linarith
  have hbound := negative_E_axis_upper hEa (canonical_bounds C hq E).2.1.le
    (C.b_nonneg E) (by have hh := (canonical_bounds C hq H).1; linarith)
    (canonical_bounds C hq H).2.1.le hHb'
    hcL (Real.cos_le_one _) (by linarith : 9/20 ≤ -Real.sin (tilt F.theta))
    (by linarith [Real.neg_one_le_sin (tilt F.theta)] : -Real.sin (tilt F.theta) ≤ 1)
    (p E)
  linarith

/-- A point of the corner disk at a level `q ≤ Q0` with `b ≥ 81/100` has `a ≤ 1`. -/
theorem large_transverse_primary_bound {a b q : ℝ} (hq : q ≤ Q0)
    (hb : 81/100 ≤ b) (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) : a ≤ 1 := by
  have hsupport := Dual.circle_linear_upper (a := a) (b := b)
    (C := 1) (D := 9/10) (μ := 1/3) (by norm_num) hcircle
  dsimp [Q0] at hq
  norm_num at hsupport
  linarith

theorem nominal_G_axis_three_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) :
    actualProjection C G 3 (nominalPhase t G) =
      C.a G-C.a A*Real.sin t-C.b A*Real.cos t := by
  have hs := hc.signed_coordinates
  simp [actualProjection, projection, projectionCoefficients, sinusoid,
    nominalPhase, zeroEdges, otherQuarterEdges, next, G, A, hs, Dual.signs,
    Real.sin_sub, Real.cos_sub]
  ring

/-- If `g ≤ 283/200`, `0 ≤ a ≤ 1` and `b ≥ 81/100`, then for a direction `(c, s)` with `c ≥ 3/4`
and `s > -9/20` the projection `g - a s - b c` of the `G` axis `3` stays below the threshold
`(1 + c + |s|)/2`, for either sign of `s`. -/
theorem large_transverse_G_three_excluded {g a b c s : ℝ}
    (hgu : g ≤ 283/200) (ha : 0 ≤ a) (hau : a ≤ 1) (hb : 81/100 ≤ b)
    (hc : 3/4 ≤ c) (hunit : c^2+s^2=1) (hs : -(9/20:ℝ) < s)
    (hprojection : (1+c+|s|)/2 ≤ g-a*s-b*c) : False := by
  have hc0 : 0 ≤ c := by linarith
  have hbprod := mul_le_mul_of_nonneg_right hb hc0
  rcases le_total 0 s with hs0 | hs0
  · have haprod := mul_nonneg ha hs0
    rw [abs_of_nonneg hs0] at hprojection
    nlinarith
  · have hr0 : 0 ≤ -s := by linarith
    have hrU : -s ≤ 9/20 := by linarith
    have hsquare := pow_le_pow_left₀ hr0 hrU 2
    have hcL : 89/100 ≤ c := by
      by_contra! hh
      have hsquare' := pow_le_pow_left₀ hc0 hh.le 2
      nlinarith
    have haprod := mul_le_mul_of_nonneg_right hau hr0
    rw [abs_of_nonpos hs0] at hprojection
    nlinarith

/-- With forbidden axes on `B → T` and `D → E` at mismatch at most `3/200`, the `G` axis `3` does
not separate `G → A`, whatever the axis of `E`. -/
theorem G_axis_three_double_forbidden_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200)
    {jB jD : Fin 4} (hB : jB ∉ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D)))
    (hGsep : (forwardAxis 3).Feasible (C.square G) (C.square (next G))) : False := by
  have hAb := double_forbidden_transverse_bound F hq hc hzero hS hB hD hBsep hDsep
  have hcorner : (C.a A+1/2)^2+(C.b A+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C A
  have hAa := large_transverse_primary_bound hq hAb hcorner
  have hsin := forbidden_D_negative_tilt_bound F hq hc hS hD hDsep
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hGp := mixed_G_projection F 3 hGsep
  rw [nominal_G_axis_three_projection hc] at hGp
  have hwidth : pairWidth (nominalPhase (tilt F.theta) G) =
      (1+Real.cos (tilt F.theta)+|Real.sin (tilt F.theta)|)/2 := by
    simp [pairWidth, nominalPhase, G, zeroEdges, otherQuarterEdges,
      Real.sin_sub, Real.cos_sub, abs_of_nonneg (by linarith : 0 ≤ Real.cos (tilt F.theta))]
  rw [hwidth] at hGp
  exact large_transverse_G_three_excluded (canonical_bounds C hq G).2.1.le
    (C.a_pos A).le hAa hAb hcL
    (by nlinarith [Real.sin_sq_add_cos_sq (tilt F.theta)]) hsin hGp

end SquaresInCircles.Eight.Candidate
