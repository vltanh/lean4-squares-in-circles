module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersTiltCone

/-!
# Eight squares: both forbidden quarter directions are impossible

With forbidden axes on both `B → T` and `D → E` at mismatch at most `3/200`, the `G` axis `1` does
not separate (`G_axis_one_double_forbidden_excluded`). With `b_A ≥ 81/100`, a supporting line of
the circle of `A` gives `a_A ≤ 99/100`, which excludes a nonnegative tilt, and
`forbidden_D_negative_tilt_bound` gives `sin t > -9/20`. On the remaining arc four arguments, one
for each axis of `E`, finish: two complete the square in the circle of `H`, two telescope the
transverse coordinates, and the shared error is at most `7S/2` (`double_G_one_all_E_excluded`).
With the `G` axes `0`, `2` and `3` (`GeometricOwnersDouble.lean`, `GeometricOwnersQuarter.lean`,
`GeometricOwnersTiltCone.lean`), two forbidden quarter directions are impossible
(`double_forbidden_excluded`), and with `quarter_mixed_direction_excluded` every axis that
separates `D → E` at mismatch at most `3/200` is a quarter owner (`D_quarter_owners`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

/-- For a direction `(c, r)` of the unit circle with `c ≥ 3/4` and `0 ≤ r ≤ 9/20`: `7/8 ≤ c ≤ 1`,
`1 - c ≤ (8/15) r²` and `1 - c ≤ r/4`. -/
theorem short_negative_geometry {c r : ℝ} (hc : 3/4 ≤ c)
    (hr : 0 ≤ r) (hrU : r ≤ 9/20) (hunit : c^2+r^2=1) :
    7/8 ≤ c ∧ c ≤ 1 ∧ 1-c ≤ (8/15)*r^2 ∧ 1-c ≤ r/4 := by
  have hc0 : 0 ≤ c := by linarith
  have hrSq := pow_le_pow_left₀ hr hrU 2
  have hcL : 7/8 ≤ c := by
    by_contra! hh
    have hcSq := pow_le_pow_left₀ hc0 hh.le 2
    nlinarith
  have hcU : c ≤ 1 := by nlinarith [sq_nonneg r, sq_nonneg (c-1)]
  have hproduct := mul_nonneg (sub_nonneg.mpr hcU) (sub_nonneg.mpr hcL)
  have hchord : 1-c ≤ (8/15)*r^2 := by nlinarith
  have hrSq' := mul_le_mul_of_nonneg_right hrU hr
  exact ⟨hcL,hcU,hchord,by nlinarith⟩

theorem nominal_G_axis_one_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) :
    actualProjection C G 1 (nominalPhase t G) =
      C.a A-C.a G*Real.sin t-C.b G*Real.cos t := by
  have hs := hc.signed_coordinates
  simp [actualProjection, projection, projectionCoefficients, sinusoid,
    nominalPhase, zeroEdges, otherQuarterEdges, next, G, A, hs, Dual.signs,
    Real.sin_sub, Real.cos_sub]
  ring

/-- For the `G` axis `1` at a tilt with `c = cos t ≥ 3/4` and `0 ≤ r = -sin t ≤ 9/20`, with
`a_A ≤ 1` and `a_E ≥ 39/40`, no axis of `E` separates `E → H`. Two cases complete the square in
the circle of `H`, with the weight `1/3` and the forces `(c, c - r)` and `(1, c)`; the other two
telescope the transverse coordinates and use bounds on the primary coordinates. -/
theorem double_G_one_all_E_excluded
    {aA aG bG aH bH aE bE c r q ε : ℝ}
    (hq : q ≤ Q0) (hAa : aA ≤ 1) (hGa : aG ≤ 283/200)
    (hHa : 1/2 ≤ aH) (hEa : 39/40 ≤ aE) (hEu : aE ≤ 283/200) (hEb : 0 ≤ bE)
    (hcircle : (aH+1/2)^2+(bH+1/2)^2 ≤ q)
    (hc : 3/4 ≤ c) (hr : 0 ≤ r) (hrU : r ≤ 9/20) (hunit : c^2+r^2=1)
    (hε : 0 ≤ ε) (hεU : ε ≤ 3/200)
    (hG : (1+c+r)/2 ≤ aA+aG*r-bG*c)
    (hH : 1-(3/2)*ε ≤ bH+bG) (j : Fin 4)
    (hE : (1+c+r)/2-2*ε ≤
      ![aH*c-bH*r-bE,aH-aE*r-bE*c,aE*c-bE*r-bH,aE-aH*r-bH*c] j) : False := by
  obtain ⟨hcL,hcU,hchord,hlinear⟩ := short_negative_geometry hc hr hrU hunit
  have hc0 : 0 ≤ c := by linarith
  have hHc := mul_le_mul_of_nonneg_right hH hc0
  have hεc := mul_le_mul_of_nonneg_right hcU hε
  have hGprimary := mul_le_mul_of_nonneg_right hGa hr
  have hcr := mul_le_mul_of_nonneg_right hcL hr
  have hrSq := mul_le_mul_of_nonneg_right hrU hr
  dsimp [Q0] at hq
  fin_cases j
  · norm_num at hE
    have hsupport := Dual.circle_linear_upper (a := aH) (b := bH)
      (C := c) (D := c-r) (μ := 1/3) (by norm_num) hcircle
    have hdirection : 3 ≤ 3*c-(183/200)*r+(3/4)*r^2+(3/2)*c*r := by
      nlinarith only [hchord,hcr,hrSq,hr]
    norm_num at hsupport
    nlinarith only [hq,hAa,hGprimary,hHc,hεc,hG,hE,hEb,hdirection,hsupport,hunit,hεU]
  · norm_num at hE
    have hEprimary := mul_le_mul_of_nonneg_right hEa hr
    have hEsign := mul_nonneg hEb hc0
    have hsupport := Dual.circle_linear_upper (a := aH) (b := bH)
      (C := 1) (D := c) (μ := 1/3) (by norm_num) hcircle
    have hdirection : 5/2 ≤ (5/2)*c+(3/4)*r^2+(14/25)*r := by
      nlinarith only [hchord,hrSq,hr]
    norm_num at hsupport
    nlinarith only [hq,hAa,hGprimary,hEprimary,hEsign,hHc,hεc,hG,hE,
      hdirection,hsupport,hunit,hεU]
  · norm_num at hE
    have hEc := mul_le_mul_of_nonneg_right hE hc0
    have hEprimary := mul_le_mul_of_nonneg_right hEu (sq_nonneg c)
    have hEsign := mul_nonneg (mul_nonneg hEb hr) hc0
    have hdirection : 3 ≤ ((1+c+r)/2)*(1+c)+c := by
      nlinarith only [hlinear,hcr,hrSq,hr,hunit]
    have hprimary : c^2+r ≤ 5/4 := by nlinarith [sq_nonneg (r-1/2)]
    nlinarith only [hAa,hGprimary,hEprimary,hEsign,hG,hHc,hEc,hprimary,
      hdirection,hεc,hεU]
  · norm_num at hE
    have hHprimary := mul_le_mul_of_nonneg_right hHa hr
    nlinarith only [hAa,hEu,hGprimary,hHprimary,hG,hHc,hE,hεc,hεU,hcL,hr]

/-- A point of the corner disk at a level `q ≤ Q0` with `b ≥ 81/100` has `a ≤ 99/100`, which
excludes a nonnegative tilt for the `G` axis `1`. -/
theorem large_transverse_primary_ninety_nine {a b q : ℝ} (hq : q ≤ Q0)
    (hb : 81/100 ≤ b) (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q) : a ≤ 99/100 := by
  have hsupport := Dual.circle_linear_upper (a := a) (b := b)
    (C := 1) (D := 9/10) (μ := 1/3) (by norm_num) hcircle
  dsimp [Q0] at hq
  norm_num at hsupport
  linarith

/-- With forbidden axes on `B → T` and `D → E` at mismatch at most `3/200`, the `G` axis `1` does
not separate `G → A`, whatever the axis of `E`. -/
theorem G_axis_one_double_forbidden_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200)
    {jB jD : Fin 4} (hB : jB ∉ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D)))
    (hGsep : (forwardAxis 1).Feasible (C.square G) (C.square (next G))) : False := by
  have hAb := double_forbidden_transverse_bound F hq hc hzero hS hB hD hBsep hDsep
  have hAcorner : (C.a A+1/2)^2+(C.b A+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C A
  have hAa := large_transverse_primary_ninety_nine hq hAb hAcorner
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcL := half_angle_cos_three_quarters (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := by linarith
  have hGp := mixed_G_projection F 1 hGsep
  rw [nominal_G_axis_one_projection hc] at hGp
  have hsin : Real.sin (tilt F.theta) < 0 := by
    by_contra! hs0
    have hGa := mul_nonneg (C.a_pos G).le hs0
    have hGb := mul_nonneg (C.b_nonneg G) hc0
    have hwidth := width_one_le (nominalPhase (tilt F.theta) G)
    nlinarith
  have hrU := forbidden_D_negative_tilt_bound F hq hc hS hD hDsep
  obtain ⟨p,hp⟩ := F.choose_owners
  have hH := hzero H (by norm_num [H, zeroEdges]) (p H) (hp H)
  have hHp := aligned_coarse_projection F hq (by norm_num [H, charged])
    (p H) (hp H) (ε := mismatch F.theta) le_rfl
  rw [nominal_zero_projection hc _ (by norm_num [H, zeroEdges]) hH] at hHp
  have hEp := mixed_E_projection F hq (p E) (hp E)
    (ε := mismatch F.theta) hS le_rfl
  rw [nominal_E_negative_projection_formula hc] at hEp
  have hwidthG : pairWidth (nominalPhase (tilt F.theta) G) =
      (1+Real.cos (tilt F.theta)+(-Real.sin (tilt F.theta)))/2 := by
    simp [pairWidth, nominalPhase, G, zeroEdges, otherQuarterEdges,
      Real.sin_sub, Real.cos_sub, abs_of_nonneg hc0, abs_of_nonpos hsin.le]
  have hwidthE : pairWidth (nominalPhase (tilt F.theta) E) =
      (1+Real.cos (tilt F.theta)+(-Real.sin (tilt F.theta)))/2 := by
    simp [pairWidth, nominalPhase, E, G, zeroEdges, otherQuarterEdges,
      Real.sin_add, Real.cos_add, abs_of_nonneg hc0, abs_of_nonpos hsin.le]
  rw [hwidthG] at hGp
  rw [hwidthE] at hEp
  have hDp := aligned_projection_loss F hq (by norm_num [D, charged]) jD hDsep
  rw [nominal_D_forbidden_projection hc _ hD] at hDp
  have hDloss := (delta_le_mismatch F.theta (i := D) (by norm_num [D, charged])).trans hS
  have hEa : 39/40 ≤ C.a E := by linarith [C.b_nonneg D]
  have hHcorner : (C.a H+1/2)^2+(C.b H+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C H
  apply double_G_one_all_E_excluded (aA := C.a A) (aG := C.a G) (bG := C.b G)
    (aH := C.a H) (bH := C.b H) (aE := C.a E) (bE := C.b E)
    (c := Real.cos (tilt F.theta)) (r := -Real.sin (tilt F.theta))
    (j := p E)
    hq (by linarith) (canonical_bounds C hq G).2.1.le
    (by have hh := (canonical_bounds C hq H).1; linarith) hEa
    (canonical_bounds C hq E).2.1.le (C.b_nonneg E) hHcorner hcL
    (by linarith) (by linarith)
    (by nlinarith [Real.sin_sq_add_cos_sq (tilt F.theta)])
    (mismatch_nonneg F.theta) hS
  · nlinarith
  · simpa [H, G, next] using hHp
  · exact hEp

/-- Forbidden axes do not separate both `B → T` and `D → E` at mismatch at most `3/200`: no axis
would separate `G → A`. Each case assumes only that its own axis separates; other axes may
separate as well. -/
theorem double_forbidden_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200)
    {jB jD : Fin 4} (hB : jB ∉ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) : False := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hG := hp G
  revert hG
  generalize p G = g
  intro hG
  fin_cases g
  · exact G_axis_zero_double_forbidden_excluded F hq hc hzero hS hB hD hBsep hDsep hG
  · exact G_axis_one_double_forbidden_excluded F hq hc hzero hS hB hD hBsep hDsep hG
  · exact G_axis_two_forbidden_quarter_excluded F hq hc hzero hS hB hBsep hG
  · exact G_axis_three_double_forbidden_excluded F hq hc hzero hS hB hD hBsep hDsep hG

/-- At mismatch at most `3/200`, every axis that separates `D → E` is a quarter owner. A forbidden
axis is excluded even when another axis separates at the same time. -/
theorem D_quarter_owners {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200) (jD : Fin 4)
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) :
    jD ∈ quarterOwners := by
  by_contra hD
  obtain ⟨p,hp⟩ := F.choose_owners
  by_cases hB : p B ∈ quarterOwners
  · exact quarter_mixed_direction_excluded F hq hc hzero (by linarith)
      hB hD (hp B) hDsep
  · exact double_forbidden_excluded F hq hc hzero hS hB hD (hp B) hDsep

end SquaresInCircles.Eight.Candidate
