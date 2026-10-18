module

public import SquaresInCircles.Eight.Candidate.GeometricOwnersQuarter

/-!
# Eight squares: two forbidden quarter directions and `G`-axis `0`

With forbidden axes on both `B → T` and `D → E`, two weighted three-edge chains and the circle of
`T` give `b_A ≥ 81/100` at mismatch at most `3/200` (`double_forbidden_transverse_bound`). One
supporting line of the circle of `A` then excludes `G`-axis `0` on the whole half-angle chart,
whatever the axis of `E` (`G_axis_zero_double_forbidden_excluded`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

/-- The weight `2/3` keeps the useful direction of the corner of `T`. The four aligned errors are
charged through their shared sum. -/
theorem double_forbidden_transverse_quantitative {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    {jB jD : Fin 4} (hB : jB ∉ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) :
    10/3-(3/2)*mismatch F.theta ≤ C.b A+(2/3)*C.a E+(3/10)*q+10/27 := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hA := hzero A (by norm_num [A, zeroEdges]) (p A) (hp A)
  have hT := hzero T (by norm_num [T, zeroEdges]) (p T) (hp T)
  have hAp := aligned_projection_loss F hq (by norm_num [A, charged]) (p A) (hp A)
  have hBp := aligned_projection_loss F hq (by norm_num [B, charged]) jB hBsep
  have hTp := aligned_projection_loss F hq (by norm_num [T, charged]) (p T) (hp T)
  have hDp := aligned_projection_loss F hq (by norm_num [D, charged]) jD hDsep
  rw [nominal_zero_projection hc _ (by norm_num [A, zeroEdges]) hA] at hAp
  rw [nominal_B_forbidden_projection hc _ hB] at hBp
  rw [nominal_zero_projection hc _ (by norm_num [T, zeroEdges]) hT] at hTp
  rw [nominal_D_forbidden_projection hc _ hD] at hDp
  have hpartial : |delta F.theta A|+|delta F.theta B|+
      (2/3)*|delta F.theta T|+(2/3)*|delta F.theta D| ≤ mismatch F.theta := by
    simp [mismatch, charged, A, B, T, D]
    linarith [abs_nonneg (delta F.theta 0), abs_nonneg (delta F.theta 4),
      abs_nonneg (delta F.theta 5)]
  have hcorner : (C.a T+1/2)^2+(C.b T+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C T
  have hsupport := Dual.circle_linear_upper (a := C.a T) (b := C.b T)
    (C := 1) (D := 2/3) (μ := 3/10) (by norm_num) hcorner
  norm_num [A, B, T, D, next] at hAp hTp
  simp only [A, B, T, D, E] at hBp hDp hpartial hsupport ⊢
  norm_num at hsupport
  linarith

theorem double_forbidden_transverse_bound {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200)
    {jB jD : Fin 4} (hB : jB ∉ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) :
    81/100 ≤ C.b A := by
  have hspan := double_forbidden_transverse_quantitative F hq hc hzero hB hD hBsep hDsep
  have hEu := (canonical_bounds C hq E).2.1
  dsimp [Q0] at hq
  linarith

/-- A rational cone containing the closed chart. At its endpoint the ratio is `48/55`, strictly
below `9/10`. -/
theorem half_angle_nine_tenths_cone {z t : ℝ} (hz : |z| ≤ 3/8)
    (ht : t=2*Real.arctan z) :
    0 ≤ Real.cos t ∧ |Real.sin t| ≤ (9/10)*Real.cos t := by
  have hid := half_angle_identities z
  have hd : 0 < 1+z^2 := by positivity
  have hzsq := pow_le_pow_left₀ (abs_nonneg z) hz 2
  rw [sq_abs] at hzsq
  constructor
  · rw [ht,hid.2]
    exact div_nonneg (by nlinarith) hd.le
  · rw [ht,hid.1,hid.2,abs_div,abs_mul,abs_of_pos hd]
    norm_num
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hd).mpr
    nlinarith

/-- One supporting line of the circle of `A` and one of the unit circle of directions. The geometric
reserve exceeds the whole aligned loss at `S = 3/200`. -/
theorem large_transverse_G_zero_loss {a b h q c s loss : ℝ}
    (hq : q ≤ Q0) (hb : 81/100 ≤ b) (hh : h ≤ 9/10)
    (hc : 0 ≤ c) (hunit : c^2+s^2=1) (hcone : |s| ≤ (9/10)*c)
    (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q)
    (hchain : (1+c+|s|)/2+1-loss ≤ a*c-b*s+h) :
    1/40 ≤ loss := by
  have hsupport := Dual.circle_linear_upper (a := a) (b := b)
    (C := 1) (D := 9/10) (μ := 1/3) (by norm_num) hcircle
  have hline : a+(9/10)*b ≤ 17127/10000 := by
    dsimp [Q0] at hq
    norm_num at hsupport
    linarith
  have hlinec := mul_le_mul_of_nonneg_right hline hc
  have htransverse := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hcone)
  have hsign := mul_le_mul_of_nonneg_left (neg_le_abs s) (by linarith : 0 ≤ b)
  have hunitcircle : ((c-1/2)+1/2)^2+((|s|-1/2)+1/2)^2 ≤ (1:ℝ) := by
    nlinarith [sq_abs s]
  have hdirection := Dual.circle_linear_upper (a := c-1/2) (b := |s|-1/2)
    (C := 4837/10000) (D := 31/100) (μ := 23/80) (by norm_num) hunitcircle
  norm_num at hdirection
  have hdirection' : (4837/10000)*c+(31/100)*|s| ≤ 23/40 := by
    linarith
  nlinarith

theorem nominal_G_axis_zero_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) :
    actualProjection C G 0 (nominalPhase t G) =
      -C.b G+C.a A*Real.cos t-C.b A*Real.sin t := by
  have hs := hc.signed_coordinates
  simp [actualProjection, projection, projectionCoefficients, sinusoid,
    nominalPhase, zeroEdges, otherQuarterEdges, next, G, A, hs, Dual.signs,
    Real.sin_sub, Real.cos_sub]
  ring

/-- This excludes four owner patterns at once, whatever the axis of `E` and the sign of the tilt. -/
theorem G_axis_zero_double_forbidden_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200)
    {jB jD : Fin 4} (hB : jB ∉ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D)))
    (hGsep : (forwardAxis 0).Feasible (C.square G) (C.square (next G))) : False := by
  have hAb := double_forbidden_transverse_bound F hq hc hzero hS hB hD hBsep hDsep
  obtain ⟨p,hp⟩ := F.choose_owners
  have hH := hzero H (by norm_num [H, zeroEdges]) (p H) (hp H)
  have hHp := aligned_projection_loss F hq (by norm_num [H, charged]) (p H) (hp H)
  have hGp := mixed_G_projection F 0 hGsep
  rw [nominal_zero_projection hc _ (by norm_num [H, zeroEdges]) hH] at hHp
  rw [nominal_G_axis_zero_projection hc] at hGp
  obtain ⟨z,hzl,hzu,ht⟩ := half_angle_chart F.tilt_small
  have hcone := half_angle_nine_tenths_cone (abs_le.mpr ⟨hzl.le,hzu.le⟩) ht
  have hwidth : pairWidth (nominalPhase (tilt F.theta) G) =
      (1+Real.cos (tilt F.theta)+|Real.sin (tilt F.theta)|)/2 := by
    simp [pairWidth, nominalPhase, G, zeroEdges, otherQuarterEdges,
      Real.sin_sub, Real.cos_sub, abs_of_nonneg hcone.1]
  rw [hwidth] at hGp
  have hHloss := delta_le_mismatch F.theta (i := H) (by norm_num [H, charged])
  have hHu := (canonical_bounds C hq H).2.2.2
  have hcorner : (C.a A+1/2)^2+(C.b A+1/2)^2 ≤ q := by
    simpa [SquaresInCircles.phi] using canonical_containment C A
  have hloss : 1/40 ≤ (3/2)*mismatch F.theta := by
    apply large_transverse_G_zero_loss (a := C.a A) (b := C.b A) (h := C.b H)
      hq hAb hHu.le hcone.1
      (by nlinarith [Real.sin_sq_add_cos_sq (tilt F.theta)]) hcone.2 hcorner
    norm_num [H, G, next] at hHp
    simp only [A, G, H] at hGp hHloss ⊢
    linarith
  linarith

end SquaresInCircles.Eight.Candidate
