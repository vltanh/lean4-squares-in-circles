module

public import SquaresInCircles.Eight.Candidate.GeometricOwners

/-!
# Eight squares: three-edge chains on the quarter edges

On the quarter edges `B → T` and `D → E` the quarter owners `2` and `3` (`quarterOwners`) are the
intended axes, and `0` and `1` the forbidden ones. The chains of this file and of
`GeometricOwnersDouble.lean` to `GeometricOwnersMixed.lean` assume the tangent cuts
(`TangentCuts`), and the zero owners (`ZeroOwners`) when they pass through a zero edge. On an
aligned edge every separating axis has projection at least `1 - (3/2)|δᵢ|` at the nominal angle
(`aligned_projection_loss`), and the errors `|δᵢ|` of the aligned edges add up to the mismatch
`S`. An intended `B → T` axis, a zero owner on `T → D` and a forbidden `D → E` axis telescope: the
transverse coordinates cancel and `3 - (3/2) S ≤ a_B + a_E` (`quarter_telescoping_primary_bound`),
which containment forbids at mismatch at most `1/10` (`quarter_mixed_direction_excluded`). A
second chain, `G → A` on the axis `2`, `A → B` and a forbidden `B → T` axis, needs one circle
completion at the rotated corner of `G` and gives `5/2 - (3/2) S ≤ a_T + q/4`
(`G_axis_two_forbidden_quarter_bound`), impossible at mismatch at most `3/200`
(`G_axis_two_forbidden_quarter_excluded`). Each separating axis is treated on its own, and both
signs of the tilt are included.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

/-- On an aligned edge, a separating axis has projection at least `1 - (3/2)|δᵢ|` at the nominal
angle, with the frame difference `δᵢ` of the edge. -/
theorem aligned_projection_loss {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) {i : Vertex} (hi : i ∈ charged) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    1-(3/2)*|delta F.theta i| ≤
      actualProjection C i j (nominalPhase (tilt F.theta) i) := by
  have hp := actualProjection_feasible F i j hj
  have hw := width_one_le (phi F.theta i)
  have hl := actualProjection_lipschitz C hq i j
    (phi F.theta i) (nominalPhase (tilt F.theta) i)
  have hdiff : phi F.theta i - nominalPhase (tilt F.theta) i = delta F.theta i := by
    rw [GeometricOwners.phase_charged F hi, add_sub_cancel_left]
  rw [hdiff] at hl
  have hh := (abs_le.mp hl).2
  linarith

/-- Under the tangent cuts, a zero owner of a zero edge has projection `bᵢ + bᵢ₊₁` at the nominal
angle. -/
theorem nominal_zero_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {i : Vertex} (hi : i ∈ zeroEdges)
    {j : Fin 4} (hj : j ∈ zeroOwners) :
    actualProjection C i j (nominalPhase t i) = C.b i + C.b (next i) := by
  have hs := hc.signed_coordinates
  have hi' : i = 0 ∨ i = 2 ∨ i = 4 := by
    revert hi
    fin_cases i <;> decide
  have hj' : j = 0 ∨ j = 2 := by
    revert hj
    fin_cases j <;> decide
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, next, hs, Dual.signs] <;> ring

theorem nominal_B_intended_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {j : Fin 4} (hj : j ∈ quarterOwners) :
    actualProjection C B j (nominalPhase t B) = C.a B-C.b T := by
  have hs := hc.signed_coordinates
  fin_cases j <;> norm_num [quarterOwners] at hj <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, B, T, hs, Dual.signs] <;> ring

theorem nominal_D_forbidden_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {j : Fin 4} (hj : j ∉ quarterOwners) :
    actualProjection C D j (nominalPhase t D) = C.a E-C.b D := by
  have hs := hc.signed_coordinates
  fin_cases j <;> norm_num [quarterOwners] at hj <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, D, E, hs, Dual.signs] <;> ring

theorem nominal_B_forbidden_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {j : Fin 4} (hj : j ∉ quarterOwners) :
    actualProjection C B j (nominalPhase t B) = C.a T-C.b B := by
  have hs := hc.signed_coordinates
  fin_cases j <;> norm_num [quarterOwners] at hj <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, B, T, hs, Dual.signs] <;> ring

theorem nominal_G_axis_two_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) :
    actualProjection C G 2 (nominalPhase t G) =
      C.a G*Real.cos t-C.b G*Real.sin t-C.b A := by
  have hs := hc.signed_coordinates
  simp [actualProjection, projection, projectionCoefficients, sinusoid,
    nominalPhase, zeroEdges, otherQuarterEdges, next, G, A, hs, Dual.signs,
    Real.sin_sub, Real.cos_sub]
  ring

/-- An intended `B → T` axis, a zero owner of `T → D` and a forbidden `D → E` axis have the
projections `a_B - b_T`, `b_T + b_D` and `a_E - b_D`, whose transverse coordinates cancel, so
`3 - (3/2) S ≤ a_B + a_E`. The bound holds on the whole tilt chart and keeps the sum of the three
edge errors. -/
theorem quarter_telescoping_primary_bound {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    {jB jD : Fin 4} (hB : jB ∈ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) :
    3-(3/2)*mismatch F.theta ≤ C.a B+C.a E := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hT := hzero T (by norm_num [T, zeroEdges]) (p T) (hp T)
  have hBp := aligned_projection_loss F hq (by norm_num [B, charged]) jB hBsep
  have hTp := aligned_projection_loss F hq (by norm_num [T, charged]) (p T) (hp T)
  have hDp := aligned_projection_loss F hq (by norm_num [D, charged]) jD hDsep
  rw [nominal_B_intended_projection hc _ hB] at hBp
  rw [nominal_zero_projection hc _ (by norm_num [T, zeroEdges]) hT] at hTp
  rw [nominal_D_forbidden_projection hc _ hD] at hDp
  have hpartial : |delta F.theta B|+|delta F.theta T|+|delta F.theta D| ≤
      mismatch F.theta := by
    simp [mismatch, charged, B, T, D]
    linarith [abs_nonneg (delta F.theta 0), abs_nonneg (delta F.theta 2)]
  norm_num [T, D, next] at hTp
  simp only [B, T, D, E] at hBp hDp hpartial ⊢
  linarith

/-- An intended `B → T` axis and a forbidden `D → E` axis do not separate together at mismatch at
most `1/10`, also when other axes separate as well: at `S = 1/10` the span `a_B + a_E` is at least
`57/20`, while containment bounds it strictly by `283/100`. -/
theorem quarter_mixed_direction_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 1/10)
    {jB jD : Fin 4} (hB : jB ∈ quarterOwners) (hD : jD ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hDsep : (forwardAxis jD).Feasible (C.square D) (C.square (next D))) : False := by
  have hspan := quarter_telescoping_primary_bound F hq hc hzero hB hD hBsep hDsep
  have hBu := (canonical_bounds C hq B).2.1
  have hEu := (canonical_bounds C hq E).2.1
  linarith

/-- If `(1 + c + |s|)/2 + 2 - loss ≤ a c - b s + x` for a point `(a, b)` of the corner disk with
`b ≥ 0` and a direction `(c, s)` with `c ≥ 0`, then `5/2 - loss ≤ x + q/4`: one circle completion
with the weight `1/4`, on the closed right semicircle and for both signs of `s`. -/
theorem rotated_corner_primary_span {a b x q c s loss : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hunit : c^2+s^2=1)
    (hcircle : (a+1/2)^2+(b+1/2)^2 ≤ q)
    (hchain : (1+c+|s|)/2+2-loss ≤ a*c-b*s+x) :
    5/2-loss ≤ x+q/4 := by
  have hsupport := Dual.circle_linear_upper (a := a) (b := b)
    (C := c) (D := |s|) (μ := 1/4) (by norm_num) hcircle
  have hsign := mul_le_mul_of_nonneg_left (neg_le_abs s) hb
  have hwidth : 1 ≤ c+|s| := by
    by_contra hh
    have hh' : c+|s| < 1 := lt_of_not_ge hh
    have hproduct : 0 ≤ (1-c-|s|)*(c+|s|) :=
      mul_nonneg (by linarith) (add_nonneg hc (abs_nonneg s))
    nlinarith [sq_abs s, mul_nonneg hc (abs_nonneg s)]
  norm_num at hsupport
  nlinarith [sq_abs s]

/-- The projections on `G → A`, `A → B` and the forbidden `B → T` axis telescope. The rotated corner
of `G` needs one circle completion, with weight `1/4`. Nothing is assumed about `D`, `E` or the sign
of the tilt. -/
theorem G_axis_two_forbidden_quarter_bound {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    {jB : Fin 4} (hB : jB ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hGsep : (forwardAxis 2).Feasible (C.square G) (C.square (next G))) :
    5/2-(3/2)*mismatch F.theta ≤ C.a T+q/4 := by
  obtain ⟨p,hp⟩ := F.choose_owners
  have hA := hzero A (by norm_num [A, zeroEdges]) (p A) (hp A)
  have hAp := aligned_projection_loss F hq (by norm_num [A, charged]) (p A) (hp A)
  have hBp := aligned_projection_loss F hq (by norm_num [B, charged]) jB hBsep
  have hGp := mixed_G_projection F 2 hGsep
  rw [nominal_zero_projection hc _ (by norm_num [A, zeroEdges]) hA] at hAp
  rw [nominal_B_forbidden_projection hc _ hB] at hBp
  rw [nominal_G_axis_two_projection hc] at hGp
  have ht := abs_lt.mp F.tilt_small
  have hc0 : 0 ≤ Real.cos (tilt F.theta) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [ht.1, Real.pi_gt_three], by linarith [ht.2, Real.pi_gt_three]⟩
  have hwidth : pairWidth (nominalPhase (tilt F.theta) G) =
      (1+Real.cos (tilt F.theta)+|Real.sin (tilt F.theta)|)/2 := by
    simp [pairWidth, nominalPhase, G, zeroEdges, otherQuarterEdges,
      Real.sin_sub, Real.cos_sub, abs_of_nonneg hc0]
  rw [hwidth] at hGp
  have hpartial : |delta F.theta A|+|delta F.theta B| ≤ mismatch F.theta := by
    simp [mismatch, charged, A, B]
    linarith [abs_nonneg (delta F.theta 0), abs_nonneg (delta F.theta 4),
      abs_nonneg (delta F.theta 5)]
  norm_num [A, B, next] at hAp
  apply rotated_corner_primary_span (a := C.a G) (b := C.b G)
    (c := Real.cos (tilt F.theta)) (s := Real.sin (tilt F.theta))
    ((canonical_bounds C hq G).2.2.1) hc0
  · nlinarith [Real.sin_sq_add_cos_sq (tilt F.theta)]
  · simpa [SquaresInCircles.phi] using canonical_containment C G
  · simp only [A, B, T, G] at hBp hGp hpartial ⊢
    linarith

/-- The `G` axis `2` and a forbidden `B → T` axis do not separate together at mismatch at most
`3/200`, whatever the axes of the other edges: at `S = 3/200` the bound of
`G_axis_two_forbidden_quarter_bound` fails by `209/2500`. -/
theorem G_axis_two_forbidden_quarter_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) (hq : q ≤ Q0) (hc : TangentCuts C) (hzero : ZeroOwners C)
    (hS : mismatch F.theta ≤ 3/200)
    {jB : Fin 4} (hB : jB ∉ quarterOwners)
    (hBsep : (forwardAxis jB).Feasible (C.square B) (C.square (next B)))
    (hGsep : (forwardAxis 2).Feasible (C.square G) (C.square (next G))) : False := by
  have hspan := G_axis_two_forbidden_quarter_bound F hq hc hzero hB hBsep hGsep
  have hTu := (canonical_bounds C hq T).2.1
  dsimp [Q0] at hq
  linarith

end SquaresInCircles.Eight.Candidate
