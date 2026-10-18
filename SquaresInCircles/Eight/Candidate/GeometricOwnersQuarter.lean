module

public import SquaresInCircles.Eight.Candidate.GeometricOwners

/-!
# A three-edge geometric exclusion of a whole quarter-owner class

An intended B-to-T separator, a zero-edge T-to-D separator, and a
forbidden D-to-E separator telescope to a primary-coordinate span three.
Containment makes that span impossible even at mismatch at most 1/10.
The argument treats each feasible signed axis separately and does not
depend on either mixed owner or on the sign of the tilt.
This source is uncompiled and imports no generated owner table.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

/-- The actual loss on this edge, before replacing it by any global budget. -/
theorem aligned_projection_loss {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (hq : q ≤ Q0) {i : Vertex} (hi : i ∈ charged) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    1-(3/2)*|delta F.theta i| ≤
      actualProjection C i j (nominalPhase (tilt F.theta) i) := by
  have hp := actualProjection_feasible F i j hj
  have hw := width_one_le (phi F.theta i)
  have hl := actualProjection_lipschitz C hq i j
    (phi F.theta i) (nominalPhase (tilt F.theta) i)
  rw [phase_decomposition F, if_pos hi, add_sub_cancel_left] at hl
  have hh := (abs_le.mp hl).2
  linarith

theorem nominal_zero_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {i : Vertex} (hi : i ∈ zeroEdges)
    {j : Fin 4} (hj : j ∈ zeroOwners) :
    actualProjection C i j (nominalPhase t i) = C.b i + C.b (next i) := by
  have hs := hc.signed_coordinates
  fin_cases i <;> fin_cases j <;>
    norm_num [zeroEdges, zeroOwners] at hi hj ⊢ <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, G, hs, Dual.signs] <;> ring

theorem nominal_B_intended_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {j : Fin 4} (hj : j ∈ quarterOwners) :
    actualProjection C B j (nominalPhase t B) = C.a B-C.b T := by
  have hs := hc.signed_coordinates
  fin_cases j <;> norm_num [quarterOwners] at hj ⊢ <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, B, T, G, hs, Dual.signs] <;> ring

theorem nominal_D_forbidden_projection {q : ℝ} {C : BoundaryCycle q}
    (hc : TangentCuts C) (t : ℝ) {j : Fin 4} (hj : j ∉ quarterOwners) :
    actualProjection C D j (nominalPhase t D) = C.a E-C.b D := by
  have hs := hc.signed_coordinates
  fin_cases j <;> norm_num [quarterOwners] at hj ⊢ <;>
    simp [actualProjection, projection, projectionCoefficients, sinusoid,
      nominalPhase, zeroEdges, otherQuarterEdges, next, D, E, G, hs, Dual.signs] <;> ring

/-- Both transverse coordinates cancel. The bound is uniform over the
entire tilt chart and retains the true sum of the three edge errors. -/
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
    simp [mismatch, charged, H, A, B, T, D] <;>
      linarith [abs_nonneg (delta F.theta 0), abs_nonneg (delta F.theta 2)]
  norm_num [T, D, next] at hTp
  simp only [B, T, D, E] at hBp hDp hpartial ⊢
  linarith

/-- Every owner pair in the class is excluded, including simultaneous
feasible axes. At the endpoint S=1/10 the span is at least 57/20,
whereas containment gives a strict upper bound 283/100. -/
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

end SquaresInCircles.Eight.Candidate
