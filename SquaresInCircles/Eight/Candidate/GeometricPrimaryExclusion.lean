module

public import SquaresInCircles.Eight.Candidate.Geometry

/-!
# Whole-domain core-primary exclusions on zero-quarter edges

The full frame bound |delta| < 7/10 already forces a feasible primary-axis
separator's corresponding primary coordinate above one. Both core curves
have primary coordinate at most 7/12. These two complete state/axis classes
are therefore impossible before any computed mismatch contraction.

This module imports no generated data and uses no numerical subdivision.
It is an uncompiled source draft, as requested for PR #10.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate.Geometric

/-- Over the complete frame range, the rotated inward primary coordinate
cannot point outward.  The strict reserve comes from cos(t)-|sin(t)|. -/
theorem primary_margin_upper {X Y v t : ℝ} (hY : 0 ≤ Y) (hv : |v| ≤ Y)
    (ht : |t| ≤ 7/10) :
    X-Y*Real.cos t+v*Real.sin t-pairWidth t ≤ X-1-(11/200:ℝ)*Y := by
  obtain ⟨hc, hs⟩ := small_angle ht
  have hvSin : v*Real.sin t ≤ Y*|Real.sin t| := by
    calc
      v*Real.sin t ≤ |v*Real.sin t| := le_abs_self _
      _ = |v|*|Real.sin t| := abs_mul _ _
      _ ≤ Y*|Real.sin t| :=
        mul_le_mul_of_nonneg_right hv (abs_nonneg _)
  have hgap : 0 ≤ Real.cos t-|Real.sin t|-(11/200:ℝ) := by
    nlinarith
  have hp := mul_nonneg hY hgap
  have hw : 1 ≤ pairWidth t := by
    have hh := h_nonneg t
    dsimp [h] at hh
    dsimp [pairWidth]
    linarith
  nlinarith

theorem core_primary_upper {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hcore : C.kind i ≠ .outer) : C.a i ≤ 7/12 := by
  have hb := C.boundary i
  cases hk : C.kind i with
  | outer => exact (hcore hk).elim
  | coreSide =>
      simp [BoundaryState, hk] at hb
      exact hb.1.le
  | coreCorner =>
      simp [BoundaryState, hk] at hb
      by_contra! ha
      nlinarith [sq_nonneg (C.a i-7/12), sq_nonneg (C.b i-1/2)]

/-- A target-primary separator on a zero-quarter edge requires an outer
target with primary coordinate greater than one.  No bound on total
mismatch, radius, or tangent signs is used. -/
theorem zero_target_primary_requires_outer {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) {i : Vertex} (hi : i ∈ zeroEdges)
    (haxis : (forwardAxis 1).Feasible (C.square i) (C.square (next i))) :
    C.kind (next i)=.outer ∧ 1 < C.a (next i) := by
  have hφ : phi F.theta i=delta F.theta i := by
    simp only [zeroEdges, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp [phi, word]
  have hp := primary_margin_upper (C.a_pos i).le
    (show |C.sigma i*C.b i| ≤ C.a i by rw [signed_b_abs]; exact C.b_le_a i)
    (F.delta_small i).le
    (X := C.a (next i))
  have hm := (F.margin_nonneg_iff i 1).1 haxis
  simp only [margin, hφ] at hm
  simp [forwardMargin] at hm
  have ha : 1 < C.a (next i) := by nlinarith [C.a_pos i]
  refine ⟨?_, ha⟩
  by_contra hk
  have hc := core_primary_upper C (next i) hk
  linarith

/-- The source-primary analogue holds on the same full angle domain. -/
theorem zero_source_primary_requires_outer {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) {i : Vertex} (hi : i ∈ zeroEdges)
    (haxis : (forwardAxis 3).Feasible (C.square i) (C.square (next i))) :
    C.kind i=.outer ∧ 1 < C.a i := by
  have hφ : phi F.theta i=delta F.theta i := by
    simp only [zeroEdges, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> simp [phi, word]
  have hp := primary_margin_upper (C.a_pos (next i)).le
    (show |-C.sigma (next i)*C.b (next i)| ≤ C.a (next i) by
      rw [neg_mul, abs_neg, signed_b_abs]
      exact C.b_le_a (next i))
    (F.delta_small i).le (X := C.a i)
  have hm := (F.margin_nonneg_iff i 3).1 haxis
  simp only [margin, hφ] at hm
  simp [forwardMargin] at hm
  have ha : 1 < C.a i := by nlinarith [C.a_pos (next i)]
  refine ⟨?_, ha⟩
  by_contra hk
  have hc := core_primary_upper C i hk
  linarith

/-- The complete core/core zero-edge state region has its owner family
captured before the first coarse mismatch table is applied. -/
theorem zero_core_pair_owners {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    {i : Vertex} (hi : i ∈ zeroEdges)
    (hs : C.kind i ≠ .outer) (ht : C.kind (next i) ≠ .outer)
    (j : Fin 4) (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    j ∈ zeroOwners := by
  fin_cases j
  · norm_num [zeroOwners]
  · exact (ht (zero_target_primary_requires_outer F hi hj).1).elim
  · norm_num [zeroOwners]
  · exact (hs (zero_source_primary_requires_outer F hi hj).1).elim

end SquaresInCircles.Eight.Candidate.Geometric
