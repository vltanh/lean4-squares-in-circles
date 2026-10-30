module

public import SquaresInCircles.Eight.Candidate.Geometry

/-!
# Eight squares: primary axes against core squares on zero edges

On an edge with the digit `0` the relative frame angle is the frame difference `t`, with
`|t| < 7/10`, where `cos t - |sin t| ≥ 11/200`. So if the primary axis `+e` of the target
separates the pair, the primary coordinate of the target exceeds `1` (`primary_margin_upper`),
and likewise for the axis `-e` of the source and the source. A square on a core curve has primary
coordinate at most `7/12` (`core_primary_upper`), so on a zero edge these axes need an outer
target or an outer source (`zero_target_primary_requires_outer`,
`zero_source_primary_requires_outer`), for every frame and at every radius. The pair tables leave
these axes out (`Arithmetic/AffineCoverage.lean`, `WordGeometry.lean`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate.Geometric

/-- For `|t| ≤ 7/10` and `|v| ≤ Y`, the margin `X - Y cos t + v sin t - pairWidth t` of a primary
axis is at most `X - 1 - (11/200) Y`: the threshold is at least `1`, and
`cos t - |sin t| ≥ 11/200`. -/
theorem primary_margin_upper {X Y v t : ℝ} (hY : 0 ≤ Y) (hv : |v| ≤ Y)
    (ht : |t| ≤ 7/10) :
    X-Y*Real.cos t+v*Real.sin t-pairWidth t ≤ X-1-(11/200:ℝ)*Y := by
  obtain ⟨hc, hs⟩ := small_angle ht
  have hvSin : v*Real.sin t ≤ Y*|Real.sin t| := by
    calc
      v*Real.sin t ≤ |v*Real.sin t| := le_abs_self _
      _ = |v| * |Real.sin t| := abs_mul _ _
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

/-- A square on a core curve has primary coordinate at most `7/12`. -/
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

/-- On a zero edge of a candidate frame, if the primary axis `+e` of the target separates, the
target is outer with primary coordinate above `1`. No bound on the mismatch, the radius or the
signs is used. -/
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

/-- Likewise, if the axis `-e` of the source separates, the source is outer with primary
coordinate above `1`. -/
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

end SquaresInCircles.Eight.Candidate.Geometric
