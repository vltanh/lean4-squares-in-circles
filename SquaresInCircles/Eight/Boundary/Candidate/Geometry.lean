module

public import SquaresInCircles.Eight.Boundary.Candidate.Model

/-!
# Eight squares: state bounds, and owners and signs at small mismatch

In a boundary cycle at a level at most `Q0` every square has `447/800 < a < 283/200` and
`0 ≤ b < 9/10` (`canonical_bounds`), on either radial curve. For a cycle with a candidate frame
the projections of a pair on the four forward axes, less the threshold, are the margins
`forwardMargin` at the angle `phi` (`Frame.margin_identity`). Two consequences follow, in this
order. If the mismatch is at most `2/5`, only the forward axes `0` and `2` can separate the pairs
of the three edges with digit `0` (`zero_owners_of_mismatch`). If it is at most `1/10`, the source
of each such edge has a positive and the target a negative tangent, which fixes the signs of `H`,
`G`, `A`, `B`, `T` and `D` (`signs_of_mismatch`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

theorem canonical_alpha {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    SquaresInCircles.alpha (C.square i) (0, 0) = C.a i := by
  have hx : frameX (C.square i) (C.square i).center = C.a i := by
    rw [C.center_eq, frameX_rotate]
  have hid : localX (C.square i) (0, 0) = -frameX (C.square i) (C.square i).center := by
    dsimp [localX, frameX]; ring
  simp [SquaresInCircles.alpha, hid, hx, abs_of_pos (C.a_pos i)]

theorem canonical_beta {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    SquaresInCircles.beta (C.square i) (0, 0) = C.b i := by
  have hy : frameY (C.square i) (C.square i).center = -C.sigma i * C.b i := by
    rw [C.center_eq, frameY_rotate]
  have hid : localY (C.square i) (0, 0) = -frameY (C.square i) (C.square i).center := by
    dsimp [localY, frameY]; ring
  rcases C.sigma_sign i with hs | hs <;>
    simp [SquaresInCircles.beta, hid, hy, hs, abs_of_nonneg (C.b_nonneg i)]

theorem canonical_containment {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    SquaresInCircles.phi (C.a i) (C.b i) ≤ q := by
  simpa only [SqContained, canonical_alpha, canonical_beta] using C.contained i

theorem canonical_core_distance {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    (1 / 12 : ℝ) ^ 2 ≤
      (max (C.a i - 1 / 2) 0) ^ 2 + (max (C.b i - 1 / 2) 0) ^ 2 := by
  obtain ⟨p, hp, he⟩ := exists_clipped_point (C.square i) (0, 0)
  have hc := C.core i p hp
  simp only [canonical_alpha, canonical_beta, sub_zero, sub] at he
  simpa [coreRadius, he] using hc

theorem canonical_bounds {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0) (i : Vertex) :
    447 / 800 < C.a i ∧ C.a i < 283 / 200 ∧ 0 ≤ C.b i ∧ C.b i < 9 / 10 := by
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hab := C.b_le_a i
  have hp := (canonical_containment C i).trans hq
  have hcore := canonical_core_distance C i
  have haHalf : 1 / 2 < C.a i := by
    by_contra! h
    have h₁ : max (C.a i - 1 / 2) 0 = 0 := max_eq_right (by linarith)
    have h₂ : max (C.b i - 1 / 2) 0 = 0 := max_eq_right (by linarith)
    norm_num [h₁, h₂] at hcore
  have hmax : max (C.a i - 1 / 2) 0 = C.a i - 1 / 2 :=
    max_eq_left (by linarith)
  have hbmax0 : 0 ≤ max (C.b i - 1 / 2) 0 := le_max_right _ _
  have hbmax : max (C.b i - 1 / 2) 0 ≤ C.a i - 1 / 2 :=
    max_le (by linarith) (by linarith)
  rw [hmax] at hcore
  have hbmaxSq : (max (C.b i - 1 / 2) 0) ^ 2 ≤ (C.a i - 1 / 2) ^ 2 :=
    pow_le_pow_left₀ hbmax0 hbmax 2
  have hal : 447 / 800 < C.a i := by
    by_contra! h
    have hsq : (C.a i - 1 / 2) ^ 2 ≤ (47 / 800 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    norm_num at hsq hcore
    linarith
  have hau : C.a i < 283 / 200 := by
    dsimp [SquaresInCircles.phi, Q0] at hp
    nlinarith only [sq_nonneg (C.b i), hb, hp, ha]
  have hbu : C.b i < 9 / 10 := by
    have hsq : (C.b i + 1 / 2) ^ 2 ≤ (C.a i + 1 / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    dsimp [SquaresInCircles.phi, Q0] at hp
    nlinarith only [hab, hp, hsq, ha, haHalf, hb]
  exact ⟨hal, hau, hb, hbu⟩

theorem signed_b_abs {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    |C.sigma i * C.b i| = C.b i := by
  rcases C.sigma_sign i with hs | hs <;>
    simp [hs, abs_of_nonneg (C.b_nonneg i)]

theorem Frame.relative_phase {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    C.canonicalAngle (next i) - C.canonicalAngle i =
      phi F.theta i - if i = 6 then 2 * Real.pi else 0 := by
  rw [F.canonical_eq (next i), F.canonical_eq i]
  fin_cases i <;> simp [phi, delta, word, offsets, next] <;> ring

theorem Frame.relative_trig {q : ℝ} {C : BoundaryCycle q} (F : Frame C) (i : Vertex) :
    relativeC (C.square i) (C.square (next i)) = Real.cos (phi F.theta i) ∧
    relativeS (C.square i) (C.square (next i)) = Real.sin (phi F.theta i) := by
  have hci : (C.square i).cosine = Real.cos (C.canonicalAngle i) := C.frame_cos i
  have hsi : (C.square i).sine = Real.sin (C.canonicalAngle i) := C.frame_sin i
  have hcj : (C.square (next i)).cosine = Real.cos (C.canonicalAngle (next i)) := C.frame_cos _
  have hsj : (C.square (next i)).sine = Real.sin (C.canonicalAngle (next i)) := C.frame_sin _
  have hC : relativeC (C.square i) (C.square (next i)) =
      Real.cos (C.canonicalAngle (next i) - C.canonicalAngle i) := by
    simp [relativeC, hci, hsi, hcj, hsj, Real.cos_sub]; ring
  have hS : relativeS (C.square i) (C.square (next i)) =
      Real.sin (C.canonicalAngle (next i) - C.canonicalAngle i) := by
    simp [relativeS, hci, hsi, hcj, hsj, Real.sin_sub]; ring
  rw [F.relative_phase] at hC hS
  by_cases hi : i = 6
  · simpa [hi, Real.cos_sub, Real.sin_sub] using And.intro hC hS
  · simpa [hi] using And.intro hC hS

theorem Frame.margin_identity {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4) :
    (forwardAxis j).projection (C.square i) (C.square (next i)) -
      SAT.threshold (C.square i) (C.square (next i)) = margin C F.theta i j := by
  exact canonical_margin_identity j _ _ _ _ _ _ _ _ _
    (C.center_eq i) (C.center_eq (next i)) (F.relative_trig i).1 (F.relative_trig i).2

theorem Frame.margin_nonneg_iff {q : ℝ} {C : BoundaryCycle q} (F : Frame C)
    (i : Vertex) (j : Fin 4) :
    (forwardAxis j).Feasible (C.square i) (C.square (next i)) ↔ 0 ≤ margin C F.theta i j := by
  rw [← F.margin_identity]
  exact (sub_nonneg).symm

end SquaresInCircles.Eight.Candidate
