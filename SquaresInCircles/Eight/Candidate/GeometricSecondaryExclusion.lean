module

public import SquaresInCircles.Eight.Candidate.GeometricPrimaryExclusion

/-!
# Eight squares: secondary axes against core squares

A core square has `a ≤ 7/12` and `|σ b| ≤ a`, so its centre `(a, -σ b)` in its canonical frame
lies in the disk of radius `5/6`, and the projection of that point on every unit direction is at
most `5/6` (`core_projection_bound`), while the threshold `pairWidth` is at least `1`. So the
secondary axis `+f` of the source does not separate it from a core target when `σ b ≤ 0`
(`target_core_secondary_margin`), and the secondary axis `+f` of the target does not separate a
core source from it when `τ B ≥ 0` (`source_core_secondary_margin`), at every angle and at every
radius; `source_secondary_excluded_of_target_core` and `target_secondary_excluded_of_source_core`
state this for a candidate frame. The pair tables leave these axes out
(`Arithmetic/AffineCoverage.lean`, `Boundary/Pairs.lean`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate.Geometric

/-- If `0 ≤ a ≤ 7/12` and `|v| ≤ a`, then `|a sin t + v cos t| ≤ 5/6` for every `t`: the point
`(a, v)` lies in the disk of radius `5/6`. -/
theorem core_projection_bound {a v : ℝ} (ha : 0 ≤ a) (hau : a ≤ 7/12)
    (hv : |v| ≤ a) (t : ℝ) :
    |a*Real.sin t+v*Real.cos t| ≤ 5/6 := by
  have ha₂ := pow_le_pow_left₀ ha hau 2
  have hv₂ : v^2 ≤ a^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg v) hv 2
  have hid : (a*Real.sin t+v*Real.cos t)^2+
      (a*Real.cos t-v*Real.sin t)^2=a^2+v^2 := by
    linear_combination (a^2+v^2) * Real.sin_sq_add_cos_sq t
  have hh := sq_nonneg (a*Real.cos t-v*Real.sin t)
  have habs := abs_nonneg (a*Real.sin t+v*Real.cos t)
  rw [← sq_abs (a*Real.sin t+v*Real.cos t)] at hid
  nlinarith

/-- The margin of the secondary axis `+f` of the source is negative, at every angle, when
`σ b ≤ 0`, `0 ≤ A ≤ 7/12` and `|τ B| ≤ A`. -/
theorem target_core_secondary_margin {a b A B σ τ t : ℝ}
    (hsource : σ*b ≤ 0) (hA : 0 ≤ A) (hcore : A ≤ 7/12)
    (htarget : |τ*B| ≤ A) :
    forwardMargin 0 a b A B σ τ t < 0 := by
  have hp := core_projection_bound hA hcore
    (v := -(τ*B)) (by simpa only [abs_neg] using htarget) t
  have hproj := (le_abs_self (A*Real.sin t+(-(τ*B))*Real.cos t)).trans hp
  have hw : 1 ≤ pairWidth t := by
    have hh := h_nonneg t
    dsimp [h] at hh
    dsimp [pairWidth]
    linarith
  simp [forwardMargin]
  nlinarith

/-- The margin of the secondary axis `+f` of the target is negative, at every angle, when
`τ B ≥ 0`, `0 ≤ a ≤ 7/12` and `|σ b| ≤ a`. -/
theorem source_core_secondary_margin {a b A B σ τ t : ℝ}
    (htarget : 0 ≤ τ*B) (ha : 0 ≤ a) (hcore : a ≤ 7/12)
    (hsource : |σ*b| ≤ a) :
    forwardMargin 2 a b A B σ τ t < 0 := by
  have hp := core_projection_bound ha hcore hsource t
  have hproj := (le_abs_self (a*Real.sin t+(σ*b)*Real.cos t)).trans hp
  have hw : 1 ≤ pairWidth t := by
    have hh := h_nonneg t
    dsimp [h] at hh
    dsimp [pairWidth]
    linarith
  simp [forwardMargin]
  nlinarith

/-- On a candidate frame, the secondary axis `+f` of the source does not separate the edge `i` when
the target has primary coordinate at most `7/12` and the source has `σ b ≤ 0`. -/
theorem source_secondary_excluded_of_target_core {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) {i : Vertex} (hcore : C.a (next i) ≤ 7/12)
    (hsource : C.sigma i*C.b i ≤ 0) :
    ¬ (forwardAxis 0).Feasible (C.square i) (C.square (next i)) := by
  intro hj
  have hn := target_core_secondary_margin (a := C.a i) hsource
    (C.a_pos (next i)).le hcore
    (show |C.sigma (next i)*C.b (next i)| ≤ C.a (next i) by
      rw [signed_b_abs]
      exact C.b_le_a (next i))
    (t := phi F.theta i)
  have hm := (F.margin_nonneg_iff i 0).1 hj
  change 0 ≤ forwardMargin 0 (C.a i) (C.b i) (C.a (next i))
    (C.b (next i)) (C.sigma i) (C.sigma (next i)) (phi F.theta i) at hm
  linarith

/-- On a candidate frame, the secondary axis `+f` of the target does not separate the edge `i` when
the source has primary coordinate at most `7/12` and the target has `τ B ≥ 0`. -/
theorem target_secondary_excluded_of_source_core {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) {i : Vertex} (hcore : C.a i ≤ 7/12)
    (htarget : 0 ≤ C.sigma (next i)*C.b (next i)) :
    ¬ (forwardAxis 2).Feasible (C.square i) (C.square (next i)) := by
  intro hj
  have hn := source_core_secondary_margin (A := C.a (next i)) htarget
    (C.a_pos i).le hcore
    (show |C.sigma i*C.b i| ≤ C.a i by
      rw [signed_b_abs]
      exact C.b_le_a i)
    (t := phi F.theta i)
  have hm := (F.margin_nonneg_iff i 2).1 hj
  change 0 ≤ forwardMargin 2 (C.a i) (C.b i) (C.a (next i))
    (C.b (next i)) (C.sigma i) (C.sigma (next i)) (phi F.theta i) at hm
  linarith

end SquaresInCircles.Eight.Candidate.Geometric
