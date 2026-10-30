module

public import SquaresInCircles.Eight.Candidate.GeometricSecondaryExclusion
public import SquaresInCircles.Eight.Frames

/-!
# Eight squares: quarter edges between core squares of opposite signs

On a quarter edge `φ = π/2 + d` from a core square with transverse sign `+1` to one with sign
`-1`, the gap `π/2 + d + arctan (b / a) + arctan (B / A)` is below `7/4`, a bound of every gap of
a cycle (`cycle_gap_lt_seven_quarters`). Since `arctan x ≥ (3/4) x` on `[0, 1]`, a core
transverse coordinate is at most `7/9` of its angle, so `b + B ≤ (7/9)(1/5 - d)`, and then no
forward axis separates the pair, on the whole frame range `|d| ≤ 7/10`
(`core_quarter_opposite_margin`, `quarter_core_opposite_excluded`). The pair tables leave these
pairs out: the word tables through `WordGeometry.original_not_core_excluded`, the affine tables
through `ExcludedArcs` (`Arithmetic/AffineCoverage.lean`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Candidate.Geometric

/-- `arctan x ≥ (3/4) x` on `[0, 1]`: `arctan` is concave there, so it lies above its chord, of
slope `π/4 > 3/4`. -/
theorem arctan_chord {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : (3/4:ℝ)*x ≤ Real.arctan x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) 1) Real.arctan :=
    concave_of_deriv2 (fun y _ => Real.hasDerivAt_arctan y)
      (fun y _ => (hasDerivAt_const y (1:ℝ)).div ((hasDerivAt_pow 2 y).const_add 1)
        (by positivity))
      (fun y hy => div_nonpos_of_nonpos_of_nonneg (by norm_num; linarith [hy.1]) (by positivity))
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show 0 ≤ 1-x by linarith [hx.2]) hx.1 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.arctan_zero, Real.arctan_one] at h
  nlinarith [Real.pi_gt_three]

/-- A core transverse coordinate is at most `7/9` of its angle: `b ≤ (7/9) arctan (b / a)` when
`0 ≤ b ≤ a ≤ 7/12`. -/
theorem core_transverse_le_angle {a b : ℝ} (ha : 0 < a) (hau : a ≤ 7/12) (hb : 0 ≤ b)
    (hab : b ≤ a) : b ≤ (7/9:ℝ)*Real.arctan (b/a) := by
  have h := arctan_chord ⟨div_nonneg hb ha.le, (div_le_one ha).mpr hab⟩
  have he : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
  nlinarith [mul_le_mul_of_nonneg_right hau (div_nonneg hb ha.le)]

/-- Every square avoids the core disk, so its primary coordinate exceeds `1/2`. -/
theorem canonical_primary_gt_half {q : ℝ} (C : BoundaryCycle q) (i : Vertex) : 1/2 < C.a i := by
  have hc := canonical_core_distance C i
  by_contra! ha
  have h₁ : max (C.a i-1/2) 0=0 := max_eq_right (by linarith)
  have h₂ : max (C.b i-1/2) 0=0 := max_eq_right (by linarith [C.b_le_a i])
  norm_num [h₁, h₂] at hc

/-- Each gap of a cycle is below `7/4`, since the six others exceed `19/25`. -/
theorem cycle_gap_lt_seven_quarters (β : Vertex → ℝ) (hgap : ∀ i, 19/25 < angleGap β i)
    (i : Vertex) : angleGap β i < 7/4 := by
  have hsum := angleGap_sum β
  have h0 := hgap 0
  have h1 := hgap 1
  have h2 := hgap 2
  have h3 := hgap 3
  have h4 := hgap 4
  have h5 := hgap 5
  have h6 := hgap 6
  have hp := pi_lt_22_over_7
  simp only [Fin.sum_univ_seven] at hsum
  fin_cases i <;> simp <;> linarith

/-- On the half `φ = π/2 - x`, `0 ≤ x ≤ 7/10`, every margin from a core square of sign `+1` to a
core square of sign `-1` is negative when `b + B ≤ (7/9)(1/5 + x)`. -/
theorem core_quarter_negative_error {a b A B x : ℝ}
    (ha : 1/2 ≤ a ∧ a ≤ 7/12) (hA : 1/2 ≤ A ∧ A ≤ 7/12)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hx : 0 ≤ x ∧ x ≤ 7/10)
    (htrans : b+B ≤ (7/9:ℝ)*(1/5+x)) (j : Fin 4) :
    forwardMargin j a b A B 1 (-1) (Real.pi/2-x) < 0 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hcu := Real.cos_le_one x
  have hsu := Real.sin_le_one x
  have hs : (9/10:ℝ)*x ≤ Real.sin x := by
    nlinarith [Real.sin_ge_sub_cube hx.1, mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hx.1 hx.2 2) hx.1]
  have hc0 : 0 ≤ Real.cos x := by nlinarith [hx.1, hx.2]
  have hs0 : 0 ≤ Real.sin x := by nlinarith [hx.1]
  have hac := mul_nonneg (show 0 ≤ 7/12-a by linarith [ha.2]) hc0
  have hAc := mul_nonneg (show 0 ≤ 7/12-A by linarith [hA.2]) hc0
  have has := mul_nonneg (show 0 ≤ a-1/2 by linarith [ha.1]) hs0
  have hAs := mul_nonneg (show 0 ≤ A-1/2 by linarith [hA.1]) hs0
  have hbc := mul_nonneg hb (show 0 ≤ 1-Real.cos x by linarith)
  have hBc := mul_nonneg hB (show 0 ≤ 1-Real.cos x by linarith)
  have hbs := mul_nonneg hb (show 0 ≤ 1-Real.sin x by linarith)
  have hBs := mul_nonneg hB (show 0 ≤ 1-Real.sin x by linarith)
  fin_cases j <;>
    simp [forwardMargin, pairWidth, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
      abs_of_nonneg hc0, abs_of_nonneg hs0] <;>
    nlinarith [ha.1, ha.2, hA.1, hA.2, hx.1, hx.2]

/-- On the half `φ = π/2 + x`, `0 ≤ x ≤ 7/10`, the same holds when `b + B ≤ (7/9)(1/5 - x)`. -/
theorem core_quarter_nonnegative_error {a b A B x : ℝ}
    (ha : 1/2 ≤ a ∧ a ≤ 7/12) (hA : 1/2 ≤ A ∧ A ≤ 7/12)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hx : 0 ≤ x ∧ x ≤ 7/10)
    (htrans : b+B ≤ (7/9:ℝ)*(1/5-x)) (j : Fin 4) :
    forwardMargin j a b A B 1 (-1) (Real.pi/2+x) < 0 := by
  have hc := (small_angle (show |x| ≤ 7/10 by rw [abs_of_nonneg hx.1]; exact hx.2)).1
  have hc0 : 0 ≤ Real.cos x := by nlinarith
  have hs0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_gt_three])
  have hcu := Real.cos_le_one x
  have hsu := Real.sin_le hx.1
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_nonneg hc0, abs_of_nonneg hs0] at hw
  have hac := mul_nonneg (show 0 ≤ 7/12-a by linarith [ha.2]) hc0
  have hAc := mul_nonneg (show 0 ≤ 7/12-A by linarith [hA.2]) hc0
  have has := mul_nonneg (show 0 ≤ 7/12-a by linarith [ha.2]) hs0
  have hAs := mul_nonneg (show 0 ≤ 7/12-A by linarith [hA.2]) hs0
  have hbc := mul_nonneg hb (show 0 ≤ 1-Real.cos x by linarith)
  have hBc := mul_nonneg hB (show 0 ≤ 1-Real.cos x by linarith)
  have hbs := mul_nonneg hb hs0
  have hBs := mul_nonneg hB hs0
  fin_cases j <;>
    simp [forwardMargin, pairWidth, Real.sin_add, Real.cos_add,
      abs_of_nonneg hc0, abs_of_nonneg hs0] <;>
    nlinarith [ha.1, ha.2, hA.1, hA.2, hx.1, hx.2]

/-- No original axis separates a core square of transverse sign `+1` from a core square of sign
`-1` on a quarter edge whose gap is below `7/4`. -/
theorem core_quarter_opposite_margin {a b A B d : ℝ}
    (ha : 1/2 ≤ a ∧ a ≤ 7/12) (hA : 1/2 ≤ A ∧ A ≤ 7/12)
    (hb : 0 ≤ b ∧ b ≤ a) (hB : 0 ≤ B ∧ B ≤ A) (hd : |d| ≤ 7/10)
    (hgap : Real.pi/2+d+Real.arctan (b/a)+Real.arctan (B/A) < 7/4)
    (j : Fin 4) : forwardMargin j a b A B 1 (-1) (Real.pi/2+d) < 0 := by
  have hbθ := core_transverse_le_angle (by linarith [ha.1]) ha.2 hb.1 hb.2
  have hBθ := core_transverse_le_angle (by linarith [hA.1]) hA.2 hB.1 hB.2
  have htrans : b+B ≤ (7/9:ℝ)*(1/5-d) := by nlinarith [Real.pi_gt_d2]
  rcases le_total 0 d with hd0 | hd0
  · exact core_quarter_nonnegative_error ha hA hb.1 hB.1
      ⟨hd0, by simpa only [abs_of_nonneg hd0] using hd⟩ htrans j
  · simpa only [sub_neg_eq_add] using core_quarter_negative_error (x := -d) ha hA hb.1 hB.1
      ⟨by linarith, by simpa only [abs_of_nonpos hd0] using hd⟩ (by linarith) j

/-- On a quarter edge of a candidate frame, no axis separates a core source with transverse
sign `+1` from a core target with sign `-1`; zero transverse coordinates take either sign. -/
theorem quarter_core_opposite_excluded {q : ℝ} {C : BoundaryCycle q} (F : Frame C) {i : Vertex}
    (hk : word i=1) (ha : C.a i ≤ 7/12) (hA : C.a (next i) ≤ 7/12)
    (hs : C.sigma i*C.b i=C.b i) (ht : C.sigma (next i)*C.b (next i)= -C.b (next i))
    (j : Fin 4) : ¬ (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
  have hφ : phi F.theta i=Real.pi/2+delta F.theta i := by simp [phi, hk]
  have hαs : C.alpha i=Real.arctan (C.b i/C.a i) := by
    simp only [BoundaryCycle.alpha, BoundaryCycle.tangent, hs]
  have hαt : C.alpha (next i)= -Real.arctan (C.b (next i)/C.a (next i)) := by
    simp only [BoundaryCycle.alpha, BoundaryCycle.tangent, ht, neg_div, Real.arctan_neg]
  have he := F.physical_angle i
  rw [hφ, hαs, hαt] at he
  have hn := core_quarter_opposite_margin
    ⟨(canonical_primary_gt_half C i).le, ha⟩ ⟨(canonical_primary_gt_half C (next i)).le, hA⟩
    ⟨C.b_nonneg i, C.b_le_a i⟩ ⟨C.b_nonneg (next i), C.b_le_a (next i)⟩
    (F.delta_small i).le (by linarith [cycle_gap_lt_seven_quarters C.beta F.gap_lower i]) j
  intro hj
  have hm := (F.margin_nonneg_iff i j).1 hj
  simp only [margin, hφ] at hm
  have hmargin : forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (C.sigma i) (C.sigma (next i)) (Real.pi/2+delta F.theta i)=
      forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) 1 (-1)
        (Real.pi/2+delta F.theta i) := by
    fin_cases j <;> simp [forwardMargin, hs, ht]
  linarith

end SquaresInCircles.Eight.Candidate.Geometric
