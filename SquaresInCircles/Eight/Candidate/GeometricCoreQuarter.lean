module

public import SquaresInCircles.Eight.Candidate.GeometricSecondaryExclusion

/-!
# Opposite transverse signs exclude a whole core/core quarter pair

The seven positive center gaps put each individual gap below `7/4`.
For positive source and negative target transverse coordinates, a quarter
phase consumes the gap together with both unsigned core angles. Concavity
of arctangent turns that angular restriction into a bound on the sum of
the transverse coordinates. Every one of the four original SAT margins
is then strictly negative on each of the two full error-sign intervals.

No candidate tangent cut, total mismatch bound, radius bound, generated
label, or angle subdivision enters the scalar statement. The actual-pair
adapter also respects the two sign choices at a zero transverse coordinate.
This Lean source remains uncompiled.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.Candidate.Geometric

/-- The chord of arctangent on `[0,1]`, weakened using `pi > 3`. -/
theorem arctan_chord_three_quarters {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    (3/4:ℝ)*x ≤ Real.arctan x := by
  have hd (y : ℝ) :
      HasDerivAt (fun z : ℝ => 1/(1+z^2)) (-2*y/(1+y^2)^2) y := by
    convert (hasDerivAt_const y (1:ℝ)).div
      ((hasDerivAt_const y (1:ℝ)).add ((hasDerivAt_id y).pow 2))
      (by positivity : (1+y^2:ℝ) ≠ 0) using 1 <;> ring
  have hc : ConcaveOn ℝ (Icc (0:ℝ) 1) Real.arctan := by
    apply concave_of_deriv2
      (f' := fun y : ℝ => 1/(1+y^2))
      (f'' := fun y : ℝ => -2*y/(1+y^2)^2)
    · intro y _
      simpa using Real.hasDerivAt_arctan y
    · intro y _
      exact hd y
    · intro y hy
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hy.1]) (sq_nonneg _)
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show 0 ≤ 1-x by linarith [hx.2]) hx.1 (by ring)
  have he : (1-x) • (0:ℝ)+x • (1:ℝ)=x := by simp
  rw [he] at h
  simp only [Real.arctan_zero,Real.arctan_one,smul_eq_mul,mul_zero,zero_add] at h
  have hp := mul_nonneg (show 0 ≤ Real.pi-3 by linarith [Real.pi_gt_three]) hx.1
  nlinarith

/-- One unsigned core angle controls its whole transverse coordinate. -/
theorem core_transverse_le_angle {a b : ℝ} (ha : 0<a) (hau : a ≤ 7/12)
    (hb : 0 ≤ b) (hab : b ≤ a) :
    b ≤ (7/9:ℝ)*Real.arctan (b/a) := by
  have hx : 0 ≤ b/a ∧ b/a ≤ 1 :=
    ⟨div_nonneg hb ha.le,(div_le_one ha).mpr hab⟩
  have h := arctan_chord_three_quarters hx
  have hm := mul_le_mul_of_nonneg_right hau hx.1
  have he : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
  nlinarith

/-- The core avoidance condition alone puts the primary coordinate above
one half, including every outer boundary state. -/
theorem canonical_primary_gt_half {q : ℝ} (C : BoundaryCycle q) (i : Vertex) :
    1/2<C.a i := by
  have hc := canonical_core_distance C i
  have hab := C.b_le_a i
  by_contra! ha
  have h₁ : max (C.a i-1/2) 0=0 := max_eq_right (by linarith)
  have h₂ : max (C.b i-1/2) 0=0 := max_eq_right (by linarith)
  norm_num [h₁,h₂] at hc

/-- Summing the other six positive gaps gives a rational upper bound
on any one gap. This statement does not use a candidate quarter word. -/
theorem cycle_gap_lt_seven_quarters {q : ℝ} (C : BoundaryCycle q)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    angleGap C.beta i<(7/4:ℝ) := by
  have hsum := angleGap_sum C.beta
  have h0 := hgap 0
  have h1 := hgap 1
  have h2 := hgap 2
  have h3 := hgap 3
  have h4 := hgap 4
  have h5 := hgap 5
  have h6 := hgap 6
  have hp := pi_lt_22_over_7
  simp only [Fin.sum_univ_succ] at hsum
  fin_cases i <;> nlinarith

private theorem small_sine_lower {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 7/10) :
    (9/10:ℝ)*x ≤ Real.sin x := by
  have hsq : x^2 ≤ (7/10:ℝ)^2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hcub := mul_le_mul_of_nonneg_right hsq hx.1
  nlinarith [hx.1,Real.sin_ge_sub_cube hx.1]

/-- The full negative-error interval. The secondary axes retain at least
`19/600` strict reserve; the primary axes have a larger reserve. -/
theorem core_quarter_negative_error {a b A B x : ℝ}
    (ha : 1/2 ≤ a ∧ a ≤ 7/12) (hA : 1/2 ≤ A ∧ A ≤ 7/12)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hx : 0 ≤ x ∧ x ≤ 7/10)
    (htrans : b+B ≤ (7/9:ℝ)*(1/5+x)) (j : Fin 4) :
    forwardMargin j a b A B 1 (-1) (Real.pi/2-x)<0 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hcu := Real.cos_le_one x
  have hsu := Real.sin_le_one x
  have hs := small_sine_lower hx
  have hx2 := mul_nonneg hx.1 (show 0 ≤ 7/10-x by linarith [hx.2])
  have hc0 : 0 ≤ Real.cos x := by nlinarith [hx.1,hx.2]
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
    simp [forwardMargin,pairWidth,Real.sin_sub,Real.cos_sub,
      abs_of_nonneg hc0,abs_of_nonneg hs0] <;> nlinarith [ha.1,ha.2,hA.1,hA.2,hx.1,hx.2]

/-- The full positive-error interval. The angular budget decreases with
the error, while every potentially helpful primary projection grows more
slowly. All four axes retain at least `47/180` strict reserve. -/
theorem core_quarter_nonnegative_error {a b A B x : ℝ}
    (ha : 1/2 ≤ a ∧ a ≤ 7/12) (hA : 1/2 ≤ A ∧ A ≤ 7/12)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hx : 0 ≤ x ∧ x ≤ 7/10)
    (htrans : b+B ≤ (7/9:ℝ)*(1/5-x)) (j : Fin 4) :
    forwardMargin j a b A B 1 (-1) (Real.pi/2+x)<0 := by
  have hc := (small_angle (show |x| ≤ 7/10 by
    rw [abs_of_nonneg hx.1]; exact hx.2)).1
  have hc0 : 0 ≤ Real.cos x := by nlinarith
  have hs0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hcu := Real.cos_le_one x
  have hsu := Real.sin_le hx.1
  have hw := one_le_abs_cos_add_abs_sin x
  rw [abs_of_nonneg hc0,abs_of_nonneg hs0] at hw
  have hac := mul_nonneg (show 0 ≤ 7/12-a by linarith [ha.2]) hc0
  have hAc := mul_nonneg (show 0 ≤ 7/12-A by linarith [hA.2]) hc0
  have has := mul_nonneg (show 0 ≤ 7/12-a by linarith [ha.2]) hs0
  have hAs := mul_nonneg (show 0 ≤ 7/12-A by linarith [hA.2]) hs0
  have hbc := mul_nonneg hb (show 0 ≤ 1-Real.cos x by linarith)
  have hBc := mul_nonneg hB (show 0 ≤ 1-Real.cos x by linarith)
  have hbs := mul_nonneg hb hs0
  have hBs := mul_nonneg hB hs0
  fin_cases j <;>
    simp [forwardMargin,pairWidth,Real.sin_add,Real.cos_add,
      abs_of_nonneg hc0,abs_of_nonneg hs0] <;> nlinarith [ha.1,ha.2,hA.1,hA.2,hx.1,hx.2]

/-- A complete core/core quarter class is infeasible on the whole frame
range. The only geometric angle hypothesis is the physical gap cap. -/
theorem core_quarter_opposite_margin {a b A B d : ℝ}
    (ha : 1/2 ≤ a ∧ a ≤ 7/12) (hA : 1/2 ≤ A ∧ A ≤ 7/12)
    (hb : 0 ≤ b ∧ b ≤ a) (hB : 0 ≤ B ∧ B ≤ A)
    (hd : |d| ≤ 7/10)
    (hgap : Real.pi/2+d+Real.arctan (b/a)+Real.arctan (B/A)<7/4)
    (j : Fin 4) : forwardMargin j a b A B 1 (-1) (Real.pi/2+d)<0 := by
  have hbθ := core_transverse_le_angle (show 0<a by linarith [ha.1]) ha.2 hb.1 hb.2
  have hBθ := core_transverse_le_angle (show 0<A by linarith [hA.1]) hA.2 hB.1 hB.2
  have hp : (31/10:ℝ)<Real.pi := by linarith [Real.pi_gt_d2]
  have htrans : b+B ≤ (7/9:ℝ)*(1/5-d) := by nlinarith
  rcases le_total 0 d with hd0 | hd0
  · exact core_quarter_nonnegative_error ha hA hb.1 hB.1
      ⟨hd0,by simpa only [abs_of_nonneg hd0] using hd⟩ htrans j
  · have hx : 0 ≤ -d ∧ -d ≤ 7/10 :=
      ⟨by linarith,by simpa only [abs_of_nonpos hd0] using hd⟩
    have ht : b+B ≤ (7/9:ℝ)*(1/5+(-d)) := by linarith
    simpa only [sub_neg_eq_add] using
      core_quarter_negative_error ha hA hb.1 hB.1 hx ht j

/-- Actual candidate coordinates enter the scalar inequality through
their signed products, so zero-coordinate sign junctions are included. -/
theorem quarter_core_opposite_excluded {q : ℝ} {C : BoundaryCycle q}
    (F : Frame C) {i : Vertex} (hk : word i=1)
    (ha : C.a i ≤ 7/12) (hA : C.a (next i) ≤ 7/12)
    (hs : C.sigma i*C.b i=C.b i)
    (ht : C.sigma (next i)*C.b (next i)= -C.b (next i)) (j : Fin 4) :
    ¬ (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
  have hφ : phi F.theta i=Real.pi/2+delta F.theta i := by simp [phi,hk]
  have hαs : C.alpha i=Real.arctan (C.b i/C.a i) := by
    simp only [BoundaryCycle.alpha,BoundaryCycle.tangent,hs]
  have hαt : C.alpha (next i)= -Real.arctan (C.b (next i)/C.a (next i)) := by
    simp only [BoundaryCycle.alpha,BoundaryCycle.tangent,ht,neg_div,Real.arctan_neg]
  have he := F.physical_angle i
  rw [hφ,hαs,hαt] at he
  have hg := cycle_gap_lt_seven_quarters C F.gap_lower i
  have hn := core_quarter_opposite_margin
    ⟨(canonical_primary_gt_half C i).le,ha⟩
    ⟨(canonical_primary_gt_half C (next i)).le,hA⟩
    ⟨C.b_nonneg i,C.b_le_a i⟩ ⟨C.b_nonneg (next i),C.b_le_a (next i)⟩
    (F.delta_small i).le (by linarith) j
  intro hj
  have hm := (F.margin_nonneg_iff i j).1 hj
  simp only [margin,hφ] at hm
  have hmargin :
      forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
        (C.sigma i) (C.sigma (next i)) (Real.pi/2+delta F.theta i)=
      forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
        1 (-1) (Real.pi/2+delta F.theta i) := by
    fin_cases j <;> simp [forwardMargin,hs,ht]
  rw [hmargin] at hm
  linarith

end SquaresInCircles.Eight.Candidate.Geometric
