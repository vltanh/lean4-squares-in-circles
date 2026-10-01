import SquaresInCircles.Seven.Analysis

/-!
Shared helpers for the research-only human-proof replacements.

The namespace is deliberately different from the production namespace. No
replacement is proved by applying the production result it is intended to
replace. These files do not alter the public packing statements.

The pi estimates below use proved Mathlib theorems, not numerical evaluation.
P_ELEMENTARY_PI_BOUNDS.md gives the accompanying elementary hand derivation.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

lemma pi_lower : (157 : ℝ) / 50 < Real.pi := by
  linarith [Real.pi_gt_d2]

lemma pi_upper : Real.pi < (22 : ℝ) / 7 := by
  linarith [Real.pi_lt_d4]

lemma pi_upper_transition : Real.pi < (377 : ℝ) / 120 := by
  linarith [Real.pi_lt_d4]

lemma sqrt_three_coarse : (173 : ℝ)/100 < Real.sqrt 3 ∧
    Real.sqrt 3 < (1733 : ℝ)/1000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]

lemma unit_pow_bounds {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (n : ℕ) :
    0 ≤ x^n ∧ x^n ≤ 1 := by
  refine ⟨pow_nonneg hx.1 n, ?_⟩
  simpa using pow_le_pow_left₀ hx.1 hx.2 n

/-- Cauchy--Schwarz, with the orthogonal error displayed explicitly. -/
lemma disk_dot_sq {X Y p q : ℝ} (h : X^2 + Y^2 ≤ (13 : ℝ)/4) :
    (p*X + q*Y)^2 ≤ (13 : ℝ)/4 * (p^2 + q^2) := by
  have hid : (p*X+q*Y)^2+(p*Y-q*X)^2 =
      (p^2+q^2)*(X^2+Y^2) := by ring
  have hm := mul_le_mul_of_nonneg_left h
    (add_nonneg (sq_nonneg p) (sq_nonneg q))
  nlinarith [sq_nonneg (p*Y-q*X)]

lemma disk_dot_upper {X Y p q c : ℝ}
    (h : X^2 + Y^2 ≤ (13 : ℝ)/4) (hc : 0 ≤ c)
    (hm : (13 : ℝ)/4*(p^2+q^2) ≤ c^2) : p*X+q*Y ≤ c := by
  have hh := disk_dot_sq (p := p) (q := q) h
  nlinarith [sq_nonneg (p*X+q*Y-c)]

lemma disk_dot_lower_strict {X Y p q c : ℝ}
    (h : X^2 + Y^2 ≤ (13 : ℝ)/4) (hc : 0 ≤ c)
    (hm : (13 : ℝ)/4*(p^2+q^2) < c^2) : -c < p*X+q*Y := by
  have hh := disk_dot_sq (p := p) (q := q) h
  nlinarith [sq_nonneg (p*X+q*Y+c)]

/-- A single derived stationary point, not a subdivision/certificate grid. -/
lemma le_at_peak {f d : ℝ → ℝ} {l c u x : ℝ}
    (hc : l ≤ c ∧ c ≤ u) (hx : l ≤ x ∧ x ≤ u)
    (hf : Continuous f) (hd : ∀ y, HasDerivAt f (d y) y)
    (hleft : ∀ y ∈ Icc l c, 0 ≤ d y)
    (hright : ∀ y ∈ Icc c u, d y ≤ 0) : f x ≤ f c := by
  rcases le_total x c with hxc | hcx
  · have hm := Seven.monoOn_of_hasDeriv_nonneg
      (l := l) (u := c) hf.continuousOn
      (fun y _ => hd y) (fun y hy => hleft y ⟨hy.1.le, hy.2.le⟩)
    exact hm ⟨hx.1,hxc⟩ ⟨hc.1,le_rfl⟩ hxc
  · have hm := Seven.antiOn_of_hasDeriv_nonpos
      (l := c) (u := u) hf.continuousOn
      (fun y _ => hd y) (fun y hy => hright y ⟨hy.1.le,hy.2.le⟩)
    exact hm ⟨le_rfl,hc.2⟩ ⟨hcx,hx.2⟩ hcx

/-- The endpoint value exceeds the greatest possible tangent-parabola loss. -/
lemma positive_from_endpoint_reserve {F d dd : ℝ → ℝ} {l u x : ℝ}
    (hx : x ∈ Icc l u) (hd : ∀ y ∈ Icc l u, HasDerivAt F (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hcurv : ∀ y ∈ Icc l u, (5 : ℝ)/8 ≤ dd y)
    (hval : (1 : ℝ)/640 < F u)
    (hslope : 0 < d u ∧ d u < (7 : ℝ)/160) :
    (1 : ℝ)/32000 < F x := by
  have ht := Seven.curvature_tangent hx ⟨hx.1.trans hx.2,le_rfl⟩ hd hdd hcurv
  have hs : (d u)^2 < (7/160 : ℝ)^2 := by nlinarith [hslope.1,hslope.2]
  have hsq := sq_nonneg ((x-u)+(8/5 : ℝ)*d u)
  nlinarith

end SquaresInCircles.Seven.Human
