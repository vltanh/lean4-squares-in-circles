module

public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Common.Charts
public import SquaresInCircles.Common.Arcs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The central square and the strict one-twelfth core

Sources: `HUMAN_GLOBAL_GEOMETRY_CLOSURE.md`,
`HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md`, and
`CENTRAL_BAND_COMMON_POINT_LEMMAS.md`.

Angular length means the measure of the complete circle intersection. It is
not the span of its endpoints. In particular disconnected circle intersections
and side tangencies remain in the definition and in the summation theorem.
The strict-core conclusion uses actual closed squares and open interiors.

Uncompiled implementation draft; no compiler or CI has been invoked.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Set
namespace SquaresInCircles.Eight

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- Complete angular intersection, allowing any number of components. -/
def squareAngles (K : UnitSquare) (r : ℝ) : Set Direction :=
  {θ | closedSquare K (circlePoint (0, 0) r θ)}

def angularLength (K : UnitSquare) (r : ℝ) : ℝ :=
  (volume (squareAngles K r)).toReal

lemma angularLength_nonneg (K : UnitSquare) (r : ℝ) : 0 ≤ angularLength K r :=
  ENNReal.toReal_nonneg

lemma squareAngles_measurable (K : UnitSquare) (r : ℝ) :
    MeasurableSet (squareAngles K r) := by
  have hx : Continuous (fun θ : Direction => localX K (circlePoint (0, 0) r θ)) := by
    dsimp [localX, circlePoint]
    fun_prop
  have hy : Continuous (fun θ : Direction => localY K (circlePoint (0, 0) r θ)) := by
    dsimp [localY, circlePoint]
    fun_prop
  exact ((isClosed_le hx.abs continuous_const).inter
    (isClosed_le hy.abs continuous_const)).measurableSet

lemma finite_angle_cos_fiber (c : ℝ) : Set.Finite {θ : Direction | θ.cos = c} := by
  by_cases h : ({θ : Direction | θ.cos = c} : Set Direction).Nonempty
  · obtain ⟨θ, hθ⟩ := h
    refine (Set.finite_insert θ (Set.finite_singleton (-θ))).subset ?_
    intro ψ hψ
    have hh : ψ.cos = θ.cos := hψ.trans hθ.symm
    rcases Real.Angle.cos_eq_iff_eq_or_eq_neg.mp hh with h | h <;> simp [h]
  · simpa only [Set.not_nonempty_iff_eq_empty.mp h] using
      (Set.finite_empty : Set.Finite (∅ : Set Direction))

lemma finite_angle_sin_fiber (c : ℝ) : Set.Finite {θ : Direction | θ.sin = c} := by
  by_cases h : ({θ : Direction | θ.sin = c} : Set Direction).Nonempty
  · obtain ⟨θ, hθ⟩ := h
    refine (Set.finite_insert θ (Set.finite_singleton ((Real.pi : Direction) - θ))).subset ?_
    intro ψ hψ
    have hh : ψ.sin = θ.sin := hψ.trans hθ.symm
    rcases Real.Angle.sin_eq_iff_eq_or_add_eq_pi.mp hh with h | h
    · simp [h]
    · have he : ψ = (Real.pi : Direction) - θ := by
        exact eq_sub_iff_add_eq.mpr h
      simp [he]
  · simpa only [Set.not_nonempty_iff_eq_empty.mp h] using
      (Set.finite_empty : Set.Finite (∅ : Set Direction))

lemma local_circle_coordinates (K : UnitSquare) (r : ℝ) {φ : ℝ}
    (hc : Real.cos φ = K.cosine) (hs : Real.sin φ = K.sine) (θ : Direction) :
    localX K (circlePoint (0, 0) r θ) =
      r * (θ - (φ : Direction)).cos - frameX K K.center ∧
    localY K (circlePoint (0, 0) r θ) =
      r * (θ - (φ : Direction)).sin - frameY K K.center := by
  simp only [localX, localY, frameX, frameY, circlePoint, zero_add,
    Real.Angle.cos_sub, Real.Angle.sin_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe, hc, hs]
  constructor <;> ring

lemma finite_localX_circle_fiber (K : UnitSquare) {r : ℝ} (hr : r ≠ 0) (c : ℝ) :
    Set.Finite {θ : Direction | localX K (circlePoint (0, 0) r θ) = c} := by
  obtain ⟨φ, hc, hs⟩ := frame_angle K
  have hinj : Function.Injective (fun θ : Direction => θ - (φ : Direction)) := by
    intro x y h
    simpa using congrArg (fun z : Direction => z + (φ : Direction)) h
  have hfinite := (finite_angle_cos_fiber ((c + frameX K K.center) / r)).preimage hinj
  refine hfinite.subset ?_
  intro θ hθ
  change (θ - (φ : Direction)).cos = (c + frameX K K.center) / r
  rw [(local_circle_coordinates K r hc hs θ).1] at hθ
  apply (eq_div_iff hr).2
  nlinarith

lemma finite_localY_circle_fiber (K : UnitSquare) {r : ℝ} (hr : r ≠ 0) (c : ℝ) :
    Set.Finite {θ : Direction | localY K (circlePoint (0, 0) r θ) = c} := by
  obtain ⟨φ, hc, hs⟩ := frame_angle K
  have hinj : Function.Injective (fun θ : Direction => θ - (φ : Direction)) := by
    intro x y h
    simpa using congrArg (fun z : Direction => z + (φ : Direction)) h
  have hfinite := (finite_angle_sin_fiber ((c + frameY K K.center) / r)).preimage hinj
  refine hfinite.subset ?_
  intro θ hθ
  change (θ - (φ : Direction)).sin = (c + frameY K K.center) / r
  rw [(local_circle_coordinates K r hc hs θ).2] at hθ
  apply (eq_div_iff hr).2
  nlinarith

/-- A line side contributes only finitely many angular points on a nonzero
circle. This includes tangent and corner coincidences. -/
lemma finite_square_boundary_angles (K : UnitSquare) {r : ℝ} (hr : r ≠ 0) :
    Set.Finite {θ : Direction |
      closedSquare K (circlePoint (0, 0) r θ) ∧
        ¬ openSquare K (circlePoint (0, 0) r θ)} := by
  have hf := ((finite_localX_circle_fiber K hr (1 / 2)).union
    (finite_localX_circle_fiber K hr (-1 / 2))).union
    ((finite_localY_circle_fiber K hr (1 / 2)).union
      (finite_localY_circle_fiber K hr (-1 / 2)))
  refine hf.subset ?_
  intro θ hθ
  rcases hθ with ⟨⟨hx, hy⟩, hn⟩
  change ¬ (|localX K _| < 1 / 2 ∧ |localY K _| < 1 / 2) at hn
  have hboundary : |localX K (circlePoint (0, 0) r θ)| = 1 / 2 ∨
      |localY K (circlePoint (0, 0) r θ)| = 1 / 2 := by
    by_contra! h
    exact hn ⟨lt_of_le_of_ne hx h.1, lt_of_le_of_ne hy h.2⟩
  rcases hboundary with h | h
  · exact Or.inl ((abs_eq (show (0 : ℝ) ≤ 1 / 2 by norm_num)).mp h)
  · exact Or.inr ((abs_eq (show (0 : ℝ) ≤ 1 / 2 by norm_num)).mp h)

/-- Actual angular budget. No connectedness hypothesis is used. -/
theorem angularLength_budget {n : ℕ} {S : Fin n → UnitSquare}
    (hd : InteriorDisjoint S) {r : ℝ} (hr : r ≠ 0) :
    ∑ i, angularLength (S i) r ≤ 2 * Real.pi := by
  have hae (i j : Fin n) (hij : i ≠ j) :
      AEDisjoint volume (squareAngles (S i) r) (squareAngles (S j) r) := by
    change volume (squareAngles (S i) r ∩ squareAngles (S j) r) = 0
    apply Set.Finite.measure_zero
    refine ((finite_square_boundary_angles (S i) hr).union
      (finite_square_boundary_angles (S j) hr)).subset ?_
    intro θ hθ
    by_cases hi : openSquare (S i) (circlePoint (0, 0) r θ)
    · exact Or.inr ⟨hθ.2, fun hj => hd i j hij _ ⟨hi, hj⟩⟩
    · exact Or.inl ⟨hθ.1, hi⟩
  have hmu := sum_measure_le_measure_univ
    (μ := (volume : Measure (AddCircle (2 * Real.pi))))
    (s := Finset.univ)
    (fun i _ => (squareAngles_measurable (S i) r).nullMeasurableSet)
    (fun i _ j _ hij => hae i j hij)
  have hreal := ENNReal.toReal_mono (measure_ne_top volume Set.univ) hmu
  rw [AddCircle.measure_univ, ENNReal.toReal_ofReal (by positivity)] at hreal
  simpa only [angularLength, ENNReal.toReal_sum (fun i _ => measure_ne_top volume _)]
    using hreal

/-- Closed chart membership is derived from the existing open membership
theorem by shrinking around the square center. -/
lemma SquareChart.closed_membership {K : UnitSquare} {o : Point}
    (C : SquareChart K o) (r θ : ℝ) :
    closedSquare K (circlePoint o r (chartAngle C.phase C.reversed θ)) ↔
      |r * Real.cos θ - C.a| ≤ 1 / 2 ∧ |r * Real.sin θ - C.b| ≤ 1 / 2 := by
  let p := circlePoint o r (chartAngle C.phase C.reversed θ)
  have hpoint (t : ℝ) :
      sub (circlePoint o (t * r) (chartAngle C.phase C.reversed θ))
        (scale (t - 1) (sub K.center o)) = (1 - t) • K.center + t • p := by
    ext <;> dsimp [p, sub, scale, circlePoint] <;> ring
  have hiff (t : ℝ) : openSquare K ((1 - t) • K.center + t • p) ↔
      |t * (r * Real.cos θ - C.a)| < 1 / 2 ∧
        |t * (r * Real.sin θ - C.b)| < 1 / 2 := by
    rw [← hpoint, C.shifted_membership]
    congr 2 <;> ring
  constructor
  · intro hp
    constructor <;> apply bound_from_shrinks <;> intro t ht₀ ht₁
    · have h := ((hiff t).1 (shrink_open K hp ht₀ ht₁)).1
      simpa only [abs_mul, abs_of_nonneg ht₀] using h.le
    · have h := ((hiff t).1 (shrink_open K hp ht₀ ht₁)).2
      simpa only [abs_mul, abs_of_nonneg ht₀] using h.le
  · intro hp
    have hh (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
        openSquare K ((1 - t) • K.center + t • p) := by
      apply (hiff t).2
      rw [abs_mul, abs_mul, abs_of_nonneg ht₀]
      constructor <;> nlinarith [hp.1, hp.2,
        abs_nonneg (r * Real.cos θ - C.a), abs_nonneg (r * Real.sin θ - C.b)]
    constructor <;> apply bound_from_shrinks <;> intro t ht₀ ht₁
    · have h := (hh t ht₀ ht₁).1
      rw [(local_affine K K.center p (sub_add_cancel 1 t)).1] at h
      simpa [localX, abs_mul, abs_of_nonneg ht₀] using h.le
    · have h := (hh t ht₀ ht₁).2
      rw [(local_affine K K.center p (sub_add_cancel 1 t)).2] at h
      simpa [localY, abs_mul, abs_of_nonneg ht₀] using h.le

/-- Even a closed-square arc may be used as a lower bound: finitely many
boundary points were accounted for in `angularLength_budget`. -/
lemma angularLength_ge_arc {K : UnitSquare} {r : ℝ}
    (A : OpenArc (0, 0) r {p | closedSquare K p}) :
    2 * A.halfWidth ≤ angularLength K r := by
  apply bound_from_shrinks
  intro t ht₀ ht₁
  have hlt : t * A.halfWidth < A.halfWidth :=
    mul_lt_of_lt_one_left A.positive ht₁
  have hsub : Metric.closedBall A.center (t * A.halfWidth) ⊆ squareAngles K r := by
    intro θ hθ
    exact A.inside θ (lt_of_le_of_lt hθ hlt)
  have hm := ENNReal.toReal_mono (measure_ne_top volume (squareAngles K r))
    (measure_mono hsub)
  rw [AddCircle.volume_closedBall,
    min_eq_right (by nlinarith [A.atMostPi]),
    ENNReal.toReal_ofReal (by positivity)] at hm
  dsimp [angularLength]
  nlinarith

/-- The weighted equality argument uses the actual angular lengths. -/
lemma central_exists_from_one_square_inequality
    {S : Fin 8 → UnitSquare} (hd : InteriorDisjoint S)
    (hbound : ∀ i, ¬ openSquare (S i) (0, 0) →
      Real.pi ≤ 3 * angularLength (S i) 1 + angularLength (S i) (5 / 4))
    (heq : ∀ i, ¬ openSquare (S i) (0, 0) →
      3 * angularLength (S i) 1 + angularLength (S i) (5 / 4) = Real.pi →
      angularLength (S i) 1 = Real.pi / 3) :
    ∃ i, openSquare (S i) (0, 0) := by
  by_contra! hn
  have h₁ := angularLength_budget hd (r := 1) (by norm_num)
  have h₂ := angularLength_budget hd (r := 5 / 4) (by norm_num)
  let W : Fin 8 → ℝ := fun i =>
    3 * angularLength (S i) 1 + angularLength (S i) (5 / 4)
  have hW : ∀ i, 0 ≤ W i - Real.pi := fun i => sub_nonneg.mpr (hbound i (hn i))
  have hsum : ∑ i, (W i - Real.pi) = 0 := by
    have hnonneg := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hW i)
    have hid : ∑ i, (W i - Real.pi) =
        3 * ∑ i, angularLength (S i) 1 +
          ∑ i, angularLength (S i) (5 / 4) - 8 * Real.pi := by
      simp [W, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hW i)).1 hsum
  have hL (i : Fin 8) : angularLength (S i) 1 = Real.pi / 3 :=
    heq i (hn i) (by have hi := hzero i (Finset.mem_univ i); dsimp [W] at hi; linarith)
  simp only [hL, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁
  linarith [Real.pi_pos]

lemma central_square_unique {n : ℕ} {S : Fin n → UnitSquare}
    (hd : InteriorDisjoint S) {o : Point} {i j : Fin n}
    (hi : openSquare (S i) o) (hj : openSquare (S j) o) : i = j := by
  by_contra hij
  exact hd i j hij o ⟨hi, hj⟩

/-- The closed one-twelfth disk is strictly inside a square whenever both
absolute center coordinates are strictly below five twelfths. -/
lemma containsCore_of_center_bounds {K : UnitSquare}
    (hx : alpha K (0, 0) < 5 / 12) (hy : beta K (0, 0) < 5 / 12) :
    ContainsCore K := by
  intro p hp
  have hf := frame_norm K p
  have hx' : |frameX K p| ≤ 1 / 12 := by
    have hs := sq_nonneg (frameY K p)
    dsimp [coreRadius] at hp
    nlinarith [sq_abs (frameX K p), abs_nonneg (frameX K p)]
  have hy' : |frameY K p| ≤ 1 / 12 := by
    have hs := sq_nonneg (frameX K p)
    dsimp [coreRadius] at hp
    nlinarith [sq_abs (frameY K p), abs_nonneg (frameY K p)]
  have heX : localX K p = frameX K p + localX K (0, 0) := by
    dsimp [localX, frameX]
    ring
  have heY : localY K p = frameY K p + localY K (0, 0) := by
    dsimp [localY, frameY]
    ring
  constructor
  · rw [heX]
    have := abs_add_le (frameX K p) (localX K (0, 0))
    change |localX K (0, 0)| < 5 / 12 at hx
    linarith
  · rw [heY]
    have := abs_add_le (frameY K p) (localY K (0, 0))
    change |localY K (0, 0)| < 5 / 12 at hy
    linarith

lemma dot_support_strict {K : UnitSquare} {n p : Point}
    (hn : n ≠ (0, 0)) (hp : openSquare K p) :
    dot n (sub p K.center) < width K n := by
  have hdot := frame_dot K n (sub p K.center)
  have hx : frameX K (sub p K.center) = localX K p := rfl
  have hy : frameY K (sub p K.center) = localY K p := rfl
  rw [hx, hy] at hdot
  have hstrict := weighted_strict (abs_nonneg (frameX K n))
    (abs_nonneg (frameY K n)) (frame_abs_sum_pos K hn) hp.1 hp.2
  have hx' := le_abs_self (frameX K n * localX K p)
  have hy' := le_abs_self (frameY K n * localY K p)
  rw [abs_mul] at hx' hy'
  dsimp [width]
  nlinarith

lemma dot_support_weak {K : UnitSquare} {n p : Point}
    (hp : closedSquare K p) : dot n (sub p K.center) ≤ width K n := by
  have hdot := frame_dot K n (sub p K.center)
  have hx : frameX K (sub p K.center) = localX K p := rfl
  have hy : frameY K (sub p K.center) = localY K p := rfl
  rw [hx, hy] at hdot
  have hx' := le_abs_self (frameX K n * localX K p)
  have hy' := le_abs_self (frameY K n * localY K p)
  rw [abs_mul] at hx' hy'
  have h₁ := mul_le_mul_of_nonneg_left hp.1 (abs_nonneg (frameX K n))
  have h₂ := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg (frameY K n))
  dsimp [width]
  nlinarith

/-- A closed square cannot touch the open interior of an interior-disjoint
square. The strict support bound avoids any assumption of positive gap. -/
lemma open_closed_disjoint {K L : UnitSquare}
    (hd : ∀ p, ¬ (openSquare K p ∧ openSquare L p)) :
    ∀ p, ¬ (openSquare K p ∧ closedSquare L p) := by
  obtain ⟨sep⟩ := support_separator K L hd
  intro p hp
  have h₁ := dot_support_strict sep.nonzero hp.1
  have h₂ := dot_support_weak (n := scale (-1) sep.normal) hp.2
  have hsep := sep.separates
  rw [width_neg] at h₂
  dsimp [dot, sub, scale] at h₁ h₂ hsep
  linarith

lemma strictCoreAvoiding_of_containsCore {K L : UnitSquare}
    (hcore : ContainsCore K) (hd : ∀ p, ¬ (openSquare K p ∧ openSquare L p)) :
    StrictCoreAvoiding L := by
  intro p hp
  by_contra! hn
  exact open_closed_disjoint hd p ⟨hcore p hn, hp⟩

/-- Polynomial identity behind the two-circle position monotonicities. -/
lemma two_circle_difference_factorization (r X Y Q : ℝ)
    (hQ : X ^ 2 + Y ^ 2 = Q) :
    X ^ 2 * (r ^ 2 - (X - 1) ^ 2) -
        Y ^ 2 * (r ^ 2 - (Y - 1) ^ 2) =
      (X - Y) * ((r ^ 2 - 1) * (X + Y) +
        (X + Y) ^ 2 - Q * (X + Y) + Q) := by
  rw [← hQ]
  ring

lemma two_circle_factor_positive {r X Y Q : ℝ}
    (hr : 1 ≤ r) (hX : 0 < X) (hY : 0 < Y) (hQ : 0 < Q ∧ Q < 4) :
    0 < (r ^ 2 - 1) * (X + Y) + (X + Y) ^ 2 - Q * (X + Y) + Q := by
  have hr' : 0 ≤ r ^ 2 - 1 := by nlinarith
  have hp := mul_nonneg hr' (show 0 ≤ X + Y by linarith)
  have hq := mul_pos hQ.1 (show 0 < 1 - Q / 4 by linarith)
  nlinarith [sq_nonneg (X + Y - Q / 2)]

lemma central_band_one_angle_contradiction {w span : ℝ}
    (hw : 347 / 200 < w) (hspan : 6 * (19 / 25 : ℝ) < span)
    (hbudget : w + span ≤ 2 * Real.pi) (hpi : Real.pi < 22 / 7) : False := by
  linarith

lemma central_band_two_angle_contradiction {w span : ℝ}
    (hw : 899 / 500 < w) (hspan : 6 * (3741 / 5000 : ℝ) < span)
    (hbudget : w + span ≤ 2 * Real.pi) (hpi : Real.pi < 22 / 7) : False := by
  linarith

lemma translated_ceiling_reserve :
    Q0 + 4 / 1000 + (1 / 1000 : ℝ) ^ 2 < 98 / 25 := by
  norm_num [Q0]

namespace TwoCircle

def lowerAngle (r x y : ℝ) : ℝ :=
  max (-Real.arccos (x / r)) (Real.arcsin (y / r))

def upperAngle (r x y : ℝ) : ℝ :=
  min (Real.arccos (x / r)) (Real.arcsin ((y + 1) / r))

def intervalLength (r x y : ℝ) : ℝ := upperAngle r x y - lowerAngle r x y

lemma arcsin_half : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
  apply Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
  constructor <;> linarith [Real.pi_pos]

lemma arccos_half : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
  exact Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos])
    Real.cos_pi_div_three.symm

/-- The elementary midpoint inequality needed at both auxiliary radii. Its
proof squares only nonnegative quantities; no derivative at arcsin(1) occurs. -/
lemma arcsin_midpoint {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v ≤ 1) :
    2 * Real.arcsin ((u + v) / 2) ≤ Real.arcsin u + Real.arcsin v := by
  have hu₁ : u ≤ 1 := by linarith
  have hv₁ : v ≤ 1 := by linarith
  let X := Real.cos (Real.arcsin u)
  let Y := Real.cos (Real.arcsin v)
  let C := 1 - (u + v) ^ 2 / 2
  have hX : 0 ≤ X := Real.cos_arcsin_nonneg u
  have hY : 0 ≤ Y := Real.cos_arcsin_nonneg v
  have hXsq : X ^ 2 = 1 - u ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin u)
    rw [Real.sin_arcsin (by linarith) hu₁] at h
    dsimp [X]
    linarith
  have hYsq : Y ^ 2 = 1 - v ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin v)
    rw [Real.sin_arcsin (by linarith) hv₁] at h
    dsimp [Y]
    linarith
  have hprod : (X * Y) ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) := by
    rw [mul_pow, hXsq, hYsq]
  have hC : 0 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (u + v - 1)]
  have hp : 0 ≤ u * v := mul_nonneg hu hv
  have hid : (C + u * v) ^ 2 - (X * Y) ^ 2 =
      (u + v) ^ 2 * (u - v) ^ 2 / 4 := by
    dsimp [C]
    rw [hprod]
    ring
  have hm := mul_nonneg (sq_nonneg (u + v)) (sq_nonneg (u - v))
  have hXY : X * Y ≤ C + u * v := by
    nlinarith [mul_nonneg hX hY]
  have hsumcos : Real.cos (Real.arcsin u + Real.arcsin v) ≤ C := by
    rw [Real.cos_add, Real.sin_arcsin (by linarith) hu₁,
      Real.sin_arcsin (by linarith) hv₁]
    exact sub_le_iff_le_add.mpr hXY
  have htarget : Real.cos (2 * Real.arcsin ((u + v) / 2)) = C := by
    have hh := Real.sin_sq_add_cos_sq (Real.arcsin ((u + v) / 2))
    rw [Real.sin_arcsin (by linarith) (by linarith)] at hh
    rw [Real.cos_two_mul]
    dsimp [C]
    nlinarith
  have hrange : Real.arcsin u + Real.arcsin v ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact add_nonneg (Real.arcsin_nonneg.mpr hu) (Real.arcsin_nonneg.mpr hv)
    · linarith [Real.arcsin_le_pi_div_two u, Real.arcsin_le_pi_div_two v]
  have htrange : 2 * Real.arcsin ((u + v) / 2) ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by linarith))
    · linarith [Real.arcsin_le_pi_div_two ((u + v) / 2)]
  by_contra! hn
  have hc := Real.strictAntiOn_cos hrange htrange hn
  rw [htarget] at hc
  linarith

lemma two_arcsin_quarter_lt : 2 * Real.arcsin (1 / 4 : ℝ) < Real.pi / 6 := by
  have hA : 0 ≤ Real.arcsin (1 / 4 : ℝ) := Real.arcsin_nonneg.mpr (by norm_num)
  have hA' : Real.arcsin (1 / 4 : ℝ) < Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hcos := Real.cos_arcsin (1 / 4 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - (1 / 4 : ℝ) ^ 2 by norm_num)
  have hsin : Real.sin (2 * Real.arcsin (1 / 4 : ℝ)) < 1 / 2 := by
    rw [Real.sin_two_mul, Real.sin_arcsin (by norm_num) (by norm_num), hcos]
    nlinarith [Real.sqrt_nonneg (1 - (1 / 4 : ℝ) ^ 2)]
  by_contra! hn
  have hh := Real.strictMonoOn_sin.monotoneOn
    (show Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show 2 * Real.arcsin (1 / 4 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) hn
  rw [Real.sin_pi_div_six] at hh
  linarith

lemma canonical_x_bound {x y : ℝ} (hx : 0 ≤ x) (hy : -1 / 2 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25) : x < 11 / 12 := by
  have hysq : 1 / 4 ≤ (y + 1) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (x - 11 / 12)]

lemma canonical_corner_sum {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25) : x + y ≤ 4 / 5 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4 / 5)]

/-- A direct polynomial substitute for the position-derivative comparison in
the corner branch. The two values of C are cos(2 asin(2/5)) and
cos(2 asin(8/25)). -/
lemma corner_quadratic {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25)
    (hC : C = 17 / 25 ∨ C = 497 / 625) :
    x ^ 2 + y ^ 2 + 2 * C * x * y ≤ 16 / 25 * C + 8 / 25 * (1 - C) := by
  have hs := canonical_corner_sum hx hy hfar
  have hp := mul_nonneg hx hy
  by_cases hlow : x + y ≤ 7 / 10
  · rcases hC with rfl | rfl <;> nlinarith [sq_nonneg (x + y - 7 / 10)]
  · have hprod : 0 ≤ (4 / 5 - (x + y)) *
        (C * (x + y + 4 / 5) - 2 * (1 - C)) := by
      apply mul_nonneg (by linarith)
      rcases hC with rfl | rfl <;> linarith
    have hscale : (1 - C) * ((x + 1) ^ 2 + (y + 1) ^ 2) ≤ (1 - C) * (98 / 25) :=
      mul_le_mul_of_nonneg_left hfar (by rcases hC with rfl | rfl <;> norm_num)
    nlinarith

lemma corner_arcsin_sum {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25)
    (hr : r = 1 ∨ r = 5 / 4) :
    Real.arcsin (x / r) + Real.arcsin (y / r) ≤
      2 * Real.arcsin (2 / (5 * r)) := by
  have hr₀ : 0 < r := by rcases hr with rfl | rfl <;> norm_num
  have hs := canonical_corner_sum hx hy hfar
  have hxrange : -1 ≤ x / r ∧ x / r ≤ 1 := by
    rcases hr with rfl | rfl <;> constructor <;> nlinarith
  have hyrange : -1 ≤ y / r ∧ y / r ≤ 1 := by
    rcases hr with rfl | rfl <;> constructor <;> nlinarith
  let C := 1 - 2 * (2 / (5 * r)) ^ 2
  let X := Real.cos (Real.arcsin (x / r))
  let Y := Real.cos (Real.arcsin (y / r))
  have hX : 0 ≤ X := Real.cos_arcsin_nonneg _
  have hY : 0 ≤ Y := Real.cos_arcsin_nonneg _
  have hC : C = 17 / 25 ∨ C = 497 / 625 := by
    rcases hr with rfl | rfl <;> norm_num [C]
  have hquad := corner_quadratic hx hy hfar hC
  have hXsq : X ^ 2 = 1 - (x / r) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin (x / r))
    rw [Real.sin_arcsin hxrange.1 hxrange.2] at h
    dsimp [X]
    linarith
  have hYsq : Y ^ 2 = 1 - (y / r) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin (y / r))
    rw [Real.sin_arcsin hyrange.1 hyrange.2] at h
    dsimp [Y]
    linarith
  have hprod : (X * Y) ^ 2 = (1 - (x / r) ^ 2) * (1 - (y / r) ^ 2) := by
    rw [mul_pow, hXsq, hYsq]
  have hXY : C + (x / r) * (y / r) ≤ X * Y := by
    have hp := mul_nonneg (div_nonneg hx hr₀.le) (div_nonneg hy hr₀.le)
    rcases hr with rfl | rfl <;> dsimp [C] at * <;>
      nlinarith [mul_nonneg hX hY]
  have hcos : C ≤ Real.cos (Real.arcsin (x / r) + Real.arcsin (y / r)) := by
    rw [Real.cos_add, Real.sin_arcsin hxrange.1 hxrange.2,
      Real.sin_arcsin hyrange.1 hyrange.2]
    exact le_sub_iff_add_le.mpr hXY
  have htcos : Real.cos (2 * Real.arcsin (2 / (5 * r))) = C := by
    have hh := Real.sin_sq_add_cos_sq (Real.arcsin (2 / (5 * r)))
    rw [Real.sin_arcsin (by rcases hr with rfl | rfl <;> norm_num)
      (by rcases hr with rfl | rfl <;> norm_num)] at hh
    rw [Real.cos_two_mul]
    dsimp [C]
    nlinarith
  by_contra! hn
  have hcontr := Real.strictAntiOn_cos
    (show 2 * Real.arcsin (2 / (5 * r)) ∈ Set.Icc 0 Real.pi by
      constructor
      · positivity
      · linarith [Real.arcsin_le_pi_div_two (2 / (5 * r))])
    (show Real.arcsin (x / r) + Real.arcsin (y / r) ∈ Set.Icc 0 Real.pi by
      constructor
      · exact add_nonneg (Real.arcsin_nonneg.mpr (div_nonneg hx hr₀.le))
          (Real.arcsin_nonneg.mpr (div_nonneg hy hr₀.le))
      · linarith [Real.arcsin_le_pi_div_two (x / r), Real.arcsin_le_pi_div_two (y / r)]) hn
  rw [htcos] at hcontr
  linarith

/-- Closed interval extraction. The interval is allowed to cross the center
ray, including its isolated tangency with a far side. -/
lemma intervalLength_le_angularLength {K : UnitSquare}
    (C : SquareChart K (0, 0)) {r x y : ℝ} (hr : 0 < r)
    (hx : 0 ≤ x ∧ x < r) (hy : -r ≤ y ∧ y ≤ r) (hfarX : r ≤ x + 1)
    (ha : C.a = x + 1 / 2) (hb : C.b = y + 1 / 2) :
    intervalLength r x y ≤ angularLength K r := by
  by_cases hlen : 0 < intervalLength r x y
  · let A := Real.arccos (x / r)
    have hArange : A ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (div_nonneg hx.1 hr.le)⟩
    obtain ⟨arc, harc, _⟩ := arcFromChartInterval (0, 0) r {p | closedSquare K p}
      C.phase C.reversed (lowerAngle r x y) (upperAngle r x y) hlen (by
        dsimp [lowerAngle, upperAngle, intervalLength] at *
        have hlo := le_max_left (-A) (Real.arcsin (y / r))
        have hhi := min_le_left A (Real.arcsin ((y + 1) / r))
        dsimp [A] at hlo hhi
        linarith [hArange.2, Real.pi_pos]) (by
        intro θ hθ
        apply (C.closed_membership r θ).2
        have hlA : -A < θ := (le_max_left _ _).trans_lt hθ.1
        have hθA : θ < A := hθ.2.trans_le (min_le_left _ _)
        have hsinlo : Real.arcsin (y / r) < θ := (le_max_right _ _).trans_lt hθ.1
        have hsinhi : θ < Real.arcsin ((y + 1) / r) := hθ.2.trans_le (min_le_right _ _)
        have hθrange : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith [hArange.2]
        have hcos : x / r ≤ Real.cos θ := by
          have habs : |θ| ≤ A := (abs_le.mpr ⟨hlA.le, hθA.le⟩)
          have hh := Real.strictAntiOn_cos.antitoneOn
            (show |θ| ∈ Set.Icc 0 Real.pi by
              exact ⟨abs_nonneg _, habs.trans (by linarith [hArange.2, Real.pi_pos])⟩)
            (show A ∈ Set.Icc 0 Real.pi by
              exact ⟨hArange.1, by linarith [hArange.2, Real.pi_pos]⟩) habs
          simpa only [A, Real.cos_abs,
            Real.cos_arccos (show -1 ≤ x / r by positivity)
              (show x / r ≤ 1 by exact (div_le_one hr).2 hx.2.le)] using hh
        have hslo : y / r ≤ Real.sin θ := by
          have hh := Real.strictMonoOn_sin.monotoneOn
            (Real.arcsin_mem_Icc (y / r)) hθrange hsinlo.le
          rw [Real.sin_arcsin ((le_div_iff₀ hr).2 (by linarith [hy.1]))
            ((div_le_iff₀ hr).2 (by linarith [hy.2]))] at hh
          exact hh
        have hshi : Real.sin θ ≤ (y + 1) / r := by
          by_cases hcut : y + 1 ≤ r
          · have hh := Real.strictMonoOn_sin.monotoneOn hθrange
              (Real.arcsin_mem_Icc ((y + 1) / r)) hsinhi.le
            rw [Real.sin_arcsin ((le_div_iff₀ hr).2 (by linarith [hy.1]))
              ((div_le_iff₀ hr).2 hcut)] at hh
            exact hh
          · have hh : 1 ≤ (y + 1) / r := (le_div_iff₀ hr).2 (by linarith)
            exact (Real.sin_le_one θ).trans hh
        rw [ha, hb]
        constructor <;> apply abs_le.mpr
        · constructor
          · have hh := (le_div_iff₀ hr).mp hcos
            nlinarith
          · have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hr.le
            nlinarith
        · constructor
          · have hh := (le_div_iff₀ hr).mp hslo
            nlinarith
          · have hh := (div_le_iff₀ hr).mp hshi
            nlinarith)
    have hmeasure := angularLength_ge_arc arc
    rw [harc] at hmeasure
    dsimp [intervalLength]
    linarith
  · exact (le_of_not_gt hlen).trans (angularLength_nonneg K r)

lemma intervalLength_straddling (r x t : ℝ) :
    intervalLength r x (-t) =
      min (Real.arccos (x / r)) (Real.arcsin ((1 - t) / r)) +
        min (Real.arccos (x / r)) (Real.arcsin (t / r)) := by
  simp only [intervalLength, upperAngle, lowerAngle, neg_div, Real.arcsin_neg]
  rw [show -t + 1 = 1 - t by ring, max_neg_neg]
  ring

lemma intervalLength_corner {r x y : ℝ} (hr : 0 < r) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    intervalLength r x y =
      min (Real.arccos (x / r) - Real.arcsin (y / r))
        (Real.arcsin ((y + 1) / r) - Real.arcsin (y / r)) := by
  have hA : 0 ≤ Real.arccos (x / r) := Real.arccos_nonneg _
  have hY : 0 ≤ Real.arcsin (y / r) := Real.arcsin_nonneg.mpr (div_nonneg hy hr.le)
  dsimp [intervalLength, upperAngle, lowerAngle]
  rw [max_eq_right (by linarith)]
  rcases le_total (Real.arccos (x / r)) (Real.arcsin ((y + 1) / r)) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]

end TwoCircle

end SquaresInCircles.Eight
