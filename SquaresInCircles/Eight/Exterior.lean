module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import SquaresInCircles.Common.Frames
public import SquaresInCircles.Eight.Model

/-!
# Eight squares: the exterior squares

The angular length `angularLength K r` of a square on the circle of radius `r` about the origin is
the measure of the whole set of directions in which the circle meets the closed square, not the
span of its endpoints: the set may have several components and isolated points of tangency with
a side. Two interior-disjoint squares share only boundary points, finitely many on each circle,
so the angular lengths of the squares add up to at most `2π` on every circle
(`angularLength_budget`). A square in the closed disk of squared radius `98/25` whose interior
misses the origin has `3 L₁ + L_{5/4} ≥ π`, with equality only if `L₁ = π/3`
(`one_square_two_circle_inequality`), where `L₁` and `L_{5/4}` are its angular lengths on the
circles of radius `1` and `5/4`: the lower and upper angles of the square on each circle
(`TwoCircle`) bound the length from below, uniformly over the position of the square. If no
square of eight contained the origin, the budgets on the two circles would force `8π/3 ≤ 2π`
(`central_exists_from_one_square_inequality`).
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Set
namespace SquaresInCircles.Eight

local instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- Angular measure: the Haar measure of the circle `ℝ ⧸ 2πℤ`, of total mass `2π`. -/
noncomputable instance : MeasureSpace Direction :=
  inferInstanceAs (MeasureSpace (AddCircle (2 * Real.pi)))

/-- The angular measure is a Borel measure. -/
local instance centralCore_borelSpace : BorelSpace Direction :=
  inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi)))

/-- The angular measure is finite. -/
local instance centralCore_isFiniteMeasure : IsFiniteMeasure (volume : Measure Direction) :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure (AddCircle (2 * Real.pi))))

/-- The total angular measure is `2π`. -/
lemma centralCore_volume_univ :
    volume (univ : Set Direction) = ENNReal.ofReal (2 * Real.pi) :=
  AddCircle.measure_univ (2 * Real.pi)

/-- A closed angular ball of radius `ε` has measure `min (2π) (2ε)`. -/
lemma centralCore_volume_closedBall (x : Direction) (ε : ℝ) :
    volume (Metric.closedBall x ε) = ENNReal.ofReal (min (2 * Real.pi) (2 * ε)) :=
  AddCircle.volume_closedBall (2 * Real.pi) ε

/-- Single directions have angular measure zero. -/
local instance centralCore_nullSingletonClass : NullSingletonClass (volume : Measure Direction) :=
  ⟨fun x => by rw [← Metric.closedBall_zero, centralCore_volume_closedBall]; simp⟩

attribute [local fun_prop] Real.Angle.continuous_cos Real.Angle.continuous_sin

/-- The directions in which the circle of radius `r` about the origin meets the closed square;
the set may have any number of components. -/
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
    refine ((Set.finite_singleton (-θ)).insert θ).subset ?_
    intro ψ hψ
    have hh : ψ.cos = θ.cos := hψ.trans hθ.symm
    rcases Real.Angle.cos_eq_iff_eq_or_eq_neg.mp hh with h | h <;> simp [h]
  · simpa only [Set.not_nonempty_iff_eq_empty.mp h] using
      (Set.finite_empty : Set.Finite (∅ : Set Direction))

lemma finite_angle_sin_fiber (c : ℝ) : Set.Finite {θ : Direction | θ.sin = c} := by
  by_cases h : ({θ : Direction | θ.sin = c} : Set Direction).Nonempty
  · obtain ⟨θ, hθ⟩ := h
    refine ((Set.finite_singleton ((Real.pi : Direction) - θ)).insert θ).subset ?_
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
  simp only [localX, localY, frameX, frameY, circlePoint, zero_add, sub_eq_add_neg θ,
    Real.Angle.cos_add, Real.Angle.sin_add, Real.Angle.cos_neg, Real.Angle.sin_neg,
    Real.Angle.cos_coe, Real.Angle.sin_coe, hc, hs]
  constructor <;> ring

lemma finite_localX_circle_fiber (K : UnitSquare) {r : ℝ} (hr : r ≠ 0) (c : ℝ) :
    Set.Finite {θ : Direction | localX K (circlePoint (0, 0) r θ) = c} := by
  obtain ⟨φ, hc, hs⟩ := frame_angle K
  have hinj : Function.Injective (fun θ : Direction => θ - (φ : Direction)) := by
    intro x y h
    simpa using congrArg (fun z : Direction => z + (φ : Direction)) h
  have hfinite := (finite_angle_cos_fiber ((c + frameX K K.center) / r)).preimage hinj.injOn
  refine hfinite.subset ?_
  intro θ hθ
  change (θ - (φ : Direction)).cos = (c + frameX K K.center) / r
  change localX K (circlePoint (0, 0) r θ) = c at hθ
  rw [(local_circle_coordinates K r hc hs θ).1] at hθ
  apply (eq_div_iff hr).2
  linarith

lemma finite_localY_circle_fiber (K : UnitSquare) {r : ℝ} (hr : r ≠ 0) (c : ℝ) :
    Set.Finite {θ : Direction | localY K (circlePoint (0, 0) r θ) = c} := by
  obtain ⟨φ, hc, hs⟩ := frame_angle K
  have hinj : Function.Injective (fun θ : Direction => θ - (φ : Direction)) := by
    intro x y h
    simpa using congrArg (fun z : Direction => z + (φ : Direction)) h
  have hfinite := (finite_angle_sin_fiber ((c + frameY K K.center) / r)).preimage hinj.injOn
  refine hfinite.subset ?_
  intro θ hθ
  change (θ - (φ : Direction)).sin = (c + frameY K K.center) / r
  change localY K (circlePoint (0, 0) r θ) = c at hθ
  rw [(local_circle_coordinates K r hc hs θ).2] at hθ
  apply (eq_div_iff hr).2
  linarith

/-- On a circle of nonzero radius, the directions of the boundary points of a square are finitely
many, tangencies and corners included. -/
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
  simp only [Set.mem_union]
  rcases hboundary with h | h
  · rcases (abs_eq (show (0 : ℝ) ≤ 1 / 2 by norm_num)).mp h with h' | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr (show _ = _ by rw [h']; norm_num))
  · rcases (abs_eq (show (0 : ℝ) ≤ 1 / 2 by norm_num)).mp h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (show _ = _ by rw [h']; norm_num))

/-- The angular budget: on a circle of nonzero radius the angular lengths of interior-disjoint
squares add up to at most `2π`. The sets of directions need not be connected. -/
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
    (μ := (volume : Measure Direction))
    (s := Finset.univ)
    (fun i _ => (squareAngles_measurable (S i) r).nullMeasurableSet)
    (fun i _ j _ hij => hae i j hij)
  have hreal := ENNReal.toReal_mono (measure_ne_top volume Set.univ) hmu
  rw [centralCore_volume_univ, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_sum (fun i _ => measure_ne_top volume _)] at hreal
  simpa only [angularLength] using hreal

/-- Membership in the closed square in chart coordinates, from the open membership
`SquareChart.shifted_membership` by shrinking towards the centre of the square. -/
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
    ring_nf
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
      constructor <;> nlinarith only [hp.1, hp.2, abs_nonneg (r * Real.cos θ - C.a),
        abs_nonneg (r * Real.sin θ - C.b), ht₁, ht₀]
    constructor <;> apply bound_from_shrinks <;> intro t ht₀ ht₁
    · have h := (hh t ht₀ ht₁).1
      rw [(local_affine K K.center p (sub_add_cancel 1 t)).1] at h
      simpa [localX, abs_mul, abs_of_nonneg ht₀] using h.le
    · have h := (hh t ht₀ ht₁).2
      rw [(local_affine K K.center p (sub_add_cancel 1 t)).2] at h
      simpa [localY, abs_mul, abs_of_nonneg ht₀] using h.le

/-- An arc of directions in which the circle meets the closed square has width at most the
angular length of the square; its points may lie on the boundary of the square. -/
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
  rw [centralCore_volume_closedBall,
    min_eq_right (by linarith [A.atMostPi]),
    ENNReal.toReal_ofReal (by nlinarith only [A.positive, ht₀])] at hm
  dsimp [angularLength]
  linarith

/-- If every square whose interior misses the origin has `3 L₁ + L_{5/4} ≥ π`, with equality
only when `L₁ = π/3`, then one of eight interior-disjoint squares contains the origin in its
interior: otherwise the angular budgets on the two circles force equality for all eight squares,
and then `8π/3 ≤ 2π`. -/
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
absolute centre coordinates are strictly below five twelfths. -/
lemma containsCore_of_center_bounds {K : UnitSquare}
    (hx : alpha K (0, 0) < 5 / 12) (hy : beta K (0, 0) < 5 / 12) :
    ContainsCore K := by
  intro p hp
  have hf := frame_norm K p
  have hx' : |frameX K p| ≤ 1 / 12 := by
    have hs := sq_nonneg (frameY K p)
    dsimp [coreRadius] at hp
    nlinarith only [sq_abs (frameX K p), abs_nonneg (frameX K p), hp, hf]
  have hy' : |frameY K p| ≤ 1 / 12 := by
    have hs := sq_nonneg (frameX K p)
    dsimp [coreRadius] at hp
    nlinarith only [sq_abs (frameY K p), abs_nonneg (frameY K p), hp, hf]
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
  linarith

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
  linarith

/-- A closed square does not meet the interior of a square whose interior is disjoint from its
own: along a separating normal the support bound of the interior is strict, with no gap
assumed. -/
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

/-- `2 arcsin ((u + v)/2) ≤ arcsin u + arcsin v` for `u, v ≥ 0` with `u + v ≤ 1`, used on both
circles. The proof squares nonnegative quantities only, with no derivative of `arcsin` at `1`. -/
lemma arcsin_midpoint {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v ≤ 1) :
    2 * Real.arcsin ((u + v) / 2) ≤ Real.arcsin u + Real.arcsin v := by
  have hu₁ : u ≤ 1 := by linarith only [hv, hs]
  have hv₁ : v ≤ 1 := by linarith only [hu, hs]
  let X := Real.cos (Real.arcsin u)
  let Y := Real.cos (Real.arcsin v)
  let C := 1 - (u + v) ^ 2 / 2
  have hX : 0 ≤ X := Real.cos_arcsin_nonneg u
  have hY : 0 ≤ Y := Real.cos_arcsin_nonneg v
  have hXsq : X ^ 2 = 1 - u ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin u)
    rw [Real.sin_arcsin (by linarith only [hu]) hu₁] at h
    dsimp [X]
    linarith only [h]
  have hYsq : Y ^ 2 = 1 - v ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin v)
    rw [Real.sin_arcsin (by linarith only [hv]) hv₁] at h
    dsimp [Y]
    linarith only [h]
  have hprod : (X * Y) ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) := by
    rw [mul_pow, hXsq, hYsq]
  have hC : 0 ≤ C := by dsimp [C]; nlinarith only [sq_nonneg (u + v - 1), hs, hu, hv]
  have hp : 0 ≤ u * v := mul_nonneg hu hv
  have hid : (C + u * v) ^ 2 - (X * Y) ^ 2 =
      (u + v) ^ 2 * (u - v) ^ 2 / 4 := by
    dsimp [C]
    rw [hprod]
    ring
  have hm := mul_nonneg (sq_nonneg (u + v)) (sq_nonneg (u - v))
  have hXY : X * Y ≤ C + u * v := by
    nlinarith only [mul_nonneg hX hY, hid, hm, hC, hp]
  have hsumcos : Real.cos (Real.arcsin u + Real.arcsin v) ≤ C := by
    rw [Real.cos_add, Real.sin_arcsin (by linarith only [hu]) hu₁,
      Real.sin_arcsin (by linarith only [hv]) hv₁]
    exact sub_le_iff_le_add.mpr hXY
  have htarget : Real.cos (2 * Real.arcsin ((u + v) / 2)) = C := by
    have hh := Real.sin_sq_add_cos_sq (Real.arcsin ((u + v) / 2))
    rw [Real.sin_arcsin (by linarith only [hu, hv]) (by linarith only [hs])] at hh
    rw [Real.cos_two_mul]
    dsimp [C]
    linarith only [hh]
  have hrange : Real.arcsin u + Real.arcsin v ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact add_nonneg (Real.arcsin_nonneg.mpr hu) (Real.arcsin_nonneg.mpr hv)
    · linarith only [Real.arcsin_le_pi_div_two u, Real.arcsin_le_pi_div_two v]
  have htrange : 2 * Real.arcsin ((u + v) / 2) ∈ Set.Icc 0 Real.pi := by
    constructor
    · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by linarith only [hu, hv]))
    · linarith only [Real.arcsin_le_pi_div_two ((u + v) / 2)]
  by_contra! hn
  have hc := Real.strictAntiOn_cos hrange htrange hn
  rw [htarget] at hc
  linarith only [hsumcos, hc]

lemma two_arcsin_quarter_lt : 2 * Real.arcsin (1 / 4 : ℝ) < Real.pi / 6 := by
  have hA : 0 ≤ Real.arcsin (1 / 4 : ℝ) := Real.arcsin_nonneg.mpr (by norm_num)
  have hA' : Real.arcsin (1 / 4 : ℝ) < Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hcos := Real.cos_arcsin (1 / 4 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - (1 / 4 : ℝ) ^ 2 by norm_num)
  have hsin : Real.sin (2 * Real.arcsin (1 / 4 : ℝ)) < 1 / 2 := by
    rw [Real.sin_two_mul, Real.sin_arcsin (by norm_num) (by norm_num), hcos]
    nlinarith only [Real.sqrt_nonneg (1 - (1 / 4 : ℝ) ^ 2), hs]
  by_contra! hn
  have hh := Real.strictMonoOn_sin.monotoneOn
    (show Real.pi / 6 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show 2 * Real.arcsin (1 / 4 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) hn
  rw [Real.sin_pi_div_six] at hh
  linarith

lemma canonical_x_bound {x y : ℝ} (hy : -1 / 2 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25) : x < 11 / 12 := by
  have hysq : 1 / 4 ≤ (y + 1) ^ 2 := by nlinarith only [hy]
  linarith [sq_nonneg (x - 11 / 12)]

lemma canonical_corner_sum {x y : ℝ} (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25) :
    x + y ≤ 4 / 5 := by
  linarith [sq_nonneg (x - y), sq_nonneg (x + y - 4 / 5)]

/-- The polynomial inequality behind `corner_arcsin_sum` in the corner branch, for the two
values `cos(2 asin(2/5)) = 17/25` and `cos(2 asin(8/25)) = 497/625` of `C`. -/
lemma corner_quadratic {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25)
    (hC : C = 17 / 25 ∨ C = 497 / 625) :
    x ^ 2 + y ^ 2 + 2 * C * x * y ≤ 16 / 25 * C + 8 / 25 * (1 - C) := by
  have hs := canonical_corner_sum hfar
  have hp := mul_nonneg hx hy
  by_cases hlow : x + y ≤ 7 / 10
  · have hsq := mul_nonneg (sub_nonneg.2 hlow)
      (show (0 : ℝ) ≤ 7 / 10 + (x + y) by linarith only [hx, hy])
    rcases hC with rfl | rfl <;> linarith only [hsq, hp]
  · have hprod : 0 ≤ (4 / 5 - (x + y)) *
        (C * (x + y + 4 / 5) - 2 * (1 - C)) := by
      apply mul_nonneg (by linarith only [hs])
      rcases hC with rfl | rfl <;> linarith only [hlow]
    have hscale : (1 - C) * ((x + 1) ^ 2 + (y + 1) ^ 2) ≤ (1 - C) * (98 / 25) :=
      mul_le_mul_of_nonneg_left hfar (by rcases hC with rfl | rfl <;> norm_num)
    linarith only [hprod, hscale]

lemma corner_arcsin_sum {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25)
    (hr : r = 1 ∨ r = 5 / 4) :
    Real.arcsin (x / r) + Real.arcsin (y / r) ≤
      2 * Real.arcsin (2 / (5 * r)) := by
  have hr₀ : 0 < r := by rcases hr with rfl | rfl <;> norm_num
  have hs := canonical_corner_sum hfar
  have hxrange : -1 ≤ x / r ∧ x / r ≤ 1 := by
    rcases hr with rfl | rfl <;> constructor <;> linarith only [hx, hy, hs]
  have hyrange : -1 ≤ y / r ∧ y / r ≤ 1 := by
    rcases hr with rfl | rfl <;> constructor <;> linarith only [hy, hx, hs]
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
    linarith only [h]
  have hYsq : Y ^ 2 = 1 - (y / r) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin (y / r))
    rw [Real.sin_arcsin hyrange.1 hyrange.2] at h
    dsimp [Y]
    linarith only [h]
  have hprod : (X * Y) ^ 2 = (1 - (x / r) ^ 2) * (1 - (y / r) ^ 2) := by
    rw [mul_pow, hXsq, hYsq]
  have hXY : C + (x / r) * (y / r) ≤ X * Y := by
    have hp := mul_nonneg (div_nonneg hx hr₀.le) (div_nonneg hy hr₀.le)
    have hsq : (C + (x / r) * (y / r)) ^ 2 ≤ (X * Y) ^ 2 := by
      rw [hprod]
      rcases hr with rfl | rfl <;> dsimp only [C] at hquad ⊢ <;> linarith only [hquad]
    exact le_of_sq_le_sq hsq (mul_nonneg hX hY)
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
    linarith only [hh]
  by_contra! hn
  have hcontr := Real.strictAntiOn_cos
    (show 2 * Real.arcsin (2 / (5 * r)) ∈ Set.Icc 0 Real.pi by
      constructor
      · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (by positivity))
      · linarith only [Real.arcsin_le_pi_div_two (2 / (5 * r))])
    (show Real.arcsin (x / r) + Real.arcsin (y / r) ∈ Set.Icc 0 Real.pi by
      constructor
      · exact add_nonneg (Real.arcsin_nonneg.mpr (div_nonneg hx hr₀.le))
          (Real.arcsin_nonneg.mpr (div_nonneg hy hr₀.le))
      · linarith only [Real.arcsin_le_pi_div_two (x / r), Real.arcsin_le_pi_div_two (y / r)]) hn
  rw [htcos] at hcontr
  linarith only [hcos, hcontr]

/-- The closed interval of directions given by the chart is at most the angular length; it may
cross the centre ray, where the circle can touch a far side at an isolated point. -/
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
      C.phase C.reversed (lowerAngle r x y) (upperAngle r x y) (sub_pos.mp hlen) (by
        dsimp [lowerAngle, upperAngle, intervalLength] at *
        have hlo := le_max_left (-A) (Real.arcsin (y / r))
        have hhi := min_le_left A (Real.arcsin ((y + 1) / r))
        dsimp [A] at hlo hhi
        linarith only [hArange.2, Real.pi_pos, hlen, hlo, hhi]) (by
        intro θ hθ
        apply (SquareChart.closed_membership C r θ).2
        have hlA : -A < θ := (le_max_left _ _).trans_lt hθ.1
        have hθA : θ < A := hθ.2.trans_le (min_le_left _ _)
        have hsinlo : Real.arcsin (y / r) < θ := (le_max_right _ _).trans_lt hθ.1
        have hsinhi : θ < Real.arcsin ((y + 1) / r) := hθ.2.trans_le (min_le_right _ _)
        have hθrange : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> linarith only [hArange.2, hlA, hθA]
        have hcos : x / r ≤ Real.cos θ := by
          have habs : |θ| ≤ A := (abs_le.mpr ⟨hlA.le, hθA.le⟩)
          have hh := Real.strictAntiOn_cos.antitoneOn
            (show |θ| ∈ Set.Icc 0 Real.pi by
              exact ⟨abs_nonneg _,
                habs.trans (by linarith only [hArange.2, Real.pi_pos, hlA, hθA])⟩)
            (show A ∈ Set.Icc 0 Real.pi by
              exact ⟨hArange.1, by linarith only [hArange.2, Real.pi_pos, hlA, hθA]⟩) habs
          simpa only [A, Real.cos_abs,
            Real.cos_arccos (show -1 ≤ x / r by linarith only [div_nonneg hx.1 hr.le, hx, hr])
              (show x / r ≤ 1 by exact (div_le_one hr).2 hx.2.le)] using hh
        have hslo : y / r ≤ Real.sin θ := by
          have hh := Real.strictMonoOn_sin.monotoneOn
            (Real.arcsin_mem_Icc (y / r)) hθrange hsinlo.le
          rw [Real.sin_arcsin ((le_div_iff₀ hr).2 (by linarith only [hy.1]))
            ((div_le_iff₀ hr).2 (by linarith only [hy.2]))] at hh
          exact hh
        have hshi : Real.sin θ ≤ (y + 1) / r := by
          by_cases hcut : y + 1 ≤ r
          · have hh := Real.strictMonoOn_sin.monotoneOn hθrange
              (Real.arcsin_mem_Icc ((y + 1) / r)) hsinhi.le
            rw [Real.sin_arcsin ((le_div_iff₀ hr).2 (by linarith only [hy.1]))
              ((div_le_iff₀ hr).2 (by linarith only [hcut]))] at hh
            exact hh
          · have hh : 1 ≤ (y + 1) / r := (le_div_iff₀ hr).2 (by linarith only [hcut])
            exact (Real.sin_le_one θ).trans hh
        rw [ha, hb]
        constructor <;> apply abs_le.mpr
        · constructor
          · have hh := (div_le_iff₀ hr).mp hcos
            linarith only [hh]
          · have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hr.le
            linarith only [hfarX, hh]
        · constructor
          · have hh := (div_le_iff₀ hr).mp hslo
            linarith only [hh]
          · have hh := (le_div_iff₀ hr).mp hshi
            linarith only [hh])
    have hmeasure := angularLength_ge_arc arc
    rw [harc] at hmeasure
    dsimp [intervalLength]
    linarith only [hmeasure]
  · exact (le_of_not_gt hlen).trans (angularLength_nonneg K r)

lemma intervalLength_straddling (r x t : ℝ) :
    intervalLength r x (-t) =
      min (Real.arccos (x / r)) (Real.arcsin ((1 - t) / r)) +
        min (Real.arccos (x / r)) (Real.arcsin (t / r)) := by
  simp only [intervalLength, upperAngle, lowerAngle, neg_div, Real.arcsin_neg]
  rw [show -t + 1 = 1 - t by ring, max_neg_neg]
  ring

lemma intervalLength_corner {r x y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
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

lemma arcsin_increment_lower {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    Real.arcsin (v - u) ≤ Real.arcsin v - Real.arcsin u := by
  let d := Real.arcsin v - Real.arcsin u
  have hd₀ : 0 ≤ d := sub_nonneg.mpr (Real.arcsin_le_arcsin huv)
  have hd₁ : d ≤ Real.pi / 2 := by
    dsimp [d]
    linarith [Real.arcsin_le_pi_div_two v, Real.arcsin_nonneg.mpr hu]
  have hsin₀ : 0 ≤ Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd₀
    (by linarith [Real.pi_pos])
  have hident : v = u * Real.cos d + Real.cos (Real.arcsin u) * Real.sin d := by
    have h := Real.sin_add (Real.arcsin u) d
    rw [show Real.arcsin u + d = Real.arcsin v by dsimp [d]; ring,
      Real.sin_arcsin (by linarith) hv,
      Real.sin_arcsin (by linarith) (huv.trans hv)] at h
    exact h
  have h₁ := mul_le_mul_of_nonneg_left (Real.cos_le_one d) hu
  have h₂ := mul_le_mul_of_nonneg_right (Real.cos_le_one (Real.arcsin u)) hsin₀
  apply (Real.arcsin_le_iff_le_sin
    (show v - u ∈ Set.Icc (-1) 1 by constructor <;> linarith)
    (show d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      exact ⟨by linarith [Real.pi_pos], hd₁⟩)).2
  linarith

lemma straddling_polynomial_upper {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 ≤ t ∧ t ≤ 1 / 2)
    (hfar : (x + 1) ^ 2 + (1 - t) ^ 2 ≤ 98 / 25) :
    x < 71 / 100 + 3 / 5 * t - t ^ 2 / 4 := by
  let P := 71 / 100 + 3 / 5 * t - t ^ 2 / 4
  have htq : t ^ 2 ≤ t / 2 := by linarith only [mul_nonneg ht.1 (show 0 ≤ 1 / 2 - t by linarith),
    ht]
  have hP : 0 ≤ P := by dsimp [P]; linarith only [ht, htq]
  have hcubic := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 / 2 - t by linarith only [ht])
  have hpol : 98 / 25 - (1 - t) ^ 2 < (P + 1) ^ 2 := by
    dsimp [P]
    nlinarith only [sq_nonneg (t ^ 2), ht, hcubic]
  dsimp [P] at *
  nlinarith

lemma straddling_unit_angle {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 ≤ t ∧ t ≤ 1 / 2)
    (hfar : (x + 1) ^ 2 + (1 - t) ^ 2 ≤ 98 / 25) :
    Real.arccos (5 / 7 : ℝ) < Real.arccos x + Real.arcsin t := by
  have hxmax := canonical_x_bound (show (-1 / 2 : ℝ) ≤ -t by linarith only [ht])
    (by linarith only [hfar] : (x + 1) ^ 2 + (-t + 1) ^ 2 ≤ 98 / 25)
  have hxP := straddling_polynomial_upper hx ht hfar
  let A := Real.arccos (5 / 7 : ℝ)
  let B := Real.arcsin t
  have hB₀ : 0 ≤ B := Real.arcsin_nonneg.mpr ht.1
  have hcosB₀ : 0 ≤ Real.cos B := Real.cos_arcsin_nonneg _
  have hcosBsq : (Real.cos B) ^ 2 = 1 - t ^ 2 := by
    have hh := Real.sin_sq_add_cos_sq B
    have he : Real.sin B = t := Real.sin_arcsin (by linarith only [ht]) (by linarith only [ht])
    rw [he] at hh
    linarith only [hh]
  have htq : t ^ 2 ≤ t / 2 := by linarith only [mul_nonneg ht.1 (show 0 ≤ 1 / 2 - t by linarith),
    ht]
  have htq' : t ^ 2 ≤ 1 / 4 := by linarith only [ht, htq]
  have hcosB : 1 - 3 / 5 * t ^ 2 ≤ Real.cos B := by
    have hfourth := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 / 4 - t ^ 2 by linarith only [ht, htq])
    have hsq : (1 - 3 / 5 * t ^ 2) ^ 2 ≤ (Real.cos B) ^ 2 := by
      rw [hcosBsq]; linarith only [sq_nonneg t, hfourth]
    exact (abs_le_of_sq_le_sq' hsq hcosB₀).2
  have hsinA : 69 / 100 < Real.sin A := by
    dsimp only [A]
    rw [Real.sin_arccos]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  have htarget : x < Real.cos (A - B) := by
    rw [Real.cos_sub, show Real.cos A = 5 / 7 by
      exact Real.cos_arccos (by norm_num) (by norm_num),
      show Real.sin B = t by exact Real.sin_arcsin (by linarith only [ht]) (by linarith only [ht])]
    have hmul := mul_le_mul_of_nonneg_right hsinA.le ht.1
    linarith only [hx, hxP, htq, hcosB, hmul]
  by_cases hAB : 0 ≤ A - B
  · have hcosX : Real.cos (Real.arccos x) = x :=
      Real.cos_arccos (by linarith only [hx]) (by linarith only [hxmax])
    by_contra! hn
    have hac : Real.arccos x ≤ A - B := by dsimp [A, B] at *; linarith only [hn]
    have hh := Real.strictAntiOn_cos.antitoneOn
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      (show A - B ∈ Set.Icc 0 Real.pi by
        exact ⟨hAB, by linarith only [Real.arccos_le_pi (5 / 7 : ℝ), hB₀]⟩) hac
    rw [hcosX] at hh
    linarith only [htarget, hh]
  · dsimp [A, B] at *
    linarith only [Real.arccos_nonneg x, hAB]

lemma straddling_larger_angle {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 ≤ t ∧ t ≤ 1 / 2)
    (hfar : (x + 1) ^ 2 + (1 - t) ^ 2 ≤ 98 / 25) :
    2 * Real.arcsin (2 / 5 : ℝ) <
      Real.arccos (x / (5 / 4)) + Real.arcsin (t / (5 / 4)) := by
  have hxmax := canonical_x_bound (show (-1 / 2 : ℝ) ≤ -t by linarith only [ht])
    (by linarith only [hfar] : (x + 1) ^ 2 + (-t + 1) ^ 2 ≤ 98 / 25)
  have hxP := straddling_polynomial_upper hx ht hfar
  let A := 2 * Real.arcsin (2 / 5 : ℝ)
  let B := Real.arcsin (t / (5 / 4))
  have hB₀ : 0 ≤ B := Real.arcsin_nonneg.mpr (div_nonneg ht.1 (by norm_num))
  have hcosB₀ : 0 ≤ Real.cos B := Real.cos_arcsin_nonneg _
  have hcosBsq : (Real.cos B) ^ 2 = 1 - (t / (5 / 4)) ^ 2 := by
    have hh := Real.sin_sq_add_cos_sq B
    rw [show Real.sin B = t / (5 / 4) by
      exact Real.sin_arcsin (by linarith only [ht]) (by linarith only [ht])] at hh
    linarith only [hh]
  have htq : t ^ 2 ≤ t / 2 := by linarith only [mul_nonneg ht.1 (show 0 ≤ 1 / 2 - t by linarith),
    ht]
  have hcosB : 1 - (t / (5 / 4)) ^ 2 ≤ Real.cos B := by
    have hh := mul_nonneg (sq_nonneg (t / (5 / 4)))
      (show 0 ≤ 1 - (t / (5 / 4)) ^ 2 by linarith only [ht, htq])
    have hsq : (1 - (t / (5 / 4)) ^ 2) ^ 2 ≤ (Real.cos B) ^ 2 := by rw [hcosBsq]; linarith only [hh]
    exact (abs_le_of_sq_le_sq' hsq hcosB₀).2
  have hcosA : Real.cos A = 17 / 25 := by
    have hh := Real.sin_sq_add_cos_sq (Real.arcsin (2 / 5 : ℝ))
    rw [Real.sin_arcsin (by norm_num) (by norm_num)] at hh
    dsimp only [A]
    rw [Real.cos_two_mul]
    linarith only [hh]
  have hsinA : 7 / 10 < Real.sin A := by
    dsimp only [A]
    rw [Real.sin_two_mul, Real.sin_arcsin (by norm_num) (by norm_num), Real.cos_arcsin]
    have hs := Real.lt_sqrt_of_sq_lt (show (7 / 8 : ℝ) ^ 2 < 1 - (2 / 5 : ℝ) ^ 2 by norm_num)
    linarith only [hs]
  have htarget : x / (5 / 4) < Real.cos (A - B) := by
    rw [Real.cos_sub, hcosA, show Real.sin B = t / (5 / 4) by
      exact Real.sin_arcsin (by linarith only [ht]) (by linarith only [ht])]
    have hmul := mul_le_mul_of_nonneg_right hsinA.le
      (show 0 ≤ t / (5 / 4) from div_nonneg ht.1 (by norm_num))
    linarith only [sq_nonneg t, hxmax, hxP, htq, hcosB, hmul]
  by_cases hAB : 0 ≤ A - B
  · have hcosX : Real.cos (Real.arccos (x / (5 / 4))) = x / (5 / 4) :=
      Real.cos_arccos (by linarith only [hx]) (by linarith only [hxmax])
    by_contra! hn
    have hac : Real.arccos (x / (5 / 4)) ≤ A - B := by dsimp [A, B] at *; linarith only [hn]
    have hh := Real.strictAntiOn_cos.antitoneOn
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      (show A - B ∈ Set.Icc 0 Real.pi by
        exact ⟨hAB, by dsimp [A]; linarith only [Real.arcsin_le_pi_div_two (2 / 5 : ℝ), hB₀]⟩) hac
    rw [hcosX] at hh
    linarith only [htarget, hh]
  · dsimp [A, B] at *
    linarith only [Real.arccos_nonneg (x / (5 / 4)), hAB]

lemma weighted_straddling_constant :
    Real.pi < 3 * Real.arccos (5 / 7 : ℝ) + 2 * Real.arcsin (2 / 5 : ℝ) := by
  let A := Real.arccos (5 / 7 : ℝ)
  let B := Real.arcsin (2 / 5 : ℝ)
  have hA₀ : 0 ≤ A := Real.arccos_nonneg _
  have hA₁ : A < Real.pi / 3 := by
    rw [← arccos_half]
    exact Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have hB₀ : 0 ≤ B := Real.arcsin_nonneg.mpr (by norm_num)
  have hB₁ : B < Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hca : Real.cos (3 * A) = -235 / 343 := by
    rw [Real.cos_three_mul, show Real.cos A = 5 / 7 by
      exact Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num
  have hcb : Real.cos (Real.pi - 2 * B) = -17 / 25 := by
    have hh := Real.sin_sq_add_cos_sq B
    rw [show Real.sin B = 2 / 5 by exact Real.sin_arcsin (by norm_num) (by norm_num)] at hh
    rw [Real.cos_pi_sub, Real.cos_two_mul]
    linarith
  by_contra! hn
  have hle : 3 * A ≤ Real.pi - 2 * B := by dsimp [A, B] at *; linarith
  have hh := Real.strictAntiOn_cos.antitoneOn
    (show 3 * A ∈ Set.Icc 0 Real.pi by constructor <;> linarith)
    (show Real.pi - 2 * B ∈ Set.Icc 0 Real.pi by constructor <;> linarith) hle
  rw [hca, hcb] at hh
  norm_num at hh

lemma weighted_corner_constant :
    6 * Real.arcsin (2 / 5 : ℝ) + 2 * Real.arcsin (8 / 25 : ℝ) < Real.pi := by
  let B := Real.arcsin (2 / 5 : ℝ)
  let G := Real.arcsin (8 / 25 : ℝ)
  have hB₀ : 0 ≤ B := Real.arcsin_nonneg.mpr (by norm_num)
  have hG₀ : 0 ≤ G := Real.arcsin_nonneg.mpr (by norm_num)
  have hB₁ : B < Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hG₁ : G < Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hsin : Real.sin (3 * B) = 118 / 125 := by
    rw [Real.sin_three_mul, show Real.sin B = 2 / 5 by
      exact Real.sin_arcsin (by norm_num) (by norm_num)]
    norm_num
  have hcos : 118 / 125 < Real.cos G := by
    dsimp only [G]
    rw [Real.cos_arcsin]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  by_contra! hn
  have hle : Real.pi / 2 - G ≤ 3 * B := by dsimp [B, G] at *; linarith
  have hh := Real.strictMonoOn_sin.monotoneOn
    (show Real.pi / 2 - G ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
    (show 3 * B ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) hle
  rw [Real.sin_pi_div_two_sub, hsin] at hh
  linarith

lemma corner_larger_far_side :
    Real.pi / 2 - 2 * Real.arcsin (8 / 25 : ℝ) < Real.arcsin (4 / 5 : ℝ) := by
  let G := Real.arcsin (8 / 25 : ℝ)
  have hG₀ : 0 ≤ G := Real.arcsin_nonneg.mpr (by norm_num)
  have hG₁ : G < Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_lt_arcsin (by norm_num) (by norm_num) (by norm_num)
  have hc : Real.sin (Real.pi / 2 - 2 * G) = 497 / 625 := by
    have hh := Real.sin_sq_add_cos_sq G
    rw [show Real.sin G = 8 / 25 by exact Real.sin_arcsin (by norm_num) (by norm_num)] at hh
    rw [Real.sin_pi_div_two_sub, Real.cos_two_mul]
    linarith
  by_contra! hn
  have hh := Real.strictMonoOn_sin.monotoneOn
    (Real.arcsin_mem_Icc (4 / 5 : ℝ))
    (show Real.pi / 2 - 2 * G ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos]) hn
  rw [Real.sin_arcsin (by norm_num) (by norm_num), hc] at hh
  norm_num at hh

lemma small_straddling_length {x t : ℝ} (hx : 0 ≤ x ∧ x < 1 / 4)
    (ht : 0 ≤ t ∧ t ≤ 1 / 2) : Real.pi / 3 ≤ intervalLength 1 x (-t) := by
  rw [intervalLength_straddling]
  simp only [div_one]
  have hA : Real.pi / 3 < Real.arccos x := by
    rw [← arccos_half]
    exact Real.arccos_lt_arccos (by linarith) (by linarith) (by norm_num)
  have hC : Real.arcsin t ≤ Real.pi / 6 := by
    rw [← arcsin_half]
    exact Real.arcsin_le_arcsin ht.2
  have hC₀ : 0 ≤ Real.arcsin t := Real.arcsin_nonneg.mpr ht.1
  have hsum := arcsin_midpoint (u := 1 - t) (v := t) (by linarith) ht.1 (by linarith)
  norm_num [arcsin_half] at hsum
  rw [min_eq_right (by linarith : Real.arcsin t ≤ Real.arccos x)]
  rcases le_total (Real.arccos x) (Real.arcsin (1 - t)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

lemma general_straddling_unit_length {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 ≤ t ∧ t ≤ 1 / 2)
    (hfar : (x + 1) ^ 2 + (1 - t) ^ 2 ≤ 98 / 25) :
    Real.arccos (5 / 7 : ℝ) < intervalLength 1 x (-t) := by
  rw [intervalLength_straddling]
  simp only [div_one]
  have hAC := straddling_unit_angle hx ht hfar
  have hmax := canonical_x_bound (show (-1 / 2 : ℝ) ≤ -t by linarith only [ht])
    (by linarith only [hfar] : (x + 1) ^ 2 + (-t + 1) ^ 2 ≤ 98 / 25)
  have hBC := arcsin_midpoint (u := 1 - t) (v := t) (by linarith only [ht]) ht.1
    (by linarith only [])
  norm_num [arcsin_half] at hBC
  have hAlpha : Real.arccos (5 / 7 : ℝ) < Real.pi / 3 := by
    rw [← arccos_half]
    exact Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have h2A : Real.arccos (5 / 7 : ℝ) < 2 * Real.arccos x := by
    have hcos : Real.cos (2 * Real.arccos x) < 5 / 7 := by
      rw [Real.cos_two_mul, Real.cos_arccos (by linarith only [hx]) (by linarith only [hmax])]
      nlinarith only [hmax, hx]
    by_contra! hn
    have hh := Real.strictAntiOn_cos.antitoneOn
      (show 2 * Real.arccos x ∈ Set.Icc 0 Real.pi by
        constructor
        · exact mul_nonneg (by norm_num) (Real.arccos_nonneg x)
        · linarith only [Real.arccos_le_pi_div_two.mpr hx, hx])
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩ hn
    rw [Real.cos_arccos (by norm_num) (by norm_num)] at hh
    linarith only [hcos, hh]
  have hCB : Real.arcsin t ≤ Real.arcsin (1 - t) := Real.arcsin_le_arcsin (by linarith only [ht])
  rcases le_total (Real.arccos x) (Real.arcsin t) with h | h
  · rw [min_eq_left (h.trans hCB), min_eq_left h]
    linarith only [h2A]
  · rw [min_eq_right h]
    rcases le_total (Real.arccos x) (Real.arcsin (1 - t)) with hh | hh
    · rw [min_eq_left hh]
      exact hAC
    · rw [min_eq_right hh]
      linarith only [hBC, hAlpha]

lemma general_straddling_larger_length {x t : ℝ} (hx : 0 ≤ x)
    (ht : 0 ≤ t ∧ t ≤ 1 / 2)
    (hfar : (x + 1) ^ 2 + (1 - t) ^ 2 ≤ 98 / 25) :
    2 * Real.arcsin (2 / 5 : ℝ) ≤ intervalLength (5 / 4) x (-t) := by
  rw [intervalLength_straddling]
  have hAC := straddling_larger_angle hx ht hfar
  have hBC := arcsin_midpoint (u := (1 - t) / (5 / 4)) (v := t / (5 / 4))
    (div_nonneg (by linarith only [ht]) (by norm_num)) (div_nonneg ht.1 (by norm_num))
    (by norm_num; linarith only [])
  have hmid : (((1 - t) / (5 / 4) + t / (5 / 4)) / 2) = (2 / 5 : ℝ) := by ring
  rw [hmid] at hBC
  have hmax := canonical_x_bound (show (-1 / 2 : ℝ) ≤ -t by linarith only [ht])
    (by linarith only [hfar] : (x + 1) ^ 2 + (-t + 1) ^ 2 ≤ 98 / 25)
  have hCA : Real.arcsin (t / (5 / 4)) ≤ Real.arccos (x / (5 / 4)) := by
    have hsq := Real.sin_sq_add_cos_sq (Real.arcsin (t / (5 / 4)))
    rw [Real.sin_arcsin (by linarith only [ht]) (by linarith only [ht])] at hsq
    have hcos₀ := Real.cos_arcsin_nonneg (t / (5 / 4))
    by_contra! hn
    have hh := Real.strictAntiOn_cos.antitoneOn
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      (show Real.arcsin (t / (5 / 4)) ∈ Set.Icc 0 Real.pi by
        exact ⟨Real.arcsin_nonneg.mpr (div_nonneg ht.1 (by norm_num)),
          (Real.arcsin_le_pi_div_two _).trans (by linarith only [Real.pi_pos])⟩) hn.le
    rw [Real.cos_arccos (by linarith only [hx]) (by linarith only [hmax])] at hh
    nlinarith only [ht, hfar, hsq, hx, hmax, hh, hcos₀]
  rw [min_eq_right hCA]
  rcases le_total (Real.arccos (x / (5 / 4)))
      (Real.arcsin ((1 - t) / (5 / 4))) with h | h
  · rw [min_eq_left h]
    exact hAC.le
  · rw [min_eq_right h]
    exact hBC

lemma small_corner_length {x y : ℝ} (hx : 0 ≤ x ∧ x < 1 / 4)
    (hy : 0 ≤ y ∧ y ≤ x) : Real.pi / 3 < intervalLength 1 x y := by
  rw [intervalLength_corner (by norm_num) hy.1]
  simp only [div_one]
  rw [Real.arcsin_of_one_le (by linarith : 1 ≤ y + 1)]
  have hA := Real.arccos_le_pi_div_two.mpr hx.1
  rw [min_eq_left (by linarith), Real.arccos_eq_pi_div_two_sub_arcsin]
  have hX := Real.arcsin_le_arcsin hx.2.le
  have hY := Real.arcsin_le_arcsin (hy.2.trans hx.2.le)
  linarith [two_arcsin_quarter_lt]

lemma corner_unit_length {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25) :
    Real.pi / 2 - 2 * Real.arcsin (2 / 5 : ℝ) ≤ intervalLength 1 x y := by
  rw [intervalLength_corner (by norm_num) hy]
  simp only [div_one]
  rw [Real.arcsin_of_one_le (by linarith : 1 ≤ y + 1)]
  have hA := Real.arccos_le_pi_div_two.mpr hx
  rw [min_eq_left (by linarith), Real.arccos_eq_pi_div_two_sub_arcsin]
  have hh := corner_arcsin_sum hx hy hfar (r := 1) (Or.inl rfl)
  norm_num at hh
  linarith

lemma corner_larger_length {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25) :
    Real.pi / 2 - 2 * Real.arcsin (8 / 25 : ℝ) ≤ intervalLength (5 / 4) x y := by
  rw [intervalLength_corner (by norm_num) hy]
  apply le_min
  · rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    have hh := corner_arcsin_sum hx hy hfar (r := 5 / 4) (Or.inr rfl)
    norm_num at hh
    linarith
  · by_cases hcut : y + 1 ≤ 5 / 4
    · have hh := arcsin_increment_lower (u := y / (5 / 4))
        (v := (y + 1) / (5 / 4)) (by positivity) (by linarith) (by linarith)
      rw [show (y + 1) / (5 / 4) - y / (5 / 4) = (4 / 5 : ℝ) by ring] at hh
      exact corner_larger_far_side.le.trans hh
    · rw [Real.arcsin_of_one_le (by linarith : 1 ≤ (y + 1) / (5 / 4))]
      have hh := corner_arcsin_sum hx hy hfar (r := 5 / 4) (Or.inr rfl)
      have hX := Real.arcsin_nonneg.mpr (show 0 ≤ x / (5 / 4) by positivity)
      norm_num at hh
      linarith

end TwoCircle

/-- The one-square two-circle inequality: a square in the disk of squared radius `98/25` whose
interior misses the origin has `3 L₁ + L_{5/4} ≥ π`, with equality only when `L₁ = π/3`, the case
of equality that the sum over the eight squares uses. The proof measures the whole sets of
directions and bounds them below by intervals where that suffices. -/
theorem one_square_two_circle_inequality (K : UnitSquare)
    (hcontain : SqContained (98 / 25) K) (hout : ¬ openSquare K (0, 0)) :
    Real.pi ≤ 3 * angularLength K 1 + angularLength K (5 / 4) ∧
      (3 * angularLength K 1 + angularLength K (5 / 4) = Real.pi →
        angularLength K 1 = Real.pi / 3) := by
  obtain ⟨C, hsort⟩ := sorted_square_chart K (0, 0)
  let x := C.a - 1 / 2
  let y := C.b - 1 / 2
  have hx : 0 ≤ x := by dsimp [x]; linarith only [C.exterior hsort hout, hsort, hout]
  have hy : -1 / 2 ≤ y := by dsimp [y]; linarith only [C.nonneg.2]
  have hyx : y ≤ x := by dsimp [x, y]; linarith only [hsort]
  have hfar : (x + 1) ^ 2 + (y + 1) ^ 2 ≤ 98 / 25 := by
    have hh := chart_phi C hcontain
    dsimp [phi, x, y] at *
    linarith only [hh]
  have hxmax := TwoCircle.canonical_x_bound hy hfar
  have hL₁ : TwoCircle.intervalLength 1 x y ≤ angularLength K 1 :=
    TwoCircle.intervalLength_le_angularLength C (by norm_num) ⟨hx, by linarith only [hxmax]⟩
      ⟨by linarith only [hy], by linarith only [hsort, hxmax]⟩ (by linarith only [hx])
      (by dsimp [x]; ring) (by dsimp [y]; ring)
  by_cases hsmall : x < 1 / 4
  · have hlower : Real.pi / 3 ≤ angularLength K 1 := by
      by_cases hy₀ : 0 ≤ y
      · exact (TwoCircle.small_corner_length ⟨hx, hsmall⟩ ⟨hy₀, hyx⟩).le.trans hL₁
      · have hh := TwoCircle.small_straddling_length ⟨hx, hsmall⟩
          (t := -y) ⟨by linarith only [hy₀], by linarith only [hy]⟩
        simp only [neg_neg] at hh
        exact hh.trans hL₁
    have hn := angularLength_nonneg K (5 / 4)
    exact ⟨by linarith only [hlower, hn], fun he => by linarith only [hlower, hn, he]⟩
  · have hL₂ : TwoCircle.intervalLength (5 / 4) x y ≤ angularLength K (5 / 4) :=
      TwoCircle.intervalLength_le_angularLength C (by norm_num) ⟨hx, by linarith only [hxmax]⟩
        ⟨by linarith only [hy], by linarith only [hsort, hxmax]⟩ (by linarith only [hsmall])
        (by dsimp [x]; ring) (by dsimp [y]; ring)
    have hstrict : Real.pi < 3 * angularLength K 1 + angularLength K (5 / 4) := by
      by_cases hy₀ : 0 ≤ y
      · have hh₁ := (TwoCircle.corner_unit_length hx hy₀ hfar).trans hL₁
        have hh₂ := (TwoCircle.corner_larger_length hx hy₀ hfar).trans hL₂
        linarith only [TwoCircle.weighted_corner_constant, hh₁, hh₂]
      · have hfar' : (x + 1) ^ 2 + (1 - (-y)) ^ 2 ≤ 98 / 25 := by linarith only [hfar]
        have hh₁ := TwoCircle.general_straddling_unit_length hx
          (t := -y) ⟨by linarith only [hy₀], by linarith only [hy]⟩ hfar'
        have hh₂ := TwoCircle.general_straddling_larger_length hx
          (t := -y) ⟨by linarith only [hy₀], by linarith only [hy]⟩ hfar'
        simp only [neg_neg] at hh₁ hh₂
        linarith only [TwoCircle.weighted_straddling_constant, hL₁, hL₂, hh₁, hh₂]
    exact ⟨hstrict.le, fun he => (hstrict.ne he.symm).elim⟩

end SquaresInCircles.Eight
