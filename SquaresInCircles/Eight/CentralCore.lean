module

public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Eight.BoundaryReduction
public import SquaresInCircles.Eight.Arithmetic.CentralBandPolynomials
public import SquaresInCircles.Eight.CentralForbidden
public import SquaresInCircles.Common.Charts
public import SquaresInCircles.Common.Arcs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Eight squares: the central square and the one-twelfth core

In a packing of eight unit squares in a closed disk of squared radius at most `98/25` about the
origin, exactly one square contains the origin in its interior (`central_square_exists`). The
angular length `angularLength K r` of a square on the circle of radius `r` about the origin is
the measure of the whole set of directions in which the circle meets the closed square, not the
span of its endpoints: the set may have several components and isolated points of tangency with
a side. Two interior-disjoint squares share only boundary points, finitely many on each circle,
so the angular lengths of the squares add up to at most `2π` on every circle
(`angularLength_budget`). A square in the disk whose interior misses the origin has
`3 L₁ + L_{5/4} ≥ π`, with equality only if `L₁ = π/3` (`one_square_two_circle_inequality`), and
if no square contained the origin, the sum over the eight squares would force `8π/3 ≤ 2π`.

At squared radius at most `Q0` the central square contains the closed disk of radius `1/12`
about the origin in its interior, and every other closed square lies at distance more than
`1/12` from the origin (`central_core_and_exteriors`). Moving the disk centre to a nearest
boundary point of the central square would give a packing in a disk of squared radius below
`98/25` with no central square, so that boundary is more than `1/1000` from the origin
(`centralDepth_gt_milli`). Every exterior square then contains the segment
`{(11/12, y) : |y| ≤ 7/20}` of its centre direction, turned to the horizontal
(`CentralBand.RayData.segment`), and a common point at a fixed distance in every direction near
its centre direction (`CentralBand.RayData.common_point_A`, `common_point_B`), so the seven centre
directions are pairwise far apart. If a side of the central square came within `1/12` of the
origin, the rectangle witnesses of `CentralForbidden.lean` would forbid these segments an interval
of directions too long to leave room for the seven directions
(`seven_rays_avoid_interval_budget`).
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

/-- Closed interval extraction. The interval is allowed to cross the centre
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

/-- The one-square two-circle inequality, including the only equality fact
needed by the eight-square summation. The proof treats complete measured
intersections and extracts lower intervals only where those are sufficient. -/
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

/-- In a packing of eight squares in the disk of squared radius at most `98/25` about the
origin, exactly one square contains the origin in its interior. -/
theorem central_square_exists {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0, 0) q) (hq : q ≤ 98 / 25) :
    ∃! i, openSquare (S i) (0, 0) := by
  have hc (i : Fin 8) : SqContained (98 / 25) (S i) := by
    apply (SqContained.iff_points (by norm_num) (S i)).2
    intro p hp'
    have h := hp.2.1 i p hp'
    simpa only [sub, sub_zero] using h.trans hq
  obtain ⟨i, hi⟩ := central_exists_from_one_square_inequality hp.2.2
    (fun i hi => (one_square_two_circle_inequality (S i) (hc i) hi).1)
    (fun i hi => (one_square_two_circle_inequality (S i) (hc i) hi).2)
  exact ⟨i, hi, fun j hj => central_square_unique hp.2.2 hj hi⟩

namespace CentralBand

/-- A quadrant is parametrized algebraically before the rational half-angle
substitution. Both endpoints, including the vertical endpoint, are retained. -/
structure Quadrant (c s : ℝ) : Prop where
  c_nonneg : 0 ≤ c
  s_nonneg : 0 ≤ s
  unit : c^2+s^2 = 1

def halfAngle (c s : ℝ) : ℝ := s/(1+c)

lemma Quadrant.swap {c s : ℝ} (h : Quadrant c s) : Quadrant s c :=
  ⟨h.s_nonneg,h.c_nonneg,by linarith [h.unit]⟩

lemma Quadrant.halfAngle_mem {c s : ℝ} (h : Quadrant c s) :
    0 ≤ halfAngle c s ∧ halfAngle c s ≤ 1 := by
  have hc : 0 < 1+c := by linarith [h.c_nonneg]
  have hs : s ≤ 1 := (abs_le_of_sq_le_sq' (by linarith [h.unit,sq_nonneg c]) zero_le_one).2
  exact ⟨div_nonneg h.s_nonneg hc.le,(div_le_iff₀ hc).2 (by linarith [h.c_nonneg])⟩

lemma Quadrant.halfAngle_identities {c s : ℝ} (h : Quadrant c s) :
    (1-(halfAngle c s)^2)/(1+(halfAngle c s)^2) = c ∧
    2*halfAngle c s/(1+(halfAngle c s)^2) = s := by
  have hc : (1+c : ℝ) ≠ 0 := ne_of_gt (by linarith [h.c_nonneg])
  have hz : (1+(halfAngle c s)^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  constructor
  · dsimp [halfAngle] at *
    field_simp [hc] at ⊢
    linarith [h.unit,congrArg (fun x : ℝ => c*x) h.unit]
  · dsimp [halfAngle] at *
    field_simp [hc] at ⊢
    linarith [h.unit,congrArg (fun x : ℝ => s*x) h.unit]

lemma Quadrant.near_halfAngle_mem {c s : ℝ} (h : Quadrant c s) (hne : s ≤ c) :
    0 ≤ halfAngle c s ∧ halfAngle c s ≤ 3/7 := by
  have hc : 2/3 ≤ c := by
    have hs₂ := mul_nonneg (sub_nonneg.mpr hne) (add_nonneg h.c_nonneg h.s_nonneg)
    nlinarith only [hs₂,h.unit,h.c_nonneg]
  have hs : s ≤ 5/7 := by
    have hs₂ := mul_nonneg (sub_nonneg.mpr hne) (add_nonneg h.c_nonneg h.s_nonneg)
    nlinarith only [hs₂,h.unit,h.s_nonneg]
  refine ⟨h.halfAngle_mem.1,?_⟩
  apply (div_le_iff₀ (by linarith : 0 < 1+c)).2
  linarith

/-- If the polynomial `Arithmetic.centralBandP C D` is positive on `[0, 1]`, a square in the disk
of squared radius `Q0` with state `(r c, r s)` has `r c < 1/2 + C c - D s`: containment puts
`r c` below the positive root of a quadratic, and the polynomial, in the half-angle variable of
`(c, s)`, puts `1/2 + C c - D s` above it. -/
lemma primary_upper {r c s C D : ℝ}
    (h : Quadrant c s) (hr : 0 ≤ r) (hC : 0 ≤ C) (hD : 0 ≤ D ∧ D < 1/2)
    (hcontained : phi (r*c) (r*s) ≤ Q0)
    (hP : ∀ u, 0 ≤ u ∧ u ≤ 1 → 0 < Arithmetic.centralBandP C D u) :
    r*c < 1/2+C*c-D*s := by
  let u := halfAngle c s
  obtain ⟨hc,hs⟩ := h.halfAngle_identities
  have hp := hP u h.halfAngle_mem
  have hz : 0 < (1+u^2)^3 := by positivity
  have hnormalized := Arithmetic.centralBandP_normalized C D u
  have hpoly := div_pos hp hz
  rw [hnormalized,hc,hs] at hpoly
  have hs₁ : s ≤ 1 := (abs_le_of_sq_le_sq' (by linarith only [h.unit, sq_nonneg c]) zero_le_one).2
  have hY : 0 < 1/2+C*c-D*s := by
    have hp := mul_nonneg hC h.c_nonneg
    have hd := mul_le_mul_of_nonneg_left hs₁ hD.1
    linarith only [hD.2, hp, hd]
  have hX : 0 ≤ r*c := mul_nonneg hr h.c_nonneg
  have hB : 0 ≤ c*(c+s) := mul_nonneg h.c_nonneg (add_nonneg h.c_nonneg h.s_nonneg)
  have hquadratic : (r*c)^2+(r*c)*c*(c+s)+(1/2-Q0)*c^2 ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_right hcontained (sq_nonneg c)
    have hu := congrArg (fun x : ℝ => r^2*c^2*x) h.unit
    dsimp [phi] at hm
    linarith only [hm, hu]
  by_contra! hn
  have hprod := mul_nonneg (sub_nonneg.mpr hn)
    (show 0 ≤ r*c+(1/2+C*c-D*s)+c*(c+s) by linarith only [hY, hB, hn])
  dsimp [Q0] at hquadratic
  linarith only [hpoly, hquadratic, hprod]

lemma secondary_upper {c s A C D : ℝ} (h : Quadrant c s) (hne : s ≤ c)
    (hV : ∀ u, 0 ≤ u ∧ u ≤ 3/7 → 0 < Arithmetic.centralBandV A C D u) :
    C*s+D*c-A*(s/c) < 1/2 := by
  have hc : 0 < c := by nlinarith only [h.unit,h.c_nonneg,h.s_nonneg,hne]
  obtain ⟨hcos,hsin⟩ := h.halfAngle_identities
  have hu := h.near_halfAngle_mem hne
  set u := halfAngle c s with hu_def
  have hp := Arithmetic.centralBandV_normalized hu (hV u hu)
  have hratio : 2*u/(1-u^2) = s/c := by
    have hz : (1+u^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hu₂ : u^2 ≤ 9/49 := by linarith [mul_nonneg (show 0 ≤ 3/7-u by linarith [hu.2]) (show 0 ≤ 3/7+u by linarith [hu.1])]
    have hu₀ : (1-u^2 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    rw [← hsin,← hcos]
    field_simp
  rw [hcos,hsin,hratio] at hp
  exact hp

/-- The four side inequalities of the square hold strictly at every point of the transverse
segment, its two endpoints included. They follow from the five Bernstein rows of the segment
for the whole segment at once. -/
theorem transverse_segment_sides {r c s y : ℝ} (h : Quadrant c s) (hne : s ≤ c)
    (hr : 0 ≤ r) (ha : 1/2 < r*c)
    (hcontained : phi (r*c) (r*s) ≤ Q0) (hy : |y| ≤ 7/20) :
    |(11/12)*c+y*s-r*c| < 1/2 ∧
      |-(11/12)*s+y*c+r*s| < 1/2 := by
  have hp := primary_upper h hr (by norm_num : (0 : ℝ) ≤ 11/12)
    (by norm_num : (0 : ℝ) ≤ 7/20 ∧ (7/20 : ℝ) < 1/2)
    hcontained (fun _ hu => Arithmetic.segment_P_positive hu)
  have hp' := primary_upper h.swap hr (by norm_num : (0 : ℝ) ≤ 11/12)
    (by norm_num : (0 : ℝ) ≤ 7/20 ∧ (7/20 : ℝ) < 1/2)
    (by simpa [phi,add_comm] using hcontained)
    (fun _ hu => Arithmetic.segment_P_positive hu)
  have hv := secondary_upper h hne (fun _ hu => Arithmetic.segment_V_positive hu)
  have hc : 0 < c := by linarith only [h.unit, h.c_nonneg, h.s_nonneg, ha, hp]
  have hratio : (1/2)*(s/c) ≤ r*s := by
    have hh := mul_le_mul_of_nonneg_right ha.le h.s_nonneg
    rw [← mul_div_assoc, div_le_iff₀ hc]
    linarith only [hh]
  have hupper : (11/12)*c+y*s < 1 := by
    have hcauchy := cauchy_sq ((11/12 : ℝ),y) (c,s)
    have hy₂ : y^2 ≤ (7/20 : ℝ)^2 := by
      linarith only [sq_abs y,
        mul_nonneg (show 0 ≤ 7/20-|y| by linarith) (show 0 ≤ 7/20+|y| by positivity), hy]
    dsimp [dot,normSq] at hcauchy
    rw [h.unit] at hcauchy
    have hsq : ((11/12)*c+y*s)^2 < 1^2 := by linarith only [hcauchy, hy₂]
    exact (abs_lt.mp (abs_lt_of_sq_lt_sq hsq zero_le_one)).2
  obtain ⟨hylo,hyhi⟩ := abs_le.mp hy
  have hyslo := mul_le_mul_of_nonneg_right hylo h.s_nonneg
  have hyshi := mul_le_mul_of_nonneg_right hyhi h.s_nonneg
  have hyclo := mul_le_mul_of_nonneg_right hylo h.c_nonneg
  have hychi := mul_le_mul_of_nonneg_right hyhi h.c_nonneg
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith only [hp, hyslo, ha, hupper, hv,
    hratio, hyclo, hp', hychi]

lemma cos_upper_eight {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24-x^6/720+x^8/40320 := by
  have h := nonneg_of_deriv_nonneg
    (fun t => 1-t^2/2+t^4/24-t^6/720+t^8/40320-Real.cos t)
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [sin_lower_seven ht]) hx
  linarith

lemma sin_upper_nine {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120-x^7/5040+x^9/362880 := by
  have h := nonneg_of_deriv_nonneg
    (fun t => t-t^3/6+t^5/120-t^7/5040+t^9/362880-Real.sin t)
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [cos_upper_eight ht]) hx
  linarith

lemma bandA_trig :
    Arithmetic.bandA_Cminus < (10007/10000)*Real.cos (3741/10000 : ℝ) ∧
    (10007/10000)*Real.cos (3741/10000 : ℝ) < Arithmetic.bandA_Cplus ∧
    (10007/10000)*Real.sin (3741/10000 : ℝ) < Arithmetic.bandA_D := by
  have hc₁ := cos_lower_six (x := (3741/10000 : ℝ)) (by norm_num)
  have hc₂ := cos_upper_eight (x := (3741/10000 : ℝ)) (by norm_num)
  have hs := sin_upper_nine (x := (3741/10000 : ℝ)) (by norm_num)
  norm_num [Arithmetic.bandA_Cminus,Arithmetic.bandA_Cplus,Arithmetic.bandA_D] at *
  exact ⟨by linarith,by linarith,by linarith⟩

lemma bandB_trig :
    Arithmetic.bandB_Cminus < (41/40)*Real.cos (19/50 : ℝ) ∧
    (41/40)*Real.cos (19/50 : ℝ) < Arithmetic.bandB_Cplus ∧
    (41/40)*Real.sin (19/50 : ℝ) < Arithmetic.bandB_D := by
  have hc₁ := cos_lower_six (x := (19/50 : ℝ)) (by norm_num)
  have hc₂ := cos_upper_eight (x := (19/50 : ℝ)) (by norm_num)
  have hs := sin_upper_nine (x := (19/50 : ℝ)) (by norm_num)
  norm_num [Arithmetic.bandB_Cminus,Arithmetic.bandB_Cplus,Arithmetic.bandB_D] at *
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The common-point calculation: from the containment inequality and a lower bound `A` on the
primary coordinate, the point at distance `lam` in a direction within `h` of the centre direction
satisfies the four side inequalities of the square strictly. They are read as membership in the
open square in `RayData.common_point_A` and `RayData.common_point_B`. -/
theorem angular_band_sides {r α β h lam A Cminus Cplus D : ℝ}
    (hα : 0 ≤ α ∧ α ≤ Real.pi/4) (hβ : |β| ≤ h) (hh : 0 ≤ h ∧ h ≤ 2/5)
    (hr : 0 ≤ r) (hlam : 0 < lam) (hA : A ≤ r*Real.cos α)
    (hupper : lam-r*Real.cos α < 1/2)
    (hcontained : phi (r*Real.cos α) (r*Real.sin α) ≤ Q0)
    (hC : 0 ≤ Cminus) (hD : 0 ≤ D ∧ D < 1/2)
    (htrig : Cminus ≤ lam*Real.cos h ∧ lam*Real.cos h ≤ Cplus ∧ lam*Real.sin h ≤ D)
    (hP : ∀ u, 0 ≤ u ∧ u ≤ 1 → 0 < Arithmetic.centralBandP Cminus D u)
    (hV : ∀ u, 0 ≤ u ∧ u ≤ 3/7 → 0 < Arithmetic.centralBandV A Cplus D u) :
    |lam*Real.cos (α+β)-r*Real.cos α| < 1/2 ∧
    |-lam*Real.sin (α+β)+r*Real.sin α| < 1/2 := by
  have hc := cos_sin_nonneg (x := α) ⟨hα.1,by linarith only [hα.2, Real.pi_pos]⟩
  have hquad : Quadrant (Real.cos α) (Real.sin α) :=
    ⟨hc.1,hc.2,by linarith only [Real.sin_sq_add_cos_sq α]⟩
  have hnear := sin_le_cos_of_small hα
  have hprimary := primary_upper hquad hr hC hD hcontained hP
  have hother := primary_upper hquad.swap hr hC hD
    (by simpa [phi,add_comm] using hcontained) hP
  have hsecondary := secondary_upper hquad hnear hV
  have hcospos : 0 < Real.cos α := by
    have hh := east_quadrant_trig hα.1 hα.2
    linarith only [hh]
  have hratio : A*(Real.sin α/Real.cos α) ≤ r*Real.sin α := by
    have hm := mul_le_mul_of_nonneg_right hA hc.2
    rw [← mul_div_assoc, div_le_iff₀ hcospos]
    linarith only [hm]
  have hb := abs_le.mp hβ
  have hcosβ : Real.cos h ≤ Real.cos β := by
    rw [← Real.cos_abs β]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg β)
      (by linarith only [hh.2, Real.pi_gt_three, hα]) hβ
  have hsinβ : -Real.sin h ≤ Real.sin β ∧ Real.sin β ≤ Real.sin h := by
    constructor
    · have he := Real.sin_le_sin_of_le_of_le_pi_div_two
        (show -(Real.pi/2) ≤ -h by linarith only [hh.2, Real.pi_gt_three, hα])
        (show β ≤ Real.pi/2 by linarith only [hb.2, hh.2, Real.pi_gt_three, hα]) hb.1
      simpa using he
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith only [hb.1, hh.2, Real.pi_gt_three, hα])
        (by linarith only [hh.2, Real.pi_gt_three, hα]) hb.2
  have hcoslow : Cminus ≤ lam*Real.cos β := htrig.1.trans (mul_le_mul_of_nonneg_left hcosβ hlam.le)
  have hsinlo : -D ≤ lam*Real.sin β := by
    have hm := mul_le_mul_of_nonneg_left hsinβ.1 hlam.le
    linarith only [htrig.2.2, hm]
  have hsinhi : lam*Real.sin β ≤ D :=
    (mul_le_mul_of_nonneg_left hsinβ.2 hlam.le).trans htrig.2.2
  have hde : Cminus*Real.cos α-D*Real.sin α ≤ lam*Real.cos (α+β) := by
    have h₁ := mul_le_mul_of_nonneg_right hcoslow hc.1
    have h₂ := mul_le_mul_of_nonneg_right hsinhi hc.2
    rw [Real.cos_add]
    linarith only [h₁, h₂]
  have hdf : Cminus*Real.sin α-D*Real.cos α ≤ lam*Real.sin (α+β) := by
    have h₁ := mul_le_mul_of_nonneg_right hcoslow hc.2
    have h₂ := mul_le_mul_of_nonneg_right hsinlo hc.1
    rw [Real.sin_add]
    linarith only [h₁, h₂]
  have hdfupper : lam*Real.sin (α+β) ≤ Cplus*Real.sin α+D*Real.cos α := by
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ α+β by linarith only [hb.1, hh.2, hα.1, Real.pi_gt_three])
      (show α+h ≤ Real.pi/2 by linarith only [hα.2, hh.2, Real.pi_gt_three])
      (show α+β ≤ α+h by linarith only [hb.2])
    have hmlam := mul_le_mul_of_nonneg_left hm hlam.le
    have h₁ := mul_le_mul_of_nonneg_right htrig.2.1 hc.2
    have h₂ := mul_le_mul_of_nonneg_right htrig.2.2 hc.1
    rw [Real.sin_add α h] at hmlam
    linarith only [hmlam, h₁, h₂]
  have hdeupper := mul_le_mul_of_nonneg_left (Real.cos_le_one (α+β)) hlam.le
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith only [hprimary, hde, hupper,
    hdeupper, hsecondary, hratio, hdfupper, hother, hdf]

theorem bandA_sides {r α β : ℝ}
    (hα : 0 ≤ α ∧ α ≤ Real.pi/4) (hβ : |β| ≤ 3741/10000)
    (hr : 0 ≤ r) (ha : 5007/10000 < r*Real.cos α)
    (hcontained : phi (r*Real.cos α) (r*Real.sin α) ≤ Q0) :
    |(10007/10000)*Real.cos (α+β)-r*Real.cos α| < 1/2 ∧
    |-(10007/10000)*Real.sin (α+β)+r*Real.sin α| < 1/2 := by
  exact angular_band_sides hα hβ (by norm_num) hr (by norm_num) ha.le
    (by linarith) hcontained
    (by norm_num [Arithmetic.bandA_Cminus]) (by norm_num [Arithmetic.bandA_D])
    ⟨bandA_trig.1.le,bandA_trig.2.1.le,bandA_trig.2.2.le⟩
    (fun _ hu => Arithmetic.bandA_P_positive hu) (fun _ hu => Arithmetic.bandA_V_positive hu)

theorem bandB_sides {r α β : ℝ}
    (hα : 0 ≤ α ∧ α ≤ Real.pi/4) (hβ : |β| ≤ 19/50)
    (hr : 0 ≤ r) (ha : 107/200 ≤ r*Real.cos α)
    (hcontained : phi (r*Real.cos α) (r*Real.sin α) ≤ Q0) :
    |(41/40)*Real.cos (α+β)-r*Real.cos α| < 1/2 ∧
    |-(41/40)*Real.sin (α+β)+r*Real.sin α| < 1/2 := by
  exact angular_band_sides hα hβ (by norm_num) hr (by norm_num) ha
    (by linarith) hcontained
    (by norm_num [Arithmetic.bandB_Cminus]) (by norm_num [Arithmetic.bandB_D])
    ⟨bandB_trig.1.le,bandB_trig.2.1.le,bandB_trig.2.2.le⟩
    (fun _ hu => Arithmetic.bandB_P_positive hu) (fun _ hu => Arithmetic.bandB_V_positive hu)

end CentralBand

theorem central_square_exists_at {S : Fin 8 → UnitSquare} {o : Point} {q : ℝ}
    (hp : SqPacking S o q) (hq : q ≤ 98/25) : ∃! i, openSquare (S i) o := by
  have hpack := (sqPacking_iff_packing S o hp.1).mp hp
  have hrot := packing_pull hpack (0 : Direction)
  have hsquare : SqPacking (fun i => pullSquare o 0 (S i)) (0,0) q :=
    (sqPacking_iff_packing _ _ hp.1).mpr hrot
  obtain ⟨i,hi,hunique⟩ := central_square_exists hsquare hq
  have hmem (j : Fin 8) : openSquare (pullSquare o 0 (S j)) (0,0) ↔ openSquare (S j) o := by
    rw [pullSquare_open,frameEquiv_zero]
  exact ⟨i,(hmem i).mp hi,fun j hj => hunique j ((hmem j).mpr hj)⟩

def centralDepth (K : UnitSquare) : ℝ :=
  1/2-max (alpha K (0,0)) (beta K (0,0))

lemma centralDepth_pos {K : UnitSquare} (h : openSquare K (0,0)) : 0 < centralDepth K := by
  dsimp [centralDepth]
  exact sub_pos.mpr (max_lt h.1 h.2)

lemma centralDepth_disk {K : UnitSquare} (h : openSquare K (0,0)) {p : Point}
    (hp : normSq p < centralDepth K^2) : openSquare K p := by
  apply inscribed_disk_mem K (0,0) (centralDepth_pos h)
    (show max (alpha K (0,0)) (beta K (0,0))+centralDepth K=1/2 by dsimp [centralDepth]; ring)
    (le_max_left _ _) (le_max_right _ _)
  simpa [sub] using hp

/-- A boundary point of the square at distance `centralDepth K` from the origin, constructed in
the frame of the square. The second coordinate is held fixed, so the construction also covers a
tie between the two nearest sides. -/
lemma centralDepth_boundary_point {K : UnitSquare} (h : openSquare K (0,0)) :
    ∃ p, closedSquare K p ∧ ¬ openSquare K p ∧ normSq p = centralDepth K^2 := by
  have hd := centralDepth_pos h
  by_cases hxy : alpha K (0,0) ≤ beta K (0,0)
  · obtain ⟨u,hu,hprod⟩ := exists_signed (localY K (0,0)) (c := 1) (by norm_num)
    let p := scale (centralDepth K) (rotate K (0,u))
    have hu₂ : u^2=1 := by rw [← sq_abs,hu]; norm_num
    have hx : localX K p = localX K (0,0) := by
      dsimp [p,scale,rotate,localX]
      ring
    have hy : localY K p = localY K (0,0)+centralDepth K*u := by
      dsimp [p,scale,rotate,localY]
      linear_combination centralDepth K*u*K.unit
    have hy₂ : (localY K p)^2=1/4 := by
      rw [hy]
      dsimp [centralDepth]
      rw [max_eq_right hxy]
      dsimp [beta]
      linear_combination (2*(1/2-|localY K (0,0)|))*hprod+(1/2-|localY K (0,0)|)^2*hu₂-
        sq_abs (localY K (0,0))
    have hyabs : |localY K p|=1/2 := by
      rw [(sq_eq_sq_iff_abs_eq_abs (localY K p) (1/2)).1 (by rw [hy₂]; norm_num)]; norm_num
    refine ⟨p,⟨by simpa [hx] using h.1.le,by rw [hyabs]⟩,?_,?_⟩
    · intro hp
      linarith only [hp.2, hyabs]
    · dsimp [p,scale,rotate,normSq]
      linear_combination (centralDepth K)^2*u^2*K.unit+(centralDepth K)^2*hu₂
  · have hyx : beta K (0,0) ≤ alpha K (0,0) := le_of_lt (lt_of_not_ge hxy)
    obtain ⟨u,hu,hprod⟩ := exists_signed (localX K (0,0)) (c := 1) (by norm_num)
    let p := scale (centralDepth K) (rotate K (u,0))
    have hu₂ : u^2=1 := by rw [← sq_abs,hu]; norm_num
    have hx : localX K p = localX K (0,0)+centralDepth K*u := by
      dsimp [p,scale,rotate,localX]
      linear_combination centralDepth K*u*K.unit
    have hy : localY K p = localY K (0,0) := by
      dsimp [p,scale,rotate,localY]
      ring
    have hx₂ : (localX K p)^2=1/4 := by
      rw [hx]
      dsimp [centralDepth]
      rw [max_eq_left hyx]
      dsimp [alpha]
      linear_combination (2*(1/2-|localX K (0,0)|))*hprod+(1/2-|localX K (0,0)|)^2*hu₂-
        sq_abs (localX K (0,0))
    have hxabs : |localX K p|=1/2 := by
      rw [(sq_eq_sq_iff_abs_eq_abs (localX K p) (1/2)).1 (by rw [hx₂]; norm_num)]; norm_num
    refine ⟨p,⟨by rw [hxabs],by simpa [hy] using h.2.le⟩,?_,?_⟩
    · intro hp
      linarith only [hp.1, hxabs]
    · dsimp [p,scale,rotate,normSq]
      linear_combination (centralDepth K)^2*u^2*K.unit+(centralDepth K)^2*hu₂

lemma translated_containment_reserve {S : Fin 8 → UnitSquare} {q δ : ℝ} {p : Point}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0)
    (hδ : 0 ≤ δ ∧ δ ≤ 1/1000) (hpδ : normSq p = δ^2) :
    SqPacking S p (Q0+4/1000+(1/1000 : ℝ)^2) := by
  refine ⟨by norm_num [Q0],?_,hp.2.2⟩
  intro i z hz
  have hnorm : normSq z ≤ Q0 := by
    simpa [sub] using (hp.2.1 i z hz).trans hq
  have hc := cauchy_sq z p
  rw [hpδ] at hc
  have hm := mul_le_mul_of_nonneg_right hnorm (sq_nonneg δ)
  have hd : -2*δ ≤ dot z p := by
    have hQ : Q0 < 4 := radius_levels.2.2.2
    have hm' := mul_le_mul_of_nonneg_right hQ.le (sq_nonneg δ)
    by_contra! hh
    have hs := mul_pos (show 0 < -dot z p-2*δ by linarith)
      (show 0 < -dot z p+2*δ by linarith [hδ.1])
    linarith
  have he : normSq (sub z p) = normSq z-2*dot z p+normSq p := by
    dsimp [normSq,dot,sub]
    ring
  rw [he,hpδ]
  have hs := mul_nonneg (show 0 ≤ 1/1000-δ by linarith [hδ.2])
    (show 0 ≤ 1/1000+δ by linarith [hδ.1])
  linarith

/-- In a packing at squared radius at most `Q0`, the boundary of the square that contains the
origin is more than `1/1000` from the origin. Otherwise the disk of squared radius
`Q0 + 4/1000 + (1/1000)² < 98/25` about a nearest boundary point would hold the packing, and no
square would contain its centre in its interior. -/
theorem centralDepth_gt_milli {S : Fin 8 → UnitSquare} {q : ℝ} {i : Fin 8}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0) (hi : openSquare (S i) (0,0)) :
    1/1000 < centralDepth (S i) := by
  by_contra! hδ
  obtain ⟨p,hclosed,hnot,hdist⟩ := centralDepth_boundary_point hi
  have htranslated := translated_containment_reserve hp hq
    ⟨(centralDepth_pos hi).le,hδ⟩ hdist
  obtain ⟨j,hj,_⟩ := central_square_exists_at htranslated translated_ceiling_reserve.le
  by_cases hij : i=j
  · subst j
    exact hnot hj
  · exact open_closed_disjoint (hp.2.2 j i (Ne.symm hij)) p ⟨hj,hclosed⟩

lemma exterior_distance_from_centralDepth {S : Fin 8 → UnitSquare} {i j : Fin 8}
    (hd : InteriorDisjoint S) (hi : openSquare (S i) (0,0)) (hij : i ≠ j) :
    centralDepth (S i)^2 ≤ coreDistanceSq (S j) := by
  obtain ⟨p,hp,he⟩ := coreDistanceSq_attained (S j)
  by_contra! hh
  have hin : openSquare (S i) p := centralDepth_disk hi (by simpa [he] using hh)
  exact open_closed_disjoint (hd i j hij) p ⟨hin,hp⟩

lemma primary_distance_lower {K : UnitSquare} {δ : ℝ}
    (hδ : 0 < δ) (hd : δ^2 ≤ coreDistanceSq K) :
    1/2 < max (alpha K (0,0)) (beta K (0,0)) ∧
    δ^2 ≤ 2*(max (alpha K (0,0)) (beta K (0,0))-1/2)^2 := by
  let A := max (alpha K (0,0)) (beta K (0,0))
  have hx : alpha K (0,0) ≤ A := le_max_left _ _
  have hy : beta K (0,0) ≤ A := le_max_right _ _
  have hA : 1/2 < A := by
    by_contra! h
    have hα : max (alpha K (0,0)-1/2) 0=0 := max_eq_right (by linarith)
    have hβ : max (beta K (0,0)-1/2) 0=0 := max_eq_right (by linarith)
    dsimp [coreDistanceSq] at hd
    rw [hα,hβ] at hd
    nlinarith only [hd, hδ]
  have hα : max (alpha K (0,0)-1/2) 0 ≤ A-1/2 := max_le (by linarith) (by linarith)
  have hβ : max (beta K (0,0)-1/2) 0 ≤ A-1/2 := max_le (by linarith) (by linarith)
  have hx₂ := pow_le_pow_left₀ (le_max_right _ _) hα 2
  have hy₂ := pow_le_pow_left₀ (le_max_right _ _) hβ 2
  exact ⟨hA,by dsimp [coreDistanceSq] at hd; linarith⟩

theorem exterior_primary_bandA {S : Fin 8 → UnitSquare} {q : ℝ} {i j : Fin 8}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0) (hi : openSquare (S i) (0,0))
    (hij : i ≠ j) : 5007/10000 < max (alpha (S j) (0,0)) (beta (S j) (0,0)) := by
  have hδ := centralDepth_gt_milli hp hq hi
  have hd := exterior_distance_from_centralDepth hp.2.2 hi hij
  obtain ⟨hA,hA₂⟩ := primary_distance_lower (centralDepth_pos hi) hd
  by_contra! hn
  nlinarith only [hA₂, hn, hδ, hA]

theorem exterior_primary_bandB {S : Fin 8 → UnitSquare} {i j : Fin 8}
    (hd : InteriorDisjoint S) (hi : openSquare (S i) (0,0)) (hij : i ≠ j)
    (hshallow : max (alpha (S i) (0,0)) (beta (S i) (0,0)) ≤ 9/20) :
    107/200 < max (alpha (S j) (0,0)) (beta (S j) (0,0)) := by
  have hδ : 1/20 ≤ centralDepth (S i) := by dsimp [centralDepth]; linarith
  have hd' := exterior_distance_from_centralDepth hd hi hij
  obtain ⟨hA,hA₂⟩ := primary_distance_lower (centralDepth_pos hi) hd'
  by_contra! hn
  nlinarith only [hδ, hA₂, hn, hA]

namespace CentralBand

structure RayData (K : UnitSquare) where
  chart : SquareChart K (0,0)
  sorted : chart.b ≤ chart.a
  radius : ℝ
  angle : ℝ
  radius_pos : 0 < radius
  angle_range : 0 ≤ angle ∧ angle ≤ Real.pi/4
  primary : radius*Real.cos angle = chart.a
  secondary : radius*Real.sin angle = chart.b

lemma RayData.primary_max {K : UnitSquare} (R : RayData K) :
    R.chart.a = max (alpha K (0,0)) (beta K (0,0)) := by
  rcases R.chart.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [← ha,← hb,max_eq_left R.sorted]
  · rw [← hb,← ha,max_eq_right R.sorted]

lemma ray_data_exists (K : UnitSquare)
    (h : 0 < max (alpha K (0,0)) (beta K (0,0))) : Nonempty (RayData K) := by
  obtain ⟨C,hsort⟩ := sorted_square_chart K (0,0)
  have hmax : C.a = max (alpha K (0,0)) (beta K (0,0)) := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [← ha,← hb,max_eq_left hsort]
    · rw [← hb,← ha,max_eq_right hsort]
  have ha : 0 < C.a := by simpa [hmax] using h
  by_cases hb : C.b=0
  · exact ⟨⟨C,hsort,C.a,0,ha,⟨by norm_num,by positivity⟩,
      by simp,by simp [hb]⟩⟩
  · have hb' : 0 < C.b := lt_of_le_of_ne C.nonneg.2 (Ne.symm hb)
    obtain ⟨r,θ,hr,hθ,hθq,_,hc,hs⟩ := first_octant_polar ha hb' hsort
    exact ⟨⟨C,hsort,r,θ,hr,⟨hθ.le,hθq⟩,hc,hs⟩⟩

def RayData.direction {K : UnitSquare} (R : RayData K) : Direction :=
  chartAngle R.chart.phase R.chart.reversed R.angle

lemma RayData.quadrant {K : UnitSquare} (R : RayData K) :
    Quadrant (Real.cos R.angle) (Real.sin R.angle) := by
  have hh := cos_sin_nonneg ⟨R.angle_range.1,by linarith [R.angle_range.2,Real.pi_pos]⟩
  exact ⟨hh.1,hh.2,by linarith [Real.sin_sq_add_cos_sq R.angle]⟩

lemma RayData.segment {K : UnitSquare} (R : RayData K)
    (ha : 1/2 < R.chart.a) (hc : SqContained Q0 K) :
    ∀ v, |v| ≤ 7/20 → openSquare K (pointInDirection (0,0) R.direction (11/12) v) := by
  have hφ : phi (R.radius*Real.cos R.angle) (R.radius*Real.sin R.angle) ≤ Q0 := by
    rw [R.primary,R.secondary]
    exact chart_phi R.chart hc
  have hsides (v : ℝ) (hv : |v| ≤ 7/20) := transverse_segment_sides R.quadrant
    (sin_le_cos_of_small R.angle_range) R.radius_pos.le (by simpa [R.primary] using ha) hφ hv
  intro v hv
  cases hrev : R.chart.reversed
  · have h := hsides (-v) (by simpa using hv)
    have he : pointInDirection (0,0) R.direction (11/12) v =
        pointInDirection (0,0) R.chart.phase
          ((11/12)*Real.cos R.angle-v*Real.sin R.angle)
          ((11/12)*Real.sin R.angle+v*Real.cos R.angle) := by
      apply Prod.ext <;>
        simp [RayData.direction,chartAngle,hrev,pointInDirection,Real.Angle.cos_add,Real.Angle.sin_add] <;> ring
    rw [he,R.chart.cartesian]
    simp only [SquareChart.signedB,hrev,Bool.false_eq_true,ite_false]
    rw [← R.primary,← R.secondary]
    constructor
    · convert h.1 using 2
      ring
    · convert h.2 using 1
      rw [← abs_neg]
      congr 1
      ring
  · have h := hsides v hv
    have he : pointInDirection (0,0) R.direction (11/12) v =
        pointInDirection (0,0) R.chart.phase
          ((11/12)*Real.cos R.angle+v*Real.sin R.angle)
          (-(11/12)*Real.sin R.angle+v*Real.cos R.angle) := by
      apply Prod.ext <;>
        simp [RayData.direction,chartAngle,hrev,pointInDirection,Real.Angle.cos_add,Real.Angle.sin_add] <;> ring
    rw [he,R.chart.cartesian]
    simp only [SquareChart.signedB,hrev,ite_true]
    rw [← R.primary,← R.secondary]
    simpa only [sub_neg_eq_add] using h

lemma RayData.direction_parameter {K : UnitSquare} (R : RayData K) (θ : Direction) :
    let t := (θ-R.direction).toReal
    chartAngle R.chart.phase R.chart.reversed
      (R.angle+(if R.chart.reversed then -t else t)) = θ := by
  intro t
  have ht : ((t : ℝ) : Direction) = θ-R.direction := Real.Angle.coe_toReal _
  have hdir : R.direction = chartAngle R.chart.phase R.chart.reversed R.angle := rfl
  cases hrev : R.chart.reversed
  · rw [hrev] at hdir
    simp only [chartAngle,Bool.false_eq_true,ite_false] at hdir ⊢
    rw [Real.Angle.coe_add,ht,hdir]
    abel
  · rw [hrev] at hdir
    simp only [chartAngle,ite_true] at hdir ⊢
    rw [show -(R.angle+-t) = -R.angle+t by ring,Real.Angle.coe_add,ht,hdir]
    abel

lemma RayData.common_point_A {K : UnitSquare} (R : RayData K)
    (ha : 5007/10000 < R.chart.a) (hc : SqContained Q0 K) :
    ∀ θ, dist θ R.direction ≤ 3741/10000 →
      openSquare K (circlePoint (0,0) (10007/10000) θ) := by
  intro θ hθ
  let t := (θ-R.direction).toReal
  let β := if R.chart.reversed then -t else t
  have hβ : |β| ≤ 3741/10000 := by
    have ht : |t| ≤ 3741/10000 := by
      rw [direction_dist] at hθ
      exact hθ
    show |if R.chart.reversed then -t else t| ≤ 3741/10000
    split_ifs
    · rw [abs_neg]
      exact ht
    · exact ht
  have hs := bandA_sides R.angle_range hβ R.radius_pos.le
    (by simpa [R.primary] using ha)
    (by rw [R.primary,R.secondary]; exact chart_phi R.chart hc)
  rw [← R.direction_parameter θ,R.chart.membership]
  rw [← R.primary,← R.secondary]
  refine ⟨hs.1,?_⟩
  rw [← abs_neg]
  convert hs.2 using 2
  ring

lemma RayData.common_point_B {K : UnitSquare} (R : RayData K)
    (ha : 107/200 ≤ R.chart.a) (hc : SqContained Q0 K) :
    ∀ θ, dist θ R.direction ≤ 19/50 →
      openSquare K (circlePoint (0,0) (41/40) θ) := by
  intro θ hθ
  let t := (θ-R.direction).toReal
  let β := if R.chart.reversed then -t else t
  have hβ : |β| ≤ 19/50 := by
    have ht : |t| ≤ 19/50 := by
      rw [direction_dist] at hθ
      exact hθ
    show |if R.chart.reversed then -t else t| ≤ 19/50
    split_ifs
    · rw [abs_neg]
      exact ht
    · exact ht
  have hs := bandB_sides R.angle_range hβ R.radius_pos.le
    (by simpa [R.primary] using ha)
    (by rw [R.primary,R.secondary]; exact chart_phi R.chart hc)
  rw [← R.direction_parameter θ,R.chart.membership]
  rw [← R.primary,← R.secondary]
  refine ⟨hs.1,?_⟩
  rw [← abs_neg]
  convert hs.2 using 2
  ring

lemma closed_caps_strictly_separated {K J : UnitSquare} {θ φ : Direction} {r h : ℝ}
    (hK : ∀ ψ, dist ψ θ ≤ h → openSquare K (circlePoint (0,0) r ψ))
    (hJ : ∀ ψ, dist ψ φ ≤ h → openSquare J (circlePoint (0,0) r ψ))
    (hd : ∀ p, ¬ (openSquare K p ∧ openSquare J p)) : 2*h < dist θ φ := by
  by_contra! hn
  let t := (φ-θ).toReal
  let ψ : Direction := θ+((t/2 : ℝ) : Direction)
  have ht : |t| ≤ 2*h := by
    rw [dist_comm,direction_dist] at hn
    exact hn
  have hψθ : dist ψ θ ≤ h := by
    have hb := direction_coe_norm_le (t/2)
    have he : ψ-θ=((t/2 : ℝ) : Direction) := by dsimp [ψ]; abel
    rw [dist_eq_norm,he]
    exact hb.trans (by rw [abs_div]; norm_num; linarith)
  have hψφ : dist ψ φ ≤ h := by
    have hb := direction_coe_norm_le (-t/2)
    have he : ψ-φ=((-t/2 : ℝ) : Direction) := by
      rw [direction_offset φ θ]
      dsimp [ψ,t]
      rw [show (-((φ-θ).toReal)/2 : ℝ)=((φ-θ).toReal)/2-((φ-θ).toReal) by ring,
        Real.Angle.coe_sub]
      abel
    rw [dist_eq_norm,he]
    exact hb.trans (by rw [abs_div,abs_neg]; norm_num; linarith)
  exact hd _ ⟨hK ψ hψθ,hJ ψ hψφ⟩

end CentralBand

def chartPoint {K : UnitSquare} (C : SquareChart K (0,0)) (x y : ℝ) : Point :=
  pointInDirection (0,0) C.phase x (if C.reversed then -y else y)

lemma chartPoint_closed {K : UnitSquare} (C : SquareChart K (0,0)) (x y : ℝ) :
    closedSquare K (chartPoint C x y) ↔ |x-C.a| ≤ 1/2 ∧ |y-C.b| ≤ 1/2 := by
  obtain ⟨r,t,hx,hy⟩ := plane_polar x y
  have he : chartPoint C x y=circlePoint (0,0) r (chartAngle C.phase C.reversed t) := by
    rw [← hx,← hy]
    cases hrev : C.reversed <;>
      apply Prod.ext <;> simp [chartPoint,chartAngle,hrev,pointInDirection,circlePoint,
        Real.Angle.cos_add,Real.Angle.sin_add] <;> ring
  rw [he,SquareChart.closed_membership C,hx,hy]

lemma chartPoint_segment {K : UnitSquare} (C : SquareChart K (0,0)) (β v : ℝ) :
    chartPoint C (pointInDirection (0,0) (β : Direction) (11/12) v).1
      (pointInDirection (0,0) (β : Direction) (11/12) v).2 =
    pointInDirection (0,0) (chartAngle C.phase C.reversed β) (11/12)
      (if C.reversed then -v else v) := by
  cases hrev : C.reversed <;>
    apply Prod.ext <;> simp [chartPoint,chartAngle,hrev,pointInDirection,
      Real.Angle.cos_add,Real.Angle.sin_add] <;> ring

/-- A forbidden closed interval leaves only one complementary arc for the
seven rays. Sorting their representatives in that arc produces six strict
gaps. -/
lemma seven_rays_avoid_interval_budget (rays : Vertex → Direction)
    {phase : Direction} {reversed : Bool} {l u g : ℝ}
    (hwidth : 0 < u-l ∧ u-l ≤ 4)
    (hsep : ∀ i j, i ≠ j → g < dist (rays i) (rays j))
    (havoid : ∀ i β, l ≤ β ∧ β ≤ u → rays i ≠ chartAngle phase reversed β) :
    (u-l)+6*g < 2*Real.pi := by
  let mid := (l+u)/2
  let center := chartAngle phase reversed mid
  have hfar (i : Vertex) : (u-l)/2 < dist (rays i) center := by
    by_contra! hn
    let t := (rays i-center).toReal
    let β := mid+(if reversed then -t else t)
    have ht : |t| ≤ (u-l)/2 := by simpa [direction_dist,t] using hn
    have hβ : l ≤ β ∧ β ≤ u := by
      rcases abs_le.mp ht with ⟨hl,hu⟩
      cases reversed <;> dsimp [β,mid] <;> constructor <;> linarith only [hl, hu]
    apply havoid i β hβ
    have he : ((t : ℝ) : Direction) = rays i-center := Real.Angle.coe_toReal _
    have hshift : chartAngle phase reversed β = center+((t : ℝ) : Direction) := by
      cases reversed
      · simp only [β,center,chartAngle,Bool.false_eq_true,ite_false,Real.Angle.coe_add]
        abel
      · simp only [β,center,chartAngle,ite_true,neg_add,neg_neg,Real.Angle.coe_add]
        abel
    rw [hshift,he]
    abel
  let t : Vertex → ℝ := fun i => (rays i-center).toReal
  let p : Vertex → ℝ := fun i => if t i < 0 then t i+2*Real.pi else t i
  have hp (i : Vertex) : (u-l)/2 < p i ∧ p i < 2*Real.pi-(u-l)/2 := by
    have ht : (u-l)/2 < |t i| := by simpa [direction_dist,t] using hfar i
    have hl := Real.Angle.neg_pi_lt_toReal (rays i-center)
    have hu := Real.Angle.toReal_le_pi (rays i-center)
    have hw : (u-l)/2 < Real.pi := by linarith only [hwidth.2, Real.pi_gt_three]
    by_cases h : t i < 0
    · simp only [p,ite_eq_left h,abs_of_neg h] at *
      dsimp [t] at *
      constructor <;> linarith only [hl, ht]
    · simp only [p,ite_eq_right h,abs_of_nonneg (le_of_not_gt h)] at *
      dsimp [t] at *
      constructor <;> linarith only [ht, hu, hw]
  have hrepr (i : Vertex) : rays i=center+(p i : Direction) := by
    rw [direction_offset (rays i) center]
    dsimp [p]
    split_ifs
    · simp [Real.Angle.coe_add,Real.Angle.coe_two_pi,t]
    · rfl
  let σ := Tuple.sort p
  let z : Vertex → ℝ := fun i => p (σ i)
  have hz : Monotone z := Tuple.monotone_sort p
  have hstep (i : Fin 6) : g < z i.succ-z i.castSucc := by
    have h := hsep (σ i.succ) (σ i.castSucc) (σ.injective.ne i.castSucc_lt_succ.ne')
    rw [hrepr,hrepr,dist_eq_norm] at h
    have he : center+(p (σ i.succ) : Direction)-(center+(p (σ i.castSucc) : Direction)) =
        ((z i.succ-z i.castSucc : ℝ) : Direction) := by
      dsimp only [z]
      rw [Real.Angle.coe_sub]
      abel
    rw [he] at h
    have hb := direction_coe_norm_le (z i.succ-z i.castSucc)
    rw [abs_of_nonneg (sub_nonneg.mpr (hz i.castSucc_lt_succ.le))] at hb
    exact h.trans_le hb
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => (hstep i).le) ⟨0,Finset.mem_univ _,hstep 0⟩
  have htel : (∑ i : Fin 6, (z i.succ-z i.castSucc))=z 6-z 0 := by
    norm_num [Fin.sum_univ_succ]
    ring
  rw [htel] at hsum
  norm_num at hsum
  have hlo := (hp (σ 0)).1
  have hhi := (hp (σ 6)).2
  dsimp [z] at hsum
  linarith only [hsum, hlo, hhi]

lemma central_rectangle_forbids {K : UnitSquare} (C : SquareChart K (0,0))
    {A l u : ℝ} (hinside : C.a < 1/2 ∧ C.b < 1/2) (hreach : A ≤ C.a+1/2)
    (hrectangle : ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ 7/20 ∧
      let p := pointInDirection (0,0) (β : Direction) (11/12) v
      0 ≤ p.1 ∧ p.1 ≤ A ∧ -(1/2-C.b) ≤ p.2 ∧ p.2 ≤ 1-(1/2-C.b))
    {J : UnitSquare} (ray : Direction)
    (hsegment : ∀ v, |v| ≤ 7/20 → openSquare J (pointInDirection (0,0) ray (11/12) v))
    (hd : ∀ p, ¬ (openSquare J p ∧ openSquare K p)) :
    ∀ β, l ≤ β ∧ β ≤ u → ray ≠ chartAngle C.phase C.reversed β := by
  intro β hβ he
  obtain ⟨v,hv,hx₀,hx₁,hy₀,hy₁⟩ := hrectangle β hβ
  let p := pointInDirection (0,0) (β : Direction) (11/12) v
  have hclosed : closedSquare K (chartPoint C p.1 p.2) := by
    rw [chartPoint_closed]
    constructor <;> apply abs_le.mpr <;> constructor <;>
      linarith [C.nonneg.1,C.nonneg.2]
  have hmem := hsegment (if C.reversed then -v else v)
    (by cases C.reversed <;> simpa using hv)
  rw [he,← chartPoint_segment C β v] at hmem
  exact open_closed_disjoint hd _ ⟨hmem,hclosed⟩

/-- The one-twelfth core: in a packing at squared radius at most `Q0`, one square contains the
closed disk of radius `1/12` about the origin in its interior, and every other closed square is at
distance more than `1/12` from the origin. The central square comes from the two-circle
inequality, the rays of the exterior squares from their charts, and the forbidden intervals from
the rectangle witnesses of `CentralForbidden.lean`. -/
theorem central_core_and_exteriors {S : Fin 8 → UnitSquare} {q : ℝ}
    (hp : SqPacking S (0,0) q) (hq : q ≤ Q0) :
    ∃ i : Fin 8, ContainsCore (S i) ∧
      ∀ j, i ≠ j → StrictCoreAvoiding (S j) := by
  obtain ⟨i,hi,_⟩ := central_square_exists hp
    (hq.trans (by norm_num [Q0] : Q0 ≤ 98/25))
  obtain ⟨C,hsort⟩ := sorted_square_chart (S i) (0,0)
  have hmax : C.a=max (alpha (S i) (0,0)) (beta (S i) (0,0)) := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [← ha,← hb,max_eq_left hsort]
    · rw [← hb,← ha,max_eq_right hsort]
  let E : Vertex → UnitSquare := fun j => S (i.succAbove j)
  have hne (j : Vertex) : i ≠ i.succAbove j := (Fin.succAbove_ne i j).symm
  have hEdisjoint : InteriorDisjoint E := by
    intro j k hjk p h
    exact hp.2.2 _ _ (Fin.succAbove_right_injective.ne hjk) p h
  have hEcontain (j : Vertex) : SqContained Q0 (E j) := by
    apply (SqContained.iff_points (by norm_num [Q0]) _).2
    intro p h
    simpa [sub] using (hp.2.1 (i.succAbove j) p h).trans hq
  have hprimary (j : Vertex) : 5007/10000 < max (alpha (E j) (0,0)) (beta (E j) (0,0)) :=
    exterior_primary_bandA hp hq hi (hne j)
  let R : (j : Vertex) → CentralBand.RayData (E j) := fun j =>
    Classical.choice (CentralBand.ray_data_exists (E j) (by linarith only [hprimary j, hprimary]))
  let rays : Vertex → Direction := fun j => (R j).direction
  have hsegments (j : Vertex) :
      ∀ v, |v| ≤ 7/20 → openSquare (E j) (pointInDirection (0,0) (rays j) (11/12) v) := by
    apply (R j).segment
    · rw [(R j).primary_max]
      linarith only [hprimary j, hprimary]
    · exact hEcontain j
  have hcore_a : C.a < 5/12 := by
    by_contra! ha
    let d := 1/2-C.b
    have hd : 0 ≤ d ∧ d ≤ 1/2 := by
      have hc := C.origin.mp hi
      dsimp [d]
      constructor <;> linarith only [C.nonneg.2, hsort, hc]
    by_cases hband : C.a ≤ 9/20
    · obtain ⟨l,u,hl,hu,hw,hw₄,hrect⟩ := CentralForbidden.bandA_forbidden hd
      have hsep (j k : Vertex) (hjk : j ≠ k) : 19/25 < dist (rays j) (rays k) := by
        have hj := exterior_primary_bandB hp.2.2 hi (hne j) (by simpa [← hmax] using hband)
        have hk := exterior_primary_bandB hp.2.2 hi (hne k) (by simpa [← hmax] using hband)
        have h := CentralBand.closed_caps_strictly_separated
          ((R j).common_point_B (by simpa [(R j).primary_max] using hj.le) (hEcontain j))
          ((R k).common_point_B (by simpa [(R k).primary_max] using hk.le) (hEcontain k))
          (hEdisjoint j k hjk)
        norm_num at h
        exact h
      have havoid (j : Vertex) := central_rectangle_forbids C (C.origin.mp hi)
        (show (11/12 : ℝ) ≤ C.a+1/2 by linarith only [ha])
        (by simpa [CentralForbidden.L,CentralForbidden.c,d] using hrect)
        (rays j) (hsegments j) (hp.2.2 (i.succAbove j) i (hne j).symm)
      have hb := seven_rays_avoid_interval_budget rays ⟨by linarith only [hw],hw₄⟩ hsep havoid
      linarith only [pi_lt_22_over_7, hw, hb]
    · obtain ⟨l,u,hl,hu,hw,hw₄,hrect⟩ := CentralForbidden.bandB_forbidden hd
      have hsep (j k : Vertex) (hjk : j ≠ k) : 3741/5000 < dist (rays j) (rays k) := by
        have h := CentralBand.closed_caps_strictly_separated
          ((R j).common_point_A (by simpa [(R j).primary_max] using hprimary j) (hEcontain j))
          ((R k).common_point_A (by simpa [(R k).primary_max] using hprimary k) (hEcontain k))
          (hEdisjoint j k hjk)
        norm_num at h
        exact h
      have havoid (j : Vertex) := central_rectangle_forbids C (C.origin.mp hi)
        (show (19/20 : ℝ) ≤ C.a+1/2 by linarith only [hband])
        (by simpa [CentralForbidden.L,CentralForbidden.c,d] using hrect)
        (rays j) (hsegments j) (hp.2.2 (i.succAbove j) i (hne j).symm)
      have hb := seven_rays_avoid_interval_budget rays ⟨by linarith only [hw],hw₄⟩ hsep havoid
      linarith only [pi_lt_22_over_7, hw, hb]
  have hmax' : max (alpha (S i) (0,0)) (beta (S i) (0,0)) < 5/12 := by
    rw [← hmax]
    exact hcore_a
  have hcore : ContainsCore (S i) := containsCore_of_center_bounds
    ((le_max_left _ _).trans_lt hmax') ((le_max_right _ _).trans_lt hmax')
  exact ⟨i,hcore,fun j hij => strictCoreAvoiding_of_containsCore hcore (hp.2.2 i j hij)⟩

end SquaresInCircles.Eight
