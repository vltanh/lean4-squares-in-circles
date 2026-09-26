import SquaresInCircles.One.Uniqueness
import SquaresInCircles.Two.Uniqueness
import SquaresInCircles.Three.Uniqueness
import SquaresInCircles.Four.Uniqueness
import SquaresInCircles.Five.Uniqueness
import SquaresInCircles.Seven.Uniqueness

/-!
# Packing one to five, and seven, unit squares in a disk

For `1 ≤ n ≤ 5` and `n = 7`, `optimalRadius n` is the least radius of a disk
that holds `n` non-overlapping unit squares, and the packings in a disk of that
radius are exactly the configurations congruent to a model in
`optimalPackings n`. For `n ≤ 5` there is one model, so the optimal packing is
unique up to a rotation about the disk centre and a relabelling of the squares.
For `n = 7` the three middle squares of the model move along the middle axis.

Every case proves the same statement, an `Optimum` (`Common/Optimum.lean`): its
models pack the disk and reach its circle, and every packing of that radius is
congruent to one of them. The rest follows once for all cases. Each case can
also be imported on its own, from its folder `SquaresInCircles/One/` to
`SquaresInCircles/Seven/`.
-/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for `n` unit squares, `1 ≤ n ≤ 5` or `n = 7`. -/
def optimalRadius : ℕ → ℝ
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 7 => Seven.radius
  | _ => 0

/-- The optimal packings of `n` unit squares, as models about the origin: one
packing for `n ≤ 5`, and for `n = 7` every position of the three middle
squares. -/
def optimalPackings : (n : ℕ) → Set (Fin n → UnitSquare)
  | 1 => {One.model}
  | 2 => {Two.model}
  | 3 => {Three.model}
  | 4 => {Four.model}
  | 5 => {Five.model}
  | 7 => Set.range Seven.columnModel
  | _ => ∅

/-- The optimum for each `n` with `1 ≤ n ≤ 5` or `n = 7`. -/
def optimum : (n : ℕ) → 1 ≤ n ∧ n ≤ 5 ∨ n = 7 → Optimum n
  | 1, _ => One.optimum
  | 2, _ => Two.optimum
  | 3, _ => Three.optimum
  | 4, _ => Four.optimum
  | 5, _ => Five.optimum
  | 7, _ => Seven.optimum
  | 0, h | 6, h | _+8, h => absurd h (by omega)

/-- `optimum n` has the radius and the models of the tables above. -/
lemma optimum_spec (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    (optimum n hn).radius = optimalRadius n ∧ (optimum n hn).models = optimalPackings n := by
  match n, hn with
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 7, _ => exact ⟨rfl,rfl⟩
  | 0, h | 6, h | _+8, h => exact absurd h (by omega)

/-- `optimalRadius n` is the least radius of a disk that holds `n` unit squares
with disjoint interiors. -/
theorem optimal_radius (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} (optimalRadius n) :=
  (optimum_spec n hn).1 ▸ (optimum n hn).isLeast

/-- The packings in a disk of radius `optimalRadius n` are exactly the
configurations congruent to an optimal model. -/
theorem optimal_packings (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ M ∈ optimalPackings n, Congruent S o M := by
  rw [← (optimum_spec n hn).1,← (optimum_spec n hn).2]
  exact (optimum n hn).packing_iff S o

/-- The forward direction of `optimal_packings`, with the frame replaced by an
explicit isometry of the plane that takes the origin to the disk centre. -/
theorem optimal_packings_rigid (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    ∃ M ∈ optimalPackings n, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) := by
  rw [← (optimum_spec n hn).1] at hp
  rw [← (optimum_spec n hn).2]
  exact (optimum n hn).rigid_uniqueness S o hp

end SquaresInCircles
