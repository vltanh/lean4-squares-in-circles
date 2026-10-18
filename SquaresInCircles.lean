module

public import SquaresInCircles.One.Uniqueness
public import SquaresInCircles.Two.Uniqueness
public import SquaresInCircles.Three.Uniqueness
public import SquaresInCircles.Four.Uniqueness
public import SquaresInCircles.Five.Uniqueness
public import SquaresInCircles.Six.Uniqueness
public import SquaresInCircles.Seven.Uniqueness
public import SquaresInCircles.Eight.Theorem
public import SquaresInCircles.Optimal

/-!
# Packing one to eight unit squares in a disk

For `1 ≤ n ≤ 8`, `optimalRadius n` is the least radius of a disk that holds `n`
non-overlapping unit squares, and the packings in a disk of that radius are
exactly the configurations congruent to a model in `optimalPackings n`. For
`n ≤ 6` there is one model, so the optimal packing is unique up to a rotation
about the disk centre and a relabelling of the squares. For `n = 7` the three
middle squares of the model move along the middle axis.
At `n = 8`, five outer anchors are fixed, two exterior squares slide, and
the central square translates and rotates in an explicit admissible domain.
Both orientations of this five-parameter family are included. The public
registries `optimalRadius` and `optimalPackings` are in `Optimal.lean`;
primitive square geometry remains in `Geometry.lean`. The eighth-case
statement data in `StatementEight.lean` use ordinary classical selection
from explicit stationary equations, with existence, uniqueness, and agreement
with the analytic root proved in `Eight/ExactFamily/StatementLink.lean`.
Thus the public definitions and their Mathlib-only Challenge mirror do not
depend on importing the case proofs.

The n=8 extension is delivered as uncompiled draft Lean source. Its proof
scripts and generated rational certificates have not been compiled or
audited in this source-writing pass.

Every case proves the same statement, an `Optimum` (`Common/Optimum.lean`): its
models pack the disk and reach its circle, and every packing of that radius is
congruent to one of them. The rest follows once for all cases. Each case can
also be imported on its own, from its folder `SquaresInCircles/One/` to
`SquaresInCircles/Eight/`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-- The optimum for each `n` with `1 ≤ n ≤ 8`. -/
def optimum : (n : ℕ) → 1 ≤ n ∧ n ≤ 8 → Optimum n
  | 1, _ => One.optimum
  | 2, _ => Two.optimum
  | 3, _ => Three.optimum
  | 4, _ => Four.optimum
  | 5, _ => Five.optimum
  | 6, _ => Six.optimum
  | 7, _ => Seven.optimum
  | 8, _ => Eight.optimum
  | 0, h | _+9, h => absurd h (by omega)

/-- `optimum n` has the radius `optimalRadius n` and the models
`optimalPackings n`. -/
lemma optimum_spec (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 8) :
    (optimum n hn).radius = optimalRadius n ∧ (optimum n hn).models = optimalPackings n := by
  match n, hn with
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => exact ⟨rfl,rfl⟩
  | 8, _ => exact ⟨Eight.radius_statement,Eight.models_statement⟩
  | 0, h | _+9, h => exact absurd h (by omega)

/-- `optimalRadius n` is the least radius of a disk that holds `n` unit squares
with disjoint interiors. -/
theorem optimal_radius (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 8) :
    IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} (optimalRadius n) :=
  (optimum_spec n hn).1 ▸ (optimum n hn).isLeast

/-- The packings in a disk of radius `optimalRadius n` are exactly the
configurations congruent to an optimal model. -/
theorem optimal_packings (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 8)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ M ∈ optimalPackings n, Congruent S o M := by
  rw [← (optimum_spec n hn).1,← (optimum_spec n hn).2]
  exact (optimum n hn).packing_iff S o

/-- The forward direction of `optimal_packings`, with the frame replaced by an
explicit isometry of the plane that takes the origin to the disk centre. -/
theorem optimal_packings_rigid (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 8)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    ∃ M ∈ optimalPackings n, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) := by
  rw [← (optimum_spec n hn).1] at hp
  rw [← (optimum_spec n hn).2]
  exact (optimum n hn).rigid_uniqueness S o hp

end SquaresInCircles
