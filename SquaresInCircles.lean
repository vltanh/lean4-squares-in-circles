import SquaresInCircles.One.Uniqueness
import SquaresInCircles.Two.Uniqueness
import SquaresInCircles.Three.Uniqueness
import SquaresInCircles.Four.Uniqueness
import SquaresInCircles.Five.Uniqueness
import SquaresInCircles.Six.Uniqueness
import SquaresInCircles.Seven.Uniqueness

/-!
# Packing one through seven unit squares in a disk

For 1 <= n <= 7, optimalRadius n is the least radius of a disk that holds n
unit squares with disjoint interiors. At that radius every packing is congruent
to one of the exact models in optimalPackings n. Cases 1 through 6 have one
model; case 7 has the column family. The six-square model includes its genuinely
rotated diagonal square. The problem predicates and congruence are unchanged.

Each case supplies the same Optimum interface. The exact public definitions
live in Geometry.lean and are mirrored independently in Challenge.lean.
The new n=6 source proofs have not yet undergone the deferred compiler and
kernel/axiom audit; the source-completion and execution records are separate.
-/

noncomputable section
namespace SquaresInCircles

/-- The optimum for every n from one through seven. -/
def optimum : (n : ℕ) → 1 ≤ n ∧ n ≤ 7 → Optimum n
  | 1, _ => One.optimum
  | 2, _ => Two.optimum
  | 3, _ => Three.optimum
  | 4, _ => Four.optimum
  | 5, _ => Five.optimum
  | 6, _ => Six.optimum
  | 7, _ => Seven.optimum
  | 0, h | _+8, h => absurd h (by omega)

lemma optimum_spec (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 7) :
    (optimum n hn).radius = optimalRadius n ∧ (optimum n hn).models = optimalPackings n := by
  match n, hn with
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => exact ⟨rfl,rfl⟩
  | 0, h | _+8, h => exact absurd h (by omega)

/-- The least disk radius for each of one through seven unit squares. -/
theorem optimal_radius (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 7) :
    IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} (optimalRadius n) :=
  (optimum_spec n hn).1 ▸ (optimum n hn).isLeast

/-- Exact equality classification with the unchanged point-set congruence. -/
theorem optimal_packings (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 7)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ M ∈ optimalPackings n, Congruent S o M := by
  rw [← (optimum_spec n hn).1,← (optimum_spec n hn).2]
  exact (optimum n hn).packing_iff S o

/-- Equality classification with an explicit rigid motion of the plane. -/
theorem optimal_packings_rigid (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 7)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    ∃ M ∈ optimalPackings n, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) := by
  rw [← (optimum_spec n hn).1] at hp
  rw [← (optimum_spec n hn).2]
  exact (optimum n hn).rigid_uniqueness S o hp

end SquaresInCircles
