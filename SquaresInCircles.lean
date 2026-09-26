import SquaresInCircles.One.Uniqueness
import SquaresInCircles.Two.Uniqueness
import SquaresInCircles.Three.Uniqueness
import SquaresInCircles.Four.Uniqueness
import SquaresInCircles.Five.Uniqueness
import SquaresInCircles.Seven.Uniqueness

/-!
# Packing one to five, and seven, unit squares in a disk

For `1 ≤ n ≤ 5` and `n = 7`, `optimalRadius n` is the smallest radius of a disk
containing `n` non-overlapping unit squares, and the packings that attain it
are exactly the normal forms of the layouts `optimalLayouts n`. For `n ≤ 5`
there is one layout, `modelCenters n`, so the optimal packing is unique up to a
rotation about the disk centre and a relabelling of the squares. For `n = 7`
the middle column of the layout slides.

Every case proves the same statement, an `Optimum` (`Common/Optimum.lean`), and
can also be imported on its own, from its folder `SquaresInCircles/One/` to
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

/-- The optimal packings, in the frame of their disk centres. For `n = 7`, the
one with the middle column centred. -/
def modelCenters : (n : ℕ) → Fin n → Point
  | 1 => One.centers
  | 2 => Two.centers
  | 3 => Three.centers
  | 4 => Four.centers
  | 5 => Five.centers
  | 7 => Seven.centers
  | _ => fun _ => (0,0)

/-- The layouts of all optimal packings: `modelCenters n` alone for `n ≤ 5`,
and every position of the middle column for `n = 7`. -/
def optimalLayouts : (n : ℕ) → Set (Fin n → Point)
  | 7 => Set.range Seven.slidingCenters
  | n => {modelCenters n}

/-- The optimum for each `n` with `1 ≤ n ≤ 5` or `n = 7`. -/
def optimum : (n : ℕ) → 1 ≤ n ∧ n ≤ 5 ∨ n = 7 → Optimum n
  | 1, _ => One.optimum
  | 2, _ => Two.optimum
  | 3, _ => Three.optimum
  | 4, _ => Four.optimum
  | 5, _ => Five.optimum
  | 7, _ => Seven.optimum
  | 0, h | 6, h | _+8, h => absurd h (by omega)

/-- `optimum n` has the radius and the layouts of the tables above. -/
lemma optimum_spec (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    (optimum n hn).radius = optimalRadius n ∧ (optimum n hn).layouts = optimalLayouts n := by
  match n, hn with
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 7, _ => exact ⟨rfl,rfl⟩
  | 0, h | 6, h | _+8, h => exact absurd h (by omega)

theorem optimality (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    optimalRadius n ≤ R :=
  (optimum_spec n hn).1 ▸ (optimum n hn).optimality S o R hp

theorem attainment (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n) :=
  (optimum_spec n hn).1 ▸ (optimum n hn).attainment

/-- The packings at the optimal radius are exactly the normal forms of the
optimal layouts. -/
theorem packing_iff (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ c ∈ optimalLayouts n, HasNormalForm S o c := by
  rw [← (optimum_spec n hn).1,← (optimum_spec n hn).2]
  exact (optimum n hn).packing_iff S o

theorem uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    ∃ c ∈ optimalLayouts n, HasNormalForm S o c :=
  (packing_iff n hn S o).mp hp

/-- Uniqueness with the frame replaced by an explicit isometry of the plane that
takes the origin to the disk centre. -/
theorem rigid_uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    ∃ c ∈ optimalLayouts n, ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openAxisSquare (c i) p.1 p.2) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedAxisSquare (c i) p.1 p.2)) := by
  rw [← (optimum_spec n hn).1] at hp
  rw [← (optimum_spec n hn).2]
  exact (optimum n hn).rigid_uniqueness S o hp

/-- The optimum for `n` unit squares: lower bound, attainment, and the optimal
packings. -/
theorem optimality_attainment_uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    (∀ (S : Fin n → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → optimalRadius n ≤ R) ∧
    (∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n)) ∧
    (∀ (S : Fin n → UnitSquare) (o : Point),
      Packing S o (optimalRadius n) ↔ ∃ c ∈ optimalLayouts n, HasNormalForm S o c) :=
  ⟨optimality n hn,attainment n hn,packing_iff n hn⟩

end SquaresInCircles
