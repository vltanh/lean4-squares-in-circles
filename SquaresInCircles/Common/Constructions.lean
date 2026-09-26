import SquaresInCircles.Common.Basic

/-! Axis-parallel unit squares: the disjointness and disk-containment tests
used by the attaining packings. -/
noncomputable section
namespace SquaresInCircles

/-- The axis-parallel unit square centred at `c`. -/
def axisSquare (c : Point) : UnitSquare where
  center := c
  cosine := 1
  sine := 0
  unit := by norm_num

lemma axisSquare_open (c p : Point) :
    openSquare (axisSquare c) p ↔ openAxisSquare c p.1 p.2 := by
  simp [axisSquare,openSquare,openAxisSquare,localX,localY]

lemma axisSquare_closed (c p : Point) :
    closedSquare (axisSquare c) p ↔ closedAxisSquare c p.1 p.2 := by
  simp [axisSquare,closedSquare,closedAxisSquare,localX,localY]

def AxisSeparated (p q : Point) : Prop :=
  p.1+1 ≤ q.1 ∨ q.1+1 ≤ p.1 ∨ p.2+1 ≤ q.2 ∨ q.2+1 ≤ p.2

lemma axis_disjoint {p q : Point} (hs : AxisSeparated p q) :
    ∀ x, ¬ (openSquare (axisSquare p) x ∧ openSquare (axisSquare q) x) := by
  rintro x ⟨hp,hq⟩
  simp only [axisSquare_open,openAxisSquare,abs_lt] at hp hq
  rcases hs with h | h | h | h <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2,
    hq.1.1,hq.1.2,hq.2.1,hq.2.2]

/-- Axis-parallel unit squares at pairwise separated centres, each inside the
disk of radius `R` about the origin, form a packing. -/
lemma axis_packing {n : ℕ} {c : Fin n → Point} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ i j, i ≠ j → AxisSeparated (c i) (c j))
    (hin : ∀ i, (|(c i).1|+1/2)^2+(|(c i).2|+1/2)^2 ≤ R^2) :
    Packing (fun i => axisSquare (c i)) (0,0) R := by
  refine ⟨hR,fun i p hp => ?_,fun i j hij => axis_disjoint (hsep i j hij)⟩
  rw [axisSquare_closed] at hp
  have hx : |p.1| ≤ |(c i).1|+1/2 := by linarith [abs_sub_abs_le_abs_sub p.1 (c i).1,hp.1]
  have hy : |p.2| ≤ |(c i).2|+1/2 := by linarith [abs_sub_abs_le_abs_sub p.2 (c i).2,hp.2]
  have := hin i
  simp only [inDisk,normSq,sub,sub_zero]
  nlinarith [sq_abs p.1,sq_abs p.2,abs_nonneg p.1,abs_nonneg p.2]

end SquaresInCircles
