module
public import SquaresInCircles.Six.NormalizeFrame

@[expose] public section

/-!
# The permitted diagonal reflection

Reflection is a point-set operation on the original square predicates. It
preserves the disk centered at zero. Proposition A uses it temporarily to
prove a symmetric bound; the later D normalization may use it once globally.
No horizontal reflection or altered D-angle domain is introduced.
-/

noncomputable section
namespace SquaresInCircles.Six

def diagonalPoint (p : Point) : Point := (p.2,p.1)

def reflectDiagonalSquare (S : UnitSquare) : UnitSquare where
  center := diagonalPoint S.center
  cosine := S.sine
  sine := S.cosine
  unit := by linarith [S.unit]

@[simp] lemma diagonalPoint_involutive (p : Point) : diagonalPoint (diagonalPoint p) = p := by
  cases p
  rfl

lemma reflectDiagonal_localX (S : UnitSquare) (p : Point) :
    localX (reflectDiagonalSquare S) p = localX S (diagonalPoint p) := by
  dsimp [localX,reflectDiagonalSquare,diagonalPoint]
  ring

lemma reflectDiagonal_localY (S : UnitSquare) (p : Point) :
    localY (reflectDiagonalSquare S) p = -localY S (diagonalPoint p) := by
  dsimp [localY,reflectDiagonalSquare,diagonalPoint]
  ring

lemma reflectDiagonal_open (S : UnitSquare) (p : Point) :
    openSquare (reflectDiagonalSquare S) p ↔ openSquare S (diagonalPoint p) := by
  simp only [openSquare,reflectDiagonal_localX,reflectDiagonal_localY,abs_neg]

lemma reflectDiagonal_closed (S : UnitSquare) (p : Point) :
    closedSquare (reflectDiagonalSquare S) p ↔ closedSquare S (diagonalPoint p) := by
  simp only [closedSquare,reflectDiagonal_localX,reflectDiagonal_localY,abs_neg]

lemma diagonalPoint_inDisk (p : Point) (R : ℝ) :
    inDisk (0,0) R (diagonalPoint p) ↔ inDisk (0,0) R p := by
  simp [inDisk,normSq,sub,diagonalPoint,add_comm]

lemma packing_reflectDiagonal {n : ℕ} {S : Fin n → UnitSquare} {R : ℝ}
    (hp : Packing S (0,0) R) : Packing (fun i => reflectDiagonalSquare (S i)) (0,0) R := by
  refine ⟨hp.1,?_,?_⟩
  · intro i p hi
    exact (diagonalPoint_inDisk p R).mp
      (hp.2.1 i _ ((reflectDiagonal_closed (S i) p).mp hi))
  · intro i j hij p hi
    exact hp.disjoint i j hij _
      ⟨(reflectDiagonal_open (S i) p).mp hi.1,(reflectDiagonal_open (S j) p).mp hi.2⟩

lemma diagonal_axis_open (c p : Point) :
    openSquare (axisSquare c) (diagonalPoint p) ↔
      openSquare (axisSquare (diagonalPoint c)) p := by
  simp [axisSquare_open,openAxisSquare,diagonalPoint,and_comm]

lemma reflected_central_axis {S : UnitSquare} {c : Point}
    (h : ∀ p, openSquare S p ↔ openSquare (axisSquare c) p) :
    ∀ p, openSquare (reflectDiagonalSquare S) p ↔
      openSquare (axisSquare (diagonalPoint c)) p := by
  intro p
  exact (reflectDiagonal_open S p).trans ((h _).trans (diagonal_axis_open c p))

end SquaresInCircles.Six
