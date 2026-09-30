module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Squares, disks, packings, congruence and the optimal models

The public problem definitions and exact models for one through seven squares.
Each square has its own position and rotation. Packing requires containment of
closed squares and disjoint open interiors, so contact is allowed.

Challenge.lean restates the definitions below word for word and in the same
order. The comparator checks that the public theorem statements use those
identical definitions. Keep both copies synchronized with the definition-copy
step in scripts/verify-comparator.sh; compiler execution is a separate check.
-/

noncomputable section
namespace SquaresInCircles

/-! ### Squares, disks, packings and congruence -/

/-- A point of the plane, by its two real coordinates. -/
abbrev Point := ℝ × ℝ

/-- The squared Euclidean length `x ^ 2 + y ^ 2` of `p = (x, y)`. -/
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
/-- The difference `p - q`, coordinate by coordinate. -/
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)

/-- A unit square, by its centre and the orthonormal frame formed by the
columns `(cosine,sine)` and `(-sine,cosine)`: the square is turned by the angle
whose cosine is `cosine` and whose sine is `sine`. -/
structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1

/-- The first coordinate of `p` in the frame of `S`, measured from its centre. -/
def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)

/-- The second coordinate of `p` in the frame of `S`, measured from its centre. -/
def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)

/-- `p` lies in the closed unit square `S`: both of its coordinates in the frame
of `S` are in `[-1/2, 1/2]`. -/
def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2

/-- `p` lies in the interior of `S`: both of its coordinates in the frame of `S`
are in `(-1/2, 1/2)`. -/
def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2

/--
Membership in the closed disk of centre `o` and radius `R`, intended for
`0 ≤ R`. The squared form means `inDisk o R p` and `inDisk o (-R) p` agree, so
for negative `R` this is the disk of radius `|R|` rather than an empty set.
Every use here goes through `Packing`, whose first conjunct supplies `0 ≤ R`.
-/
def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2

/-- `n` unit squares packed in the closed disk of centre `o` and radius `R`:
the radius is nonnegative, every closed square lies in the closed disk, and no
point is interior to two different squares. -/
def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))

/-- A direction in the plane: an angle modulo `2 * π`. -/
abbrev Direction := Real.Angle

/-- The point with coordinates `(x, y)` in the frame at `o` rotated by `phase`:
`o` plus the vector `(x, y)` turned by the angle `phase`. -/
def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1 + phase.cos * x - phase.sin * y, o.2 + phase.sin * x + phase.cos * y)

/-- The axis-parallel unit square centred at `c`. -/
def axisSquare (c : Point) : UnitSquare where
  center := c
  cosine := 1
  sine := 0
  unit := by norm_num

/--
`S` is the configuration `M`, given about the origin, turned about the origin
by one angle `φ`, moved to `o`, and relabelled by `σ`: square `σ i` is exactly
`M i` read in the frame at `o` turned by `φ`, both as an open and as a closed
set.
-/
def Congruent {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (M : Fin n → UnitSquare) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i p,
    (openSquare (S (σ i)) (pointInDirection o φ p.1 p.2) ↔ openSquare (M i) p) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ p.1 p.2) ↔ closedSquare (M i) p)

/-! ### The optimal radii and models

Models are specified about the origin. The six-square model has one genuinely
rotated square; all squares in the other displayed models are axis-parallel. -/

namespace One

/-- The optimal radius for one unit square: half its diagonal. -/
def radius : ℝ := Real.sqrt 2 / 2

/-- The centre of the square. -/
def centers : Fin 1 → Point := ![(0,0)]

/-- The unit square centred at the origin. -/
def model : Fin 1 → UnitSquare := fun i => axisSquare (centers i)

end One

namespace Two

/-- The optimal radius for two unit squares: half the diagonal of the 2 × 1
rectangle. -/
def radius : ℝ := Real.sqrt 5 / 2

/-- The centres of the rectangle. -/
def centers : Fin 2 → Point := ![(-1/2,0),(1/2,0)]

/-- The 2 × 1 rectangle, centred at the origin. -/
def model : Fin 2 → UnitSquare := fun i => axisSquare (centers i)

end Two

namespace Three

/-- The optimal radius for three unit squares: the distance from the disk
centre to the four outer corners of the T. -/
def radius : ℝ := 5 * Real.sqrt 17 / 16

/-- The centres of the T: two squares side by side, and one centred on top of
them. The disk centre is at height `5/16` above the lower pair. -/
def centers : Fin 3 → Point := ![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]

/-- The T. -/
def model : Fin 3 → UnitSquare := fun i => axisSquare (centers i)

end Three

namespace Four

/-- The optimal radius for four unit squares: half the diagonal of the 2 × 2
block. -/
def radius : ℝ := Real.sqrt 2

/-- The centres of the 2 × 2 block. -/
def centers : Fin 4 → Point := ![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]

/-- The 2 × 2 block, centred at the origin. -/
def model : Fin 4 → UnitSquare := fun i => axisSquare (centers i)

end Four

namespace Five

/-- The optimal radius for five unit squares: the distance from the disk centre
to the eight outer corners of the plus. -/
def radius : ℝ := Real.sqrt (5 / 2)

/-- The centres of the plus: a square at the origin and its four
side-neighbours. -/
def centers : Fin 5 → Point := ![(0,0),(1,0),(0,1),(-1,0),(0,-1)]

/-- The plus, centred at the origin. -/
def model : Fin 5 → UnitSquare := fun i => axisSquare (centers i)

end Five

namespace Seven

/-- The optimal radius for seven unit squares: the distance from the disk centre
to the outer corners `(±3/2, ±1)` of the two side columns. -/
def radius : ℝ := Real.sqrt 13 / 2

/-- How far a centre of the middle column can be from the disk centre: a unit
square centred at `(0, y)` lies in the disk of radius `√13 / 2` exactly when
`|y| ≤ √3 - 1/2`. -/
def columnLimit : ℝ := Real.sqrt 3 - 1 / 2

/-- The heights of the three centres of the middle column: at least 1 apart,
and within `columnLimit` of the disk centre. Every such triple occurs, so the
three middle squares can each move along the middle axis. -/
structure Column where
  bottom : ℝ
  middle : ℝ
  top : ℝ
  lower : -columnLimit ≤ bottom
  gap_lower : bottom + 1 ≤ middle
  gap_upper : middle + 1 ≤ top
  upper : top ≤ columnLimit

/-- The four centres of the side columns, then the three centres of the middle
column. -/
def columnCenters (c : Column) : Fin 7 → Point :=
  ![(1, -1/2), (1, 1/2), (-1, -1/2), (-1, 1/2),
    (0, c.bottom), (0, c.middle), (0, c.top)]

/-- The column packing of `c`: axis-parallel unit squares at
`columnCenters c`. -/
def columnModel (c : Column) : Fin 7 → UnitSquare :=
  fun i => axisSquare (columnCenters c i)

end Seven

namespace Six

/-- Half the diagonal of a unit square. -/
def hStar : ℝ := Real.sqrt 2 / 2

def AStar : ℝ := (1466 + 1940 * hStar) / 267

def BStar : ℝ := (327 + 432 * hStar) / 712

def discriminant : ℝ := AStar ^ 2 - 4 * BStar

/-- The small positive root, written in its numerically stable radical form. -/
def sStar : ℝ := 2 * BStar / (AStar + Real.sqrt discriminant)

def tStar : ℝ := (-20 + 30 * hStar) * sStar + 7 / 2 - 9 * hStar / 2

def dStar : ℝ := 1 / 2 + hStar - tStar

/-- Exact squared radius of the six-square model. -/
def qStar : ℝ := 2 * sStar ^ 2 + 4 * sStar + 5 / 2

def radius : ℝ := Real.sqrt qStar

/-- The one diagonal square in the six-square model. -/
def diagonalSquare : UnitSquare where
  center := (-dStar, -dStar)
  cosine := hStar
  sine := hStar
  unit := by
    dsimp [hStar]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The exact model in C,N,E,W,S,D order. -/
def model : Fin 6 → UnitSquare :=
  ![axisSquare (sStar, sStar), axisSquare (sStar, sStar + 1),
    axisSquare (sStar + 1, sStar), axisSquare (sStar - 1, tStar),
    axisSquare (tStar, sStar - 1), diagonalSquare]

end Six

/-- The optimal radius for `n` unit squares for `1 ≤ n ≤ 7`.
Other values receive the placeholder zero and are not covered by the theorems. -/
def optimalRadius : ℕ → ℝ
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 6 => Six.radius
  | 7 => Seven.radius
  | _ => 0

/-- Optimal models about the origin: a single model for `1 ≤ n ≤ 6`, and the
column family for `n = 7`. Other values receive the empty placeholder set. -/
def optimalPackings : (n : ℕ) → Set (Fin n → UnitSquare)
  | 1 => {One.model}
  | 2 => {Two.model}
  | 3 => {Three.model}
  | 4 => {Four.model}
  | 5 => {Five.model}
  | 6 => {Six.model}
  | 7 => Set.range Seven.columnModel
  | _ => ∅

end SquaresInCircles
