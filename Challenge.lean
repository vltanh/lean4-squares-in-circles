module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Tactic

/-!
# Packing unit squares in a disk: the statement

The statement a reader audits. It imports only Mathlib, restates the
definitions of `SquaresInCircles/Geometry.lean` word for word, and states the
two main theorems, which the root module of the library `SquaresInCircles`
proves; Comparator checks that statements and definitions are identical.

A packing of `n` unit squares in a disk places `n` squares of side 1 in the
closed disk, each at its own position and rotation, so that no point is interior
to two squares. For `n = 1, …, 8` the theorems give the least radius of such a
disk, and every packing that attains it, up to a rotation about the disk centre
and a relabelling of the squares:

| `n` | least radius | the optimal packings |
| :-: | :-: | --- |
| 1 | `√2 / 2` | the square |
| 2 | `√5 / 2` | the 2 × 1 rectangle |
| 3 | `5√17 / 16` | the T: two squares side by side, and one centred on top of them |
| 4 | `√2` | the 2 × 2 block |
| 5 | `√(5/2)` | the plus: a square and its four side-neighbours |
| 6 | `√qStar ≈ 1.6885` | a square with four neighbours, two of them pushed along its sides, and a sixth square turned by `π/4` in the corner between those two |
| 7 | `√13 / 2` | two columns of two squares, and between them a column of three, each of which can move along the middle axis |
| 8 | `√qStar ≈ 1.9788` | five squares with a corner on the circle, four axis-parallel and one turned; two that slide, an axis-parallel one between two of them and a turned one beside the turned one; and a central square that moves and turns; with the reflections of these packings |

For `n = 8`, `qStar` is the squared radius of the unique solution of an
explicit stationary system (`EightStatement.IsStationary`), and the packings
are the models of the admissible parameters (`EightStatement.Parameters.Admissible`).

The theorems assume `1 ≤ n ≤ 8`. For every other `n`, `optimalRadius n` is the
placeholder `0`, `optimalPackings n` is empty, and nothing is claimed.

A unit square is a centre and an orthonormal frame; in the coordinates of its
frame it is `[-1/2, 1/2]²`, closed (`closedSquare`) or open (`openSquare`). A
packing asks that every closed square lie in the closed disk and that no point
lie in two open squares, so squares may touch each other and the circle.
Distances use the squared Euclidean length `normSq` (Mathlib's norm on
`ℝ × ℝ` is the maximum norm). Congruence compares point sets, since a quarter
turn of a frame describes the same square. It allows a rotation about the disk
centre and a relabelling, but no reflection: every optimal model for `n ≤ 7` is
symmetric under a reflection, and for `n = 8` the reflected models are listed.
-/

@[expose] public section

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

/-! ### The optimal radii and the optimal models

The models are given in the frame of the disk centre, which is the origin.
Every model is made of axis-parallel unit squares, except that the model for
six squares has one square turned by `π / 4`. -/

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

namespace Six

/-- `√2 / 2`, half the diagonal of a unit square. -/
def hStar : ℝ := Real.sqrt 2 / 2

/-- The linear coefficient of the quadratic `s ^ 2 - AStar * s + BStar`, whose
smaller root is `sStar`. -/
def AStar : ℝ := (1466 + 1940 * hStar) / 267

/-- The constant coefficient of the quadratic `s ^ 2 - AStar * s + BStar`. -/
def BStar : ℝ := (327 + 432 * hStar) / 712

/-- The discriminant of `s ^ 2 - AStar * s + BStar`. -/
def discriminant : ℝ := AStar ^ 2 - 4 * BStar

/-- The smaller root of `s ^ 2 - AStar * s + BStar`, about `0.0842`: the central
square of the model is centred at `(sStar, sStar)`. -/
def sStar : ℝ := 2 * BStar / (AStar + Real.sqrt discriminant)

/-- About `0.4202`: the squares left of and below the central square are
centred at `(sStar - 1, tStar)` and `(tStar, sStar - 1)`. -/
def tStar : ℝ := (-20 + 30 * hStar) * sStar + 7 / 2 - 9 * hStar / 2

/-- About `0.7869`: the turned square of the model is centred at
`(-dStar, -dStar)`. -/
def dStar : ℝ := 1 / 2 + hStar - tStar

/-- The square of the optimal radius, about `2.8512`. -/
def qStar : ℝ := 2 * sStar ^ 2 + 4 * sStar + 5 / 2

/-- The optimal radius for six unit squares, about `1.6885`: the distance from
the disk centre to the six points of the model on the circle. -/
def radius : ℝ := Real.sqrt qStar

/-- The unit square centred at `(-dStar, -dStar)` and turned by `π / 4`. -/
def diagonalSquare : UnitSquare where
  center := (-dStar, -dStar)
  cosine := hStar
  sine := hStar
  unit := by
    dsimp [hStar]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The optimal packing: a central square, one square on top of it and one to
its right, one to its left and one below it, pushed up and right by
`tStar - sStar`, and the turned square in the corner between those two. -/
def model : Fin 6 → UnitSquare :=
  ![axisSquare (sStar, sStar), axisSquare (sStar, sStar + 1),
    axisSquare (sStar + 1, sStar), axisSquare (sStar - 1, tStar),
    axisSquare (tStar, sStar - 1), diagonalSquare]

end Six

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

namespace EightStatement

/-- The cosine of the angle whose half has tangent `z`. -/
def halfAngleCos (z : ℝ) : ℝ := (1-z^2)/(1+z^2)
/-- The sine of the angle whose half has tangent `z`. -/
def halfAngleSin (z : ℝ) : ℝ := 2*z/(1+z^2)

theorem halfAngle_unit (z : ℝ) : halfAngleCos z^2+halfAngleSin z^2=1 := by
  have hd : 0<1+z^2 := by positivity
  unfold halfAngleCos halfAngleSin
  field_simp [ne_of_gt hd]
  ring

/-- The numbers of the five-corner chain: the squared radius `q`, the height `y` of the
lower right corner, the half-angle tangent `z` of the tilt of the two turned squares, and
the coordinates `x₁`, `x₂`, `y₃`, `x₄` of the corners on the circle. -/
structure Root where
  q : ℝ
  y : ℝ
  z : ℝ
  x₁ : ℝ
  x₂ : ℝ
  y₃ : ℝ
  x₄ : ℝ
  deriving Inhabited

namespace Root

/-- The cosine of the tilt. -/
def c (d : Root) : ℝ := halfAngleCos d.z
/-- The sine of the tilt. -/
def s (d : Root) : ℝ := halfAngleSin d.z
/-- The abscissa of the upper left corner, three to the left of `x₂`. -/
def x₃ (d : Root) : ℝ := d.x₂-3
/-- The height of the lower left corner, two below `y₃`. -/
def y₄ (d : Root) : ℝ := d.y₃-2
/-- The first coordinate, in the tilted frame, of the fifth corner, a corner of `H`. -/
def h₁ (d : Root) : ℝ := d.c*d.x₁+d.s*d.y-2-d.c
/-- The second coordinate of the fifth corner. -/
def h₂ (d : Root) : ℝ := -d.s*d.x₄+d.c*d.y₄-1-d.s
/-- How far the fifth corner is from the circle: `h₁² + h₂² - q`. -/
def defect (d : Root) : ℝ := d.h₁^2+d.h₂^2-d.q
/-- The derivative of `y₄` in `y` along the chain. -/
def y₄deriv (d : Root) : ℝ := d.x₃*(d.y+2)/(d.y₃*d.x₂)
/-- The derivative of `h₁` in `y` along the chain. -/
def h₁deriv (d : Root) : ℝ := d.s-d.c*d.y/d.x₁
/-- The derivative of `h₂` in `y` along the chain. -/
def h₂deriv (d : Root) : ℝ := (d.c+d.s*d.y₄/d.x₄)*d.y₄deriv
/-- The derivative of the defect in `y`, along the chain. -/
def positionDerivative (d : Root) : ℝ := 2*(d.h₁*d.h₁deriv+d.h₂*d.h₂deriv)
/-- The derivative of the defect in the tilt. -/
def tiltDerivative (d : Root) : ℝ :=
  2*(d.h₁*(-d.s*(d.x₁-1)+d.c*d.y)+d.h₂*(-d.c*(d.x₄+1)-d.s*d.y₄))

/-- The four corners `(x₁, y)`, `(x₂, y + 2)`, `(x₃, y₃)`, `(x₄, y₄)` lie on the circle of
squared radius `q`, on the sides of the axes that the signs select. -/
structure IsChain (d : Root) : Prop where
  x₁_pos : 0<d.x₁
  x₂_pos : 0<d.x₂
  y₃_pos : 0<d.y₃
  x₄_neg : d.x₄<0
  first_circle : d.x₁^2+d.y^2=d.q
  second_circle : d.x₂^2+(d.y+2)^2=d.q
  third_circle : d.x₃^2+d.y₃^2=d.q
  fourth_circle : d.x₄^2+d.y₄^2=d.q

/-- The stationary system: the chain closes (the defect vanishes) and the defect is
stationary in the position and in the tilt, inside a strip of the parameters. The system
has exactly one solution. -/
structure IsStationary (d : Root) : Prop extends IsChain d where
  q_lower : (79/40 : ℝ)^2≤d.q
  q_upper : d.q≤9789/2500
  y_lower : -1<d.y
  y_upper : d.y< -(1/2)
  y₄_lower : -1<d.y₄
  y₄_upper : d.y₄< -(1/2)
  position_order : d.y<d.y₄
  z_pos : 0<d.z
  tilt_range : 2*d.z/(1-d.z^2)<1/5
  z_lt_one : d.z<1
  zero_defect : d.defect=0
  position_stationary : d.positionDerivative=0
  tilt_stationary : d.tiltDerivative=0

/-- The point with coordinates `(a, b)` in the tilted frame. -/
def inFrame (d : Root) (a b : ℝ) : Point :=
  (d.c*a-d.s*b,d.s*a+d.c*b)

/-- The centre of `A`, whose lower right corner is `(x₁, y)`. -/
def pA (d : Root) : Point := (d.x₁-1/2,d.y+1/2)
/-- The centre of `B`, whose upper right corner is `(x₂, y + 2)`. -/
def pB (d : Root) : Point := (d.x₂-1/2,d.y+3/2)
/-- The centre of `D`, whose upper left corner is `(x₃, y₃)`. -/
def pD (d : Root) : Point := (d.x₃+1/2,d.y₃-1/2)
/-- The centre of `E`, whose lower left corner is `(x₄, y₄)`. -/
def pE (d : Root) : Point := (d.x₄+1/2,d.y₄+1/2)
/-- The centre of the turned square `H`, with the corner `(h₁, h₂)` in the tilted frame. -/
def pH (d : Root) : Point := d.inFrame (d.h₁+1/2) (d.h₂+1/2)
/-- The centre of `T`, between `D` and `B`, at height `Z`. -/
def pT (d : Root) (Z : ℝ) : Point := (d.x₂-3/2,Z)
/-- The centre of the turned square `G`, beside `H`, at offset `η` along the tilted frame. -/
def pG (d : Root) (η : ℝ) : Point := d.inFrame (d.h₁+3/2) (d.h₂+1/2+η)

/-- The unit square centred at `p` with the tilted frame. -/
def tiltedSquare (d : Root) (p : Point) : UnitSquare where
  center := p
  cosine := d.c
  sine := d.s
  unit := halfAngle_unit d.z

/-- The greatest height of `T` in the disk. -/
def zMax (d : Root) : ℝ := Real.sqrt (d.q-(d.x₂-1)^2)-1/2
/-- The least offset of `G` in the disk. -/
def etaMin (d : Root) : ℝ := -d.h₂-Real.sqrt (d.q-(d.h₁+2)^2)
/-- The greatest offset of `G`: its side nearest the centre then lies at distance `1/12`
from it, as the side of `T` does at the least height `7/12`. -/
def etaMax (d : Root) : ℝ := -d.h₂-13/12

end Root

/-- The solution of the stationary system. It is unique, so the choice is not arbitrary. -/
def selected : Root := Classical.epsilon Root.IsStationary

/-- The squared optimal radius for eight unit squares. -/
def qStar : ℝ := selected.q

/-- The optimal radius for eight unit squares, `√qStar ≈ 1.97877`. -/
def radius : ℝ := Real.sqrt qStar

/-- The five free numbers of an optimal packing: the centre `(x, y)` and the half-angle
tangent `w` of the turn of the central square, the height `z` of `T`, and the offset `eta`
of `G`. -/
structure Parameters where
  x : ℝ
  y : ℝ
  w : ℝ
  z : ℝ
  eta : ℝ

namespace Parameters

/-- The cosine of the turn of the central square. -/
def C (p : Parameters) : ℝ := halfAngleCos p.w
/-- The sine of the turn of the central square. -/
def S (p : Parameters) : ℝ := halfAngleSin p.w
def center (p : Parameters) : Point := (p.x,p.y)

/-- The central square. -/
def centralSquare (p : Parameters) : UnitSquare where
  center := p.center
  cosine := p.C
  sine := p.S
  unit := halfAngle_unit p.w

/-- The largest absolute projection of `v` on the axes of the coordinate frame and of the
frame of the central square. -/
def M₀ (p : Parameters) (v : Point) : ℝ :=
  max (max |v.1| |v.2|) (max |p.C*v.1+p.S*v.2| |-p.S*v.1+p.C*v.2|)

/-- The largest absolute projection of `v` on the axes of the tilted frame and of the frame
of the central square. -/
def Mₜ (p : Parameters) (d : Root) (v : Point) : ℝ :=
  max (max |d.c*v.1+d.s*v.2| |-d.s*v.1+d.c*v.2|)
    (max |p.C*v.1+p.S*v.2| |-p.S*v.1+p.C*v.2|)

/-- The separation threshold of an axis-parallel square and the central square: half the
sum of their widths along an axis of either. -/
def W₀ (p : Parameters) : ℝ := (1+p.C+|p.S|)/2
/-- The separation threshold of a tilted square and the central square. -/
def Wₜ (p : Parameters) (d : Root) : ℝ :=
  (1+d.c*p.C+d.s*p.S+|d.c*p.S-d.s*p.C|)/2

/-- The parameters of the optimal packings: the turn of the central square in a half-open
interval; `T` and `G` in the disk, with their sides nearest the centre at distance at least
`1/12` from it; the disk centre less than `5/12` from the centre of the central square along
each of its axes; and the central square separated by an axis from each of the seven other
squares. -/
structure Admissible (d : Root) (p : Parameters) : Prop where
  frame_lower : 1-Real.sqrt 2≤p.w
  frame_upper : p.w<Real.sqrt 2-1
  top_lower : 7/12≤p.z
  top_upper : p.z≤d.zMax
  tilted_lower : d.etaMin≤p.eta
  tilted_upper : p.eta≤d.etaMax
  core_first : |p.C*p.x+p.S*p.y|<5/12
  core_second : |-p.S*p.x+p.C*p.y|<5/12
  A_sep : p.W₀≤p.M₀ (sub d.pA p.center)
  B_sep : p.W₀≤p.M₀ (sub d.pB p.center)
  D_sep : p.W₀≤p.M₀ (sub d.pD p.center)
  E_sep : p.W₀≤p.M₀ (sub d.pE p.center)
  T_sep : p.W₀≤p.M₀ (sub (d.pT p.z) p.center)
  H_sep : p.Wₜ d≤p.Mₜ d (sub d.pH p.center)
  G_sep : p.Wₜ d≤p.Mₜ d (sub (d.pG p.eta) p.center)

/-- The packing of parameters `p`: the central square, the turned squares `H` and `G`, and
the axis-parallel squares `A`, `B`, `T`, `D`, `E`. -/
def model (d : Root) (p : Parameters) : Fin 8 → UnitSquare :=
  ![p.centralSquare,d.tiltedSquare d.pH,d.tiltedSquare (d.pG p.eta),
    axisSquare d.pA,axisSquare d.pB,axisSquare (d.pT p.z),axisSquare d.pD,axisSquare d.pE]

end Parameters

/-- The reflection of a square in the diagonal `x = y`. -/
def reflectSquare (K : UnitSquare) : UnitSquare where
  center := (K.center.2,K.center.1)
  cosine := K.sine
  sine := K.cosine
  unit := by linarith [K.unit]

/-- The packing of parameters `p`, or its reflection in the diagonal. -/
def reflectedModel (reflected : Bool) (p : Parameters) : Fin 8 → UnitSquare :=
  if reflected then fun i=>reflectSquare (p.model selected i) else p.model selected

/-- The optimal packings of eight unit squares, as models about the origin: the packings of
admissible parameters and their reflections. Congruence turns but never reflects, so the
reflections are listed. -/
def models : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool,∃ p : Parameters,
    p.Admissible selected ∧ M=reflectedModel reflected p}

end EightStatement

/-- The optimal radius for `n` unit squares, for `1 ≤ n ≤ 8`. Every other `n`
gets the placeholder `0`, about which nothing is claimed. -/
def optimalRadius : ℕ → ℝ
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 6 => Six.radius
  | 7 => Seven.radius
  | 8 => EightStatement.radius
  | _ => 0

/-- The optimal packings of `n` unit squares, as models about the origin: one
packing for `n ≤ 6`, for `n = 7` every position of the three middle squares,
and for `n = 8` the five-parameter family and its reflections. Every other `n`
gets the placeholder `∅`, about which nothing is claimed. -/
def optimalPackings : (n : ℕ) → Set (Fin n → UnitSquare)
  | 1 => {One.model}
  | 2 => {Two.model}
  | 3 => {Three.model}
  | 4 => {Four.model}
  | 5 => {Five.model}
  | 6 => {Six.model}
  | 7 => Set.range Seven.columnModel
  | 8 => EightStatement.models
  | _ => ∅

/-! ### The theorems -/

/-- `optimalRadius n` is the least radius of a disk that holds `n` unit squares
with disjoint interiors: some packing of `n` unit squares fits in a disk of
that radius, and none fits in a disk of smaller radius. -/
theorem optimal_radius (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 8) :
    IsLeast {R | ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o R} (optimalRadius n) := by
  sorry

/-- The packings in a disk of radius `optimalRadius n` are exactly the
configurations congruent to an optimal model: the model, turned about the disk
centre and relabelled. For `n ≤ 6` the optimal packing is therefore unique up
to rotation and relabelling, for `n = 7` they are the column packings, and for
`n = 8` they are the five-parameter family and its reflected models. -/
theorem optimal_packings (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 8)
    (S : Fin n → UnitSquare) (o : Point) :
    Packing S o (optimalRadius n) ↔ ∃ M ∈ optimalPackings n, Congruent S o M := by
  sorry

end SquaresInCircles
