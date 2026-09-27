# Definitions

[Back to the README](../README.md)

These definitions carry the entire meaning of the results. All of them are in
`SquaresInCircles/Geometry.lean`, and `Challenge.lean` restates them word for
word.

## The plane

```lean
abbrev Point := ℝ × ℝ

def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)
```

A point is a pair of reals — the Euclidean plane in coordinates. `normSq p` is
the **squared** Euclidean length of `p`, and the statements measure distances
only with it, so `Real.sqrt` appears in them only in the radii. (Mathlib's
`dist` on `ℝ × ℝ` is the maximum metric.)

## Squares

```lean
structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1
```

A square is a centre plus an orientation. The orientation is stored as the pair
`(cosine, sine)` rather than as an angle `θ`:

- `unit` forces `cosine² + sine² = 1`, so the vectors `(cosine, sine)` and
  `(-sine, cosine)` are unit length and perpendicular. They are the square's own
  axes — an **orthonormal frame**.
- Storing the pair rather than an angle keeps the statement algebraic, with no
  branch cut and no ambiguity of `θ` modulo `2π`. Every `θ` gives such a
  pair, and every such pair comes from some `θ` (`frame_angle`), so nothing is
  lost. The proofs do use angles, as elements of `Real.Angle`, to parametrize
  circles.
- The fields are per-square, so the squares rotate **independently**.

```lean
def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)

def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)
```

`localX`/`localY` give the coordinates of `p` in the square's own frame:
translate so the centre is the origin, then project onto the two axes. Because
the frame is orthonormal this is a rigid change of coordinates — it preserves
distances, so a set that is a unit square in local coordinates is a unit square
in the plane.

```lean
def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2

def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2
```

In local coordinates the square is the box `[-1/2, 1/2]²`, whose side is
`1/2 - (-1/2) = 1` — genuinely a **unit** square. The two versions differ only
in strictness: `closedSquare` includes the boundary, `openSquare` is the
interior. Non-overlap is stated with `openSquare`, so squares may touch along
edges or at corners but may not share interior area. Every optimal packing
but the single square relies on this.

## The disk

```lean
def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2
```

`p` lies within distance `R` of `o`, written squared to stay polynomial. Since
`‖p - o‖ ≤ R ⟺ ‖p - o‖² ≤ R²` when both sides are nonnegative, and `≤` is
non-strict, this is the **closed** disk. Note the squaring makes `inDisk o R p`
and `inDisk o (-R) p` agree, so the definition is only meaningful given
`0 ≤ R`, which `Packing` supplies.

## Packing

```lean
def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))
```

Three conditions, and nothing else:

- `0 ≤ R` — the radius is nonnegative.
- **Containment** — every point of every closed square lies in the disk.
  Stated with `closedSquare`, so boundaries must fit too.
- **Non-overlap** — no point is interior to two distinct squares.

What the encoding leaves free:

- `S : Fin n → UnitSquare` is an arbitrary family, each square with its own
  frame, so the squares are independently placed and independently rotated.
- `o` and `R` are universally quantified in the theorems, so the disk centre
  ranges over the whole plane.
- The hypothesis is `Packing` alone: orientations, separating axes, arcs,
  tangents and the lower bound all come out of the proof.

## The optimal radii

Each case has its radius, and `optimalRadius` collects them:

```lean
def One.radius : ℝ := Real.sqrt 2 / 2
def Two.radius : ℝ := Real.sqrt 5 / 2
def Three.radius : ℝ := 5 * Real.sqrt 17 / 16
def Four.radius : ℝ := Real.sqrt 2
def Five.radius : ℝ := Real.sqrt (5 / 2)
def Seven.radius : ℝ := Real.sqrt 13 / 2

def optimalRadius : ℕ → ℝ
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 7 => Seven.radius
  | _ => 0
```

Each value is the distance from the disk centre to the outermost corners of the
optimal packing. Their squares `1/2`, `5/4`, `425/256`, `2`, `5/2` and `13/4`
are rational (`One.radius_sq`, …, `Five.radius_sq`, `Seven.radius_sq`). The
proofs work with the squared radius, so the contact inequalities stay
polynomial, which is what `nlinarith` needs. That no smaller radius works is
proved once for all cases (`Optimum.optimality`): a packing in a smaller disk
would also lie in the optimal disk, so it would be congruent to an optimal
model, and the outermost corners of that model would lie outside the smaller
disk.

## Congruence

Uniqueness says that every packing at the optimal radius is an optimal model,
placed at the disk centre, turned by one rotation about it, with the squares
relabelled. It is stated about point sets:

```lean
abbrev Direction := Real.Angle

def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1 + phase.cos * x - phase.sin * y, o.2 + phase.sin * x + phase.cos * y)

def Congruent {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (M : Fin n → UnitSquare) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i p,
    (openSquare (S (σ i)) (pointInDirection o φ p.1 p.2) ↔ openSquare (M i) p) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ p.1 p.2) ↔ closedSquare (M i) p)
```

`pointInDirection o φ` reads coordinates `(x, y)` in the frame at the disk
centre `o`, rotated by `φ`; it is a rotation about the origin followed by the
translation to `o`, so it preserves distances. The model `M` is a configuration
about the origin. `Congruent S o M` says that in one such frame, after
relabelling by `σ`, square `σ i` is exactly the model square `M i`, both as an
open and as a closed set. It compares point sets rather than `UnitSquare`
records, because a quarter-turn of a frame describes the same square. No
reflection is needed, since each optimal model is symmetric under one.

## The optimal packings

Every optimal model is made of axis-parallel unit squares:

```lean
def axisSquare (c : Point) : UnitSquare where
  center := c
  cosine := 1
  sine := 0
  unit := by norm_num
```

For `n ≤ 5` the optimal packing is unique. Its model is
`fun i => axisSquare (centers i)`, with the disk centre at the origin and these
centres:

| n | `centers` | packing |
| --- | --- | --- |
| 1 | `(0, 0)` | the square |
| 2 | `(-1/2, 0)`, `(1/2, 0)` | the 2×1 rectangle |
| 3 | `(-1/2, -5/16)`, `(1/2, -5/16)`, `(0, 11/16)` | the T |
| 4 | `(±1/2, ±1/2)` | the 2×2 block |
| 5 | `(0, 0)`, `(±1, 0)`, `(0, ±1)` | the plus |

These are `One.centers`, …, `Five.centers`, and the models `One.model`, …,
`Five.model`. For `n = 7` the optimum is not unique: between two columns of two
squares, each of the three squares of the middle column can move along it on
its own. A `Column` records their three heights:

```lean
def Seven.columnLimit : ℝ := Real.sqrt 3 - 1 / 2

structure Seven.Column where
  bottom : ℝ
  middle : ℝ
  top : ℝ
  lower : -columnLimit ≤ bottom
  gap_lower : bottom + 1 ≤ middle
  gap_upper : middle + 1 ≤ top
  upper : top ≤ columnLimit

def Seven.columnCenters (c : Column) : Fin 7 → Point :=
  ![(1, -1/2), (1, 1/2), (-1, -1/2), (-1, 1/2),
    (0, c.bottom), (0, c.middle), (0, c.top)]

def Seven.columnModel (c : Column) : Fin 7 → UnitSquare :=
  fun i => axisSquare (columnCenters c i)
```

The heights are at least 1 apart, so the three squares do not overlap, and
within `√3 - 1/2` of the disk centre, so they fit in the disk of radius `√13/2`.
`Seven.centers` and `Seven.model` (`Seven/Construction.lean`) are the column
with heights `-1, 0, 1`. `optimalPackings` collects the optimal models, and
uniqueness (`SquaresInCircles.lean`) says that every optimal packing is
congruent to one of them:

```lean
def optimalPackings : (n : ℕ) → Set (Fin n → UnitSquare)
  | 1 => {One.model}
  | 2 => {Two.model}
  | 3 => {Three.model}
  | 4 => {Four.model}
  | 5 => {Five.model}
  | 7 => Set.range Seven.columnModel
  | _ => ∅
```

Read these definitions before trusting the result. A kernel check establishes
that the proofs are valid; it cannot establish that the statements mean what
you intend.
