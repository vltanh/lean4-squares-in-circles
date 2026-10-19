module

public import SquaresInCircles.Eight.Arithmetic.AffineArc
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Eight squares: the data and the claims of an affine table

An affine table at a level `Q` bounds the charged costs of the edges of the boundary cycles at
that level. Its data (`AffineTableMeta`) are exact rationals: the arcs, the cuts of the signed
tangents, and for each edge the quarter of the word, the charge, the target, the range of the
frame difference and the allowed axes. An arc (`ArcData`) has a role (a vertex of the cycle), a
curve, a sign `σ`, an interval of the tangent `b / a` and an affine label. The curve is the outer
circle `(a + 1/2)² + (b + 1/2)² = Q` or the core curve, which is its side `a = 7/12` up to the
tangent `6/7` and its corner circle `(a - 1/2)² + (b - 1/2)² = (1/12)²` beyond;
`ArcData.Contains` says that a state lies on the arc.

A row (`AffineTableRow`) names an edge, a source and a target arc, a forward axis, a quarter `k`,
a half (a sign), an interval of `u`, a multiplier `λ` and a lower target. Its claim
(`AffineTableRow.Claim`) is that for every source state, every target state and every `u` in the
interval, at the angle `φ = k π / 2 ± u` between the frames, the charged cost of the edge exceeds
the lower target wherever the margin of the axis is nonnegative. `RowCheck.lean` proves the claims
of the rows, and `AffineCoverage.lean` assembles them into the charged bound of the cycles.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

/-- An arc of a table: its identifier in the generator's data, its role, its curve (outer or
core), its sign (`positive`), its interval of the tangent `b / a` and its affine label. -/
structure ArcData where
  sourceId : ℕ
  role : Fin 7
  outer : Bool
  positive : Bool
  tangent : QInterval
  label : AffineLabel

instance : Inhabited ArcData := ⟨⟨0,0,false,false,⟨0,0⟩,⟨0,0,0⟩⟩⟩

/-- The sign `σ = ±1` of the arc. -/
def ArcData.sign (a : ArcData) : ℝ := if a.positive then 1 else -1

/-- The state `(a, b)` lies on the curve of the arc: the outer circle of the level `Q`, the core
side for an arc with tangents up to `6/7`, or the core corner. -/
def ArcData.OnCurve (s : ArcData) (Q a b : ℝ) : Prop :=
  if s.outer then (a+1/2)^2+(b+1/2)^2=Q
  else if s.tangent.hi ≤ 6/7 then a=7/12 ∧ b ≤ 1/2
  else 1/2 ≤ b ∧ (a-1/2)^2+(b-1/2)^2=(1/12 : ℝ)^2

/-- The state `(a, b)` lies on the arc: `0 ≤ b ≤ a` with `a > 0`, the tangent `b / a` in the
interval of the arc, and the state on its curve. -/
def ArcData.Contains (s : ArcData) (Q a b : ℝ) : Prop :=
  0 < a ∧ 0 ≤ b ∧ b ≤ a ∧ s.tangent.Mem (b/a) ∧ s.OnCurve Q a b

/-- The exact data of an affine table: the level `Q` (`radius`), the arcs, the interval of the
signed tangent of each vertex (`cuts`), and for each edge the quarter of the word, the charge, the
target, the range of the frame difference and the allowed axes. -/
structure AffineTableMeta where
  radius : ℚ
  arcs : List ArcData
  cuts : Fin 7 → QInterval
  word : Fin 7 → ℕ
  charge : Fin 7 → ℚ
  target : Fin 7 → ℚ
  differenceRange : Fin 7 → QInterval
  allowedAxes : Fin 7 → List ForwardAxis

/-- A row of an affine table: its edge, the indices of its source and target arcs, its axis, the
quarter `k`, the half (`positiveHalf`), the interval of `u`, the multiplier `λ` and the lower
target. -/
structure AffineTableRow where
  edge : Fin 7
  source : ℕ
  target : ℕ
  axis : ForwardAxis
  quarter : ℕ
  positiveHalf : Bool
  angle : QInterval
  multiplier : ℚ
  lowerTarget : ℚ

def AffineTableRow.sign (r : AffineTableRow) : ℝ := if r.positiveHalf then 1 else -1
/-- The angle `φ = k π / 2 ± u` of the row, with the sign of its half. -/
def AffineTableRow.phi (r : AffineTableRow) (u : ℝ) : ℝ :=
  (r.quarter : ℝ)*Real.pi/2+r.sign*u
/-- The source arc of the row (a default arc for an index out of range); `targetArc` is its
target arc. -/
def AffineTableRow.sourceArc (M : AffineTableMeta) (r : AffineTableRow) : ArcData :=
  M.arcs.getD r.source default
def AffineTableRow.targetArc (M : AffineTableMeta) (r : AffineTableRow) : ArcData :=
  M.arcs.getD r.target default

/-- The domain of the claim of a row: the source state on the source arc, the target state on
the target arc, and `u` in the angle interval. -/
def AffineTableRow.Domain (M : AffineTableMeta) (r : AffineTableRow)
    (a b A B u : ℝ) : Prop :=
  (r.sourceArc M).Contains M.radius a b ∧
  (r.targetArc M).Contains M.radius A B ∧ r.angle.Mem u

/-- The claim of a row: on its domain, wherever the margin of its axis is nonnegative, the
charged cost of its edge exceeds the lower target. -/
def AffineTableRow.Claim (M : AffineTableMeta) (r : AffineTableRow) : Prop :=
  ∀ a b A B u : ℝ, r.Domain M a b A B u →
    0 ≤ forwardMargin r.axis (r.sourceArc M).sign (r.targetArc M).sign a b A B (r.phi u) →
    (r.lowerTarget : ℝ) < chargedCost (r.sourceArc M).label (r.targetArc M).label
      (M.charge r.edge) a b A B (r.phi u)

end SquaresInCircles.Eight.Arithmetic
