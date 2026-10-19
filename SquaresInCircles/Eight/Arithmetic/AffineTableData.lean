module

public import SquaresInCircles.Eight.Arithmetic.AffineArc
public import SquaresInCircles.Eight.Arithmetic.Bernstein
public import SquaresInCircles.Eight.Arithmetic.ScalarExpr
public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Embedded affine table schema and real row meaning

The generated data records contain every original arc, row, axis domain,
angle range, multiplier, and charged edge target. A row means the continuous
proposition `Claim` on the product of its two arcs and its angle interval; the
row check of `RowCheck` proves it.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

structure ArcData where
  sourceId : ℕ
  role : Fin 7
  outer : Bool
  positive : Bool
  tangent : QInterval
  label : AffineLabel

instance : Inhabited ArcData := ⟨⟨0,0,false,false,⟨0,0⟩,⟨0,0,0⟩⟩⟩

def ArcData.sign (a : ArcData) : ℝ := if a.positive then 1 else -1

def ArcData.OnCurve (s : ArcData) (Q a b : ℝ) : Prop :=
  if s.outer then (a+1/2)^2+(b+1/2)^2=Q
  else if s.tangent.hi ≤ 6/7 then a=7/12 ∧ b ≤ 1/2
  else 1/2 ≤ b ∧ (a-1/2)^2+(b-1/2)^2=(1/12 : ℝ)^2

def ArcData.Contains (s : ArcData) (Q a b : ℝ) : Prop :=
  0 < a ∧ 0 ≤ b ∧ b ≤ a ∧ s.tangent.Mem (b/a) ∧ s.OnCurve Q a b

structure AffineTableMeta where
  radius : ℚ
  arcs : List ArcData
  cuts : Fin 7 → QInterval
  word : Fin 7 → ℕ
  charge : Fin 7 → ℚ
  target : Fin 7 → ℚ
  differenceRange : Fin 7 → QInterval
  allowedAxes : Fin 7 → List ForwardAxis

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
def AffineTableRow.phi (r : AffineTableRow) (u : ℝ) : ℝ :=
  (r.quarter : ℝ)*Real.pi/2+r.sign*u
def AffineTableRow.sourceArc (M : AffineTableMeta) (r : AffineTableRow) : ArcData :=
  M.arcs.getD r.source default
def AffineTableRow.targetArc (M : AffineTableMeta) (r : AffineTableRow) : ArcData :=
  M.arcs.getD r.target default

def AffineTableRow.Domain (M : AffineTableMeta) (r : AffineTableRow)
    (a b A B u : ℝ) : Prop :=
  (r.sourceArc M).Contains M.radius a b ∧
  (r.targetArc M).Contains M.radius A B ∧ r.angle.Mem u

/-- The real continuous proposition represented by an embedded row. -/
def AffineTableRow.Claim (M : AffineTableMeta) (r : AffineTableRow) : Prop :=
  ∀ a b A B u : ℝ, r.Domain M a b A B u →
    0 ≤ forwardMargin r.axis (r.sourceArc M).sign (r.targetArc M).sign a b A B (r.phi u) →
    (r.lowerTarget : ℝ) < chargedCost (r.sourceArc M).label (r.targetArc M).label
      (M.charge r.edge) a b A B (r.phi u)

end SquaresInCircles.Eight.Arithmetic
