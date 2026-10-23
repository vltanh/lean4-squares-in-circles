module

public import SquaresInCircles.Eight.Arithmetic.AffineArc
public import SquaresInCircles.Eight.Arithmetic.IntervalPolynomial

/-!
# Embedded affine table schema and real row meaning

The generated data records contain every original arc, row, axis domain,
angle range, multiplier, and charged edge target. `Structural` is deliberately
separate from `Claim`: well-formed finite data is not a continuous proof.
The latter is discharged by the scalar, interval-polynomial, Bernstein, and
arc-support kernels in their respective generated proof modules.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic

inductive SupportMode | lower | upper | endpoints | circle
  deriving DecidableEq, Repr

structure ArcData where
  sourceId : ℕ
  role : Fin 7
  outer : Bool
  positive : Bool
  tangent : QInterval
  label : AffineLabel
  deriving DecidableEq, Repr

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
  mode : SupportMode
  radicalParameter : ℚ
  lowerTarget : ℚ
  deriving DecidableEq, Repr

def AffineTableRow.sign (r : AffineTableRow) : ℝ := if r.positiveHalf then 1 else -1
def AffineTableRow.phi (r : AffineTableRow) (u : ℝ) : ℝ :=
  (r.quarter : ℝ)*Real.pi/2+r.sign*u
def AffineTableRow.sourceArc (M : AffineTableMeta) (r : AffineTableRow) : ArcData :=
  M.arcs.getD r.source default
def AffineTableRow.targetArc (M : AffineTableMeta) (r : AffineTableRow) : ArcData :=
  M.arcs.getD r.target default

def AffineTableRow.Structural (M : AffineTableMeta) (r : AffineTableRow) : Prop :=
  r.source < M.arcs.length ∧ r.target < M.arcs.length ∧
  (r.sourceArc M).role = r.edge ∧ (r.targetArc M).role = r.edge+1 ∧
  r.quarter = M.word r.edge ∧ 0 ≤ r.angle.lo ∧ r.angle.lo ≤ r.angle.hi ∧
  0 ≤ r.multiplier ∧ M.target r.edge ≤ r.lowerTarget ∧
  (r.mode = .circle → 0 < r.radicalParameter)

instance (M : AffineTableMeta) (r : AffineTableRow) : Decidable (r.Structural M) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

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

theorem AffineTableRow.Claim.actual {M : AffineTableMeta} {r : AffineTableRow}
    (hr : r.Claim M) {a b A B u : ℝ} (hdom : r.Domain M a b A B u)
    (haxis : (forwardAxis r.axis.index).Feasible
      (localSource a b (r.sourceArc M).sign)
      (localTarget A B (r.targetArc M).sign (r.phi u))) :
    (r.lowerTarget : ℝ) < chargedCost (r.sourceArc M).label (r.targetArc M).label
      (M.charge r.edge) a b A B (r.phi u) :=
  hr a b A B u hdom ((actual_axis_iff_margin _ _ _ _ _ _ _ _).mp haxis)

/-- Coverage and row soundness remain independent obligations. The labels on
both sides are selected once before this implication is applied. -/
theorem affine_table_covered {M : AffineTableMeta} {rows : List AffineTableRow}
    (hrows : ∀ r ∈ rows, r.Claim M) {edge : Fin 7} {Ls Lt : AffineLabel}
    {axis : ForwardAxis} {σ τ a b A B φ : ℝ}
    (hcover : ∃ r ∈ rows, ∃ u : ℝ,
      r.edge=edge ∧ r.axis=axis ∧ (r.sourceArc M).label=Ls ∧ (r.targetArc M).label=Lt ∧
      (r.sourceArc M).sign=σ ∧ (r.targetArc M).sign=τ ∧ r.phi u=φ ∧
      r.Domain M a b A B u ∧ M.target edge ≤ r.lowerTarget)
    (haxis : 0 ≤ forwardMargin axis σ τ a b A B φ) :
    (M.target edge : ℝ) < chargedCost Ls Lt (M.charge edge) a b A B φ := by
  obtain ⟨r,hr,u,he,ha,hs,ht,hσ,hτ,hφ,hdom,hγ⟩ := hcover
  have h := hrows r hr a b A B u hdom
    (by simpa [ha,hσ,hτ,hφ] using haxis)
  have htarget : (M.target edge : ℝ) ≤ r.lowerTarget := by exact_mod_cast hγ
  simpa [he,hs,ht,hφ] using htarget.trans_lt h

end SquaresInCircles.Eight.Arithmetic
