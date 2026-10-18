module

public import SquaresInCircles.Eight.Arithmetic.AffineCoverage
public import Std.Data.HashMap.Basic

/-!
# One preparation and coverage argument for every affine table

The data contain arc labels and row multipliers, not proof terms. Root
brackets, arctangent bounds and coverage witnesses are computed here rather
than printed again for each row. Every proposal is still checked by the
existing interval, row-matching and closed-cover predicates.

This consolidates source representation; it does not turn the finite
certificate argument into an analytic proof or certify its running cost.
-/

@[expose] public section
namespace SquaresInCircles.Eight.Arithmetic.AffineCertificate

/-- Precision witnesses are implementation data, not geometric constants. -/
def rootScale : ℕ := 10 ^ 14
def angleScale : ℕ := 10 ^ 20

/-- A proposed bracket. Its correctness is checked by `NumericValid`. -/
def rootBracket (x : ℚ) : QInterval :=
  let k := Nat.sqrt ((x.num.toNat * rootScale ^ 2) / x.den)
  ⟨(k : ℚ) / rootScale, ((k + 1 : ℕ) : ℚ) / rootScale⟩

def prepareArc (Q : ℚ) (a : ArcData) : PreparedArc :=
  let p : PreparedArc := ⟨a, Q, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩⟩
  if a.side then p else
    { p with
      rootLo := rootBracket (p.discriminant a.tangent.lo)
      rootHi := rootBracket (p.discriminant a.tangent.hi)
      radiusRoot := if a.outer then rootBracket Q else ⟨0,0⟩ }

/-- Select the original ordered endpoints first. `core` performs the proved
axis reversal, so the source norm is attached to the correct signed label. -/
def prepare (M : AffineTableMeta) (r : AffineTableRow) : PreparedRow :=
  let p : PreparedRow :=
    ⟨r, prepareArc M.radius (r.sourceArc M),
      prepareArc M.radius (r.targetArc M), M.charge r.edge, ⟨0,0⟩⟩
  let c := p.core
  let sign : ℚ := if c.source.data.positive then 1 else -1
  let x := c.source.data.label.p - if c.axisFour then c.multiplier else 0
  let y := c.source.data.label.q - if c.axisFour then 0 else c.multiplier * sign
  { p with sourceNormRoot := rootBracket (x ^ 2 + y ^ 2) }

/-- Finite data checks remain ordinary propositions, not imported verdicts. -/
def RowsValid (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  Every (fun r => (prepare M r).NumericValid ∧ (prepare M r).Matches M ∧ r.Structural M) rows

instance (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (RowsValid M rows) := by unfold RowsValid; infer_instance

noncomputable section

theorem row_claims {M : AffineTableMeta} {rows : List AffineTableRow}
    (hv : RowsValid M rows) : ∀ r ∈ rows, r.Claim M := by
  intro r hr
  have h := Every.of_mem hv hr
  exact PreparedRow.claim (p := prepare M r) h.1 h.2.1

theorem rows_structural {M : AffineTableMeta} {rows : List AffineTableRow}
    (hv : RowsValid M rows) : ∀ r ∈ rows, r.Structural M := by
  intro r hr
  exact (Every.of_mem hv hr).2.2

end

private def floorRat (x : ℚ) : ℤ := x.num / (x.den : ℤ)
private def roundDown (x : ℚ) : ℚ :=
  (floorRat (x * angleScale) : ℚ) / angleScale
private def roundUp (x : ℚ) : ℚ := -roundDown (-x)

/-- Reuse the single arctangent-expression definition and round outwards. -/
def endpoint (x : ℚ) : ArctanEndpoint :=
  let a : ArctanEndpoint := ⟨x, rootBracket (1 + x ^ 2), ⟨0,0⟩⟩
  { a with output :=
      ⟨roundDown (a.lowerExpr.range closedBoxes).lo,
       roundUp (a.upperExpr.range closedBoxes).hi⟩ }

abbrev IndexedInterval := ℕ × QInterval

private def ordered (a b : IndexedInterval) : Bool :=
  decide (a.2.lo < b.2.lo ∨ (a.2.lo = b.2.lo ∧ a.2.hi ≤ b.2.hi))

/-- A proposal for a closed chain. A missing or insufficient interval is not
silently accepted: `AffineCover.NumericValid` checks the resulting chain. -/
def chain (goal : QInterval) : List IndexedInterval → List ℕ
  | [] => []
  | (i,I) :: rest =>
      if goal.hi < goal.lo then []
      else if I.hi < goal.lo then chain goal rest
      else i :: (if goal.hi ≤ I.hi then [] else chain ⟨max goal.lo I.hi, goal.hi⟩ rest)

private def indexKey (n s t : ℕ) (axis : ForwardAxis) (positive : Bool) : ℕ :=
  (((s * n + t) * 4 + axis.index.val) * 2) + if positive then 1 else 0

/-- One index construction replaces the repeated lists of row identifiers. -/
def indexRows (n : ℕ) (rows : List AffineTableRow) : Std.HashMap ℕ (List IndexedInterval) :=
  ((rows.foldl (fun (state : ℕ × Std.HashMap ℕ (List IndexedInterval)) r =>
    let key := indexKey n r.source r.target r.axis r.positiveHalf
    (state.1 + 1, state.2.insert key ((state.1,r.angle) :: state.2.getD key [])))
      (0,{})).2)

/-- Labels are selected by a state cover independently of the chosen axis. -/
def stateChains (M : AffineTableMeta) : StateChains :=
  fun role outer =>
    let arcs := ((List.range M.arcs.length).filterMap fun i =>
      let a := arcAt M i
      if a.role = role ∧ a.outer = outer then some (i,a.signedInterval) else none)
    chain (M.cuts role) (arcs.mergeSort ordered)

/-- All four original axes and both signed angular halves remain in scope.
No row is accepted merely because it occurred in a source report. -/
def cover (M : AffineTableMeta) (rows : List AffineTableRow) : AffineCover :=
  let base : AffineCover :=
    { endpoints := M.arcs.map (fun a => (endpoint a.tangent.lo, endpoint a.tangent.hi))
      states := stateChains M
      angleRows := fun _ _ _ _ => [] }
  let index := indexRows M.arcs.length rows
  { base with angleRows := fun s t axis positive =>
      let key := indexKey M.arcs.length s t axis positive
      chain (base.required M s t positive) ((index.getD key []).mergeSort ordered) }

end SquaresInCircles.Eight.Arithmetic.AffineCertificate
