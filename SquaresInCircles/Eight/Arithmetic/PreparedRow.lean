module

public import SquaresInCircles.Eight.Arithmetic.CoreRow

/-!
# Original-axis binding for a proof-producing row

Axes two and three exchange the endpoints and negate both signs and labels.
This adapter restores the statement to the original ordered geometric pair.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic

def ArcData.reverse (a : ArcData) : ArcData :=
  {a with positive:=!a.positive,label:=a.label.neg}
def PreparedArc.reverse (a : PreparedArc) : PreparedArc := {a with data:=a.data.reverse}

@[simp] theorem ArcData.reverse_sign (a : ArcData) : a.reverse.sign = -a.sign := by
  cases a.positive <;> simp [reverse,sign]
@[simp] theorem ArcData.reverse_label (a : ArcData) : a.reverse.label=a.label.neg := rfl
@[simp] theorem ArcData.reverse_contains (a : ArcData) (Q x y : ℝ) :
    a.reverse.Contains Q x y ↔ a.Contains Q x y := Iff.rfl

structure PreparedRow where
  row : AffineTableRow
  source : PreparedArc
  target : PreparedArc
  charge : ℚ
  sourceNormRoot : QInterval
  deriving DecidableEq, Repr

namespace PreparedRow

def core (p : PreparedRow) : CoreRow :=
  let reversed := p.row.axis=.two ∨ p.row.axis=.three
  { source := if reversed then p.target.reverse else p.source
    target := if reversed then p.source.reverse else p.target
    axisFour := decide (p.row.axis=.two ∨ p.row.axis=.four)
    quarter := p.row.quarter
    positiveHalf := p.row.positiveHalf
    angle := p.row.angle
    multiplier := p.row.multiplier
    charge := p.charge
    lowerTarget := p.row.lowerTarget
    mode := p.row.mode
    radicalParameter := p.row.radicalParameter
    sourceNormRoot := p.sourceNormRoot }

def NumericValid (p : PreparedRow) : Prop := p.core.NumericValid
instance (p : PreparedRow) : Decidable p.NumericValid := inferInstanceAs (Decidable p.core.NumericValid)

theorem core_phi (p : PreparedRow) (u : ℝ) : p.core.phi u=p.row.phi u := by
  cases p.row.positiveHalf <;>
    simp [core,CoreRow.phi,AnglePolynomial.phi,AnglePolynomial.signQ,
      AffineTableRow.phi,AffineTableRow.sign]

theorem sound {p : PreparedRow} (hp : p.NumericValid)
    {a b A B u : ℝ} (hs : p.source.data.Contains p.source.radius a b)
    (ht : p.target.data.Contains p.target.radius A B) (hu : p.row.angle.Mem u)
    (haxis : 0≤forwardMargin p.row.axis p.source.data.sign p.target.data.sign
      a b A B (p.row.phi u)) :
    (p.row.lowerTarget : ℝ) < chargedCost p.source.data.label p.target.data.label
      p.charge a b A B (p.row.phi u) := by
  cases ha : p.row.axis with
  | one =>
      have hh := p.core.sound hp
        (by simpa [core,ha] using hs)
        (by simpa [core,ha] using ht) hu
        (by simpa [core,ha,CoreRow.axis,core_phi] using haxis)
      simpa [core,ha,core_phi] using hh
  | two =>
      have hm := margin_reverse .two p.source.data.sign p.target.data.sign
        a b A B (p.row.phi u)
      have hn : 0≤forwardMargin .four (-p.target.data.sign) (-p.source.data.sign)
          A B a b (p.row.phi u) := by simpa [ForwardAxis.reverse,ha] using hm.symm ▸ haxis
      have hh := p.core.sound hp
        (by simpa [core,ha,PreparedArc.reverse] using ht)
        (by simpa [core,ha,PreparedArc.reverse] using hs) hu
        (by simpa [core,ha,CoreRow.axis,PreparedArc.reverse,core_phi] using hn)
      simpa [core,ha,PreparedArc.reverse,core_phi,charge_reverse] using hh
  | three =>
      have hm := margin_reverse .three p.source.data.sign p.target.data.sign
        a b A B (p.row.phi u)
      have hn : 0≤forwardMargin .one (-p.target.data.sign) (-p.source.data.sign)
          A B a b (p.row.phi u) := by simpa [ForwardAxis.reverse,ha] using hm.symm ▸ haxis
      have hh := p.core.sound hp
        (by simpa [core,ha,PreparedArc.reverse] using ht)
        (by simpa [core,ha,PreparedArc.reverse] using hs) hu
        (by simpa [core,ha,CoreRow.axis,PreparedArc.reverse,core_phi] using hn)
      simpa [core,ha,PreparedArc.reverse,core_phi,charge_reverse] using hh
  | four =>
      have hh := p.core.sound hp
        (by simpa [core,ha] using hs)
        (by simpa [core,ha] using ht) hu
        (by simpa [core,ha,CoreRow.axis,core_phi] using haxis)
      simpa [core,ha,core_phi] using hh

def Matches (p : PreparedRow) (M : AffineTableMeta) : Prop :=
  p.source.data=p.row.sourceArc M ∧ p.target.data=p.row.targetArc M ∧
  p.source.radius=M.radius ∧ p.target.radius=M.radius ∧ p.charge=M.charge p.row.edge

instance (p : PreparedRow) (M : AffineTableMeta) : Decidable (p.Matches M) := by
  unfold Matches; infer_instance

/-- This is the exported semantic row theorem used by complete table proofs. -/
theorem claim {p : PreparedRow} {M : AffineTableMeta}
    (hp : p.NumericValid) (hm : p.Matches M) : p.row.Claim M := by
  intro a b A B u hdom haxis
  exact (by
    simpa [hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2] using
      p.sound hp
        (by simpa [hm.1,hm.2.2.1] using hdom.1)
        (by simpa [hm.2.1,hm.2.2.2.1] using hdom.2.1) hdom.2.2
        (by simpa [hm.1,hm.2.1] using haxis))

end PreparedRow
end SquaresInCircles.Eight.Arithmetic
