module

public import SquaresInCircles.Eight.Arithmetic.CoreRow

/-!
# Original-axis binding for a proof-producing row

Axes two and three exchange the endpoints and negate both signs and labels.
This adapter restores the statement to the original ordered geometric pair.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

def ArcData.reverse (a : ArcData) : ArcData :=
  {a with positive:=!a.positive,label:=a.label.neg}
def PreparedArc.reverse (a : PreparedArc) : PreparedArc := {a with data:=a.data.reverse}

@[simp] theorem ArcData.reverse_sign (a : ArcData) : a.reverse.sign = -a.sign := by
  cases h : a.positive <;> simp [reverse,sign,h]
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
  cases h : p.row.positiveHalf <;>
    simp [core,CoreRow.phi,AnglePolynomial.phi,AnglePolynomial.signQ,
      AffineTableRow.phi,AffineTableRow.sign,h]

/-- The charged inequality on the original ordered pair, from the Lagrangian bound of the
core row (whose axes 2 and 3 are reversed to 4 and 1). -/
theorem sound_of_positive {p : PreparedRow} (hp : p.core.Positive) (hlam : 0 ≤ p.row.multiplier)
    {a b A B u : ℝ} (hs : p.source.data.Contains p.source.radius a b)
    (ht : p.target.data.Contains p.target.radius A B) (hu : p.row.angle.Mem u)
    (haxis : 0≤forwardMargin p.row.axis p.source.data.sign p.target.data.sign
      a b A B (p.row.phi u)) :
    (p.row.lowerTarget : ℝ) < chargedCost p.source.data.label p.target.data.label
      p.charge a b A B (p.row.phi u) := by
  have hphi := core_phi p u
  cases ha : p.row.axis with
  | one =>
      have h1 : p.core.source = p.source := by simp [core,ha]
      have h2 : p.core.target = p.target := by simp [core,ha]
      have h3 : p.core.axis = .one := by simp [core,CoreRow.axis,ha]
      rw [ha] at haxis
      have hh := CoreRow.sound_of_positive hp hlam (a:=a) (b:=b) (A:=A) (B:=B) (u:=u)
        (by rw [h1]; exact hs) (by rw [h2]; exact ht) hu
        (by rw [h3,h1,h2,hphi]; exact haxis)
      rw [h1,h2,hphi] at hh
      exact hh
  | two =>
      have h1 : p.core.source = p.target.reverse := by simp [core,ha]
      have h2 : p.core.target = p.source.reverse := by simp [core,ha]
      have h3 : p.core.axis = .four := by simp [core,CoreRow.axis,ha]
      have hm := margin_reverse .two p.source.data.sign p.target.data.sign
        a b A B (p.row.phi u)
      rw [ha] at haxis
      have hn : 0≤forwardMargin .four (-p.target.data.sign) (-p.source.data.sign)
          A B a b (p.row.phi u) := by
        rw [← hm] at haxis
        exact haxis
      have hh := CoreRow.sound_of_positive hp hlam (a:=A) (b:=B) (A:=a) (B:=b) (u:=u)
        (by rw [h1]; exact ht) (by rw [h2]; exact hs) hu
        (by rw [h3,h1,h2,hphi]; simpa [PreparedArc.reverse] using hn)
      rw [h1,h2,hphi] at hh
      simp only [PreparedArc.reverse,ArcData.reverse_label] at hh
      rw [charge_reverse] at hh
      exact hh
  | three =>
      have h1 : p.core.source = p.target.reverse := by simp [core,ha]
      have h2 : p.core.target = p.source.reverse := by simp [core,ha]
      have h3 : p.core.axis = .one := by simp [core,CoreRow.axis,ha]
      have hm := margin_reverse .three p.source.data.sign p.target.data.sign
        a b A B (p.row.phi u)
      rw [ha] at haxis
      have hn : 0≤forwardMargin .one (-p.target.data.sign) (-p.source.data.sign)
          A B a b (p.row.phi u) := by
        rw [← hm] at haxis
        exact haxis
      have hh := CoreRow.sound_of_positive hp hlam (a:=A) (b:=B) (A:=a) (B:=b) (u:=u)
        (by rw [h1]; exact ht) (by rw [h2]; exact hs) hu
        (by rw [h3,h1,h2,hphi]; simpa [PreparedArc.reverse] using hn)
      rw [h1,h2,hphi] at hh
      simp only [PreparedArc.reverse,ArcData.reverse_label] at hh
      rw [charge_reverse] at hh
      exact hh
  | four =>
      have h1 : p.core.source = p.source := by simp [core,ha]
      have h2 : p.core.target = p.target := by simp [core,ha]
      have h3 : p.core.axis = .four := by simp [core,CoreRow.axis,ha]
      rw [ha] at haxis
      have hh := CoreRow.sound_of_positive hp hlam (a:=a) (b:=b) (A:=A) (B:=B) (u:=u)
        (by rw [h1]; exact hs) (by rw [h2]; exact ht) hu
        (by rw [h3,h1,h2,hphi]; exact haxis)
      rw [h1,h2,hphi] at hh
      exact hh

theorem sound {p : PreparedRow} (hp : p.NumericValid)
    {a b A B u : ℝ} (hs : p.source.data.Contains p.source.radius a b)
    (ht : p.target.data.Contains p.target.radius A B) (hu : p.row.angle.Mem u)
    (haxis : 0≤forwardMargin p.row.axis p.source.data.sign p.target.data.sign
      a b A B (p.row.phi u)) :
    (p.row.lowerTarget : ℝ) < chargedCost p.source.data.label p.target.data.label
      p.charge a b A B (p.row.phi u) :=
  sound_of_positive (CoreRow.lagrangian_positive hp) hp.2.2.2.2.2.2.1 hs ht hu haxis

def Matches (p : PreparedRow) (M : AffineTableMeta) : Prop :=
  p.source.data=p.row.sourceArc M ∧ p.target.data=p.row.targetArc M ∧
  p.source.radius=M.radius ∧ p.target.radius=M.radius ∧ p.charge=M.charge p.row.edge

instance (p : PreparedRow) (M : AffineTableMeta) : Decidable (p.Matches M) := by
  unfold Matches; infer_instance

/-- The row claim from the Lagrangian bound of the core row. -/
theorem claim_of_positive {p : PreparedRow} {M : AffineTableMeta}
    (hp : p.core.Positive) (hlam : 0 ≤ p.row.multiplier) (hm : p.Matches M) :
    p.row.Claim M := by
  intro a b A B u hdom haxis
  exact (by
    simpa [hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2] using
      sound_of_positive hp hlam
        (by simpa [hm.1,hm.2.2.1] using hdom.1)
        (by simpa [hm.2.1,hm.2.2.2.1] using hdom.2.1) hdom.2.2
        (by simpa [hm.1,hm.2.1] using haxis))

/-- This is the exported semantic row theorem used by complete table proofs. -/
theorem claim {p : PreparedRow} {M : AffineTableMeta}
    (hp : p.NumericValid) (hm : p.Matches M) : p.row.Claim M :=
  claim_of_positive (CoreRow.lagrangian_positive hp) hp.2.2.2.2.2.2.1 hm

end PreparedRow
end SquaresInCircles.Eight.Arithmetic
