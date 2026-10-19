module

public import SquaresInCircles.Eight.Arithmetic.CoreRow

/-!
# Eight squares: from a table row to its core row

A prepared row (`PreparedRow`) is a row of a table with its two prepared arcs and the charge of
its edge. Its core row (`PreparedRow.core`) keeps a row on the axis one or four as it is; on the
axes two and three it exchanges the source and the target and reverses both arcs (opposite sign,
negated label), which turns the axis two into four and three into one without changing the
margin or the charged cost (`margin_reverse`, `charge_reverse`). So the Lagrangian bound of the
core row and a nonnegative multiplier give the charged inequality of the row itself
(`sound_of_positive`), and when the arcs and the charge are those of the table (`Matches`), the
claim of the row (`claim_of_positive`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

/-- The arc with the opposite sign and the negated label. -/
def ArcData.reverse (a : ArcData) : ArcData :=
  {a with positive:=!a.positive,label:=a.label.neg}
def PreparedArc.reverse (a : PreparedArc) : PreparedArc := {a with data:=a.data.reverse}

@[simp] theorem ArcData.reverse_sign (a : ArcData) : a.reverse.sign = -a.sign := by
  cases h : a.positive <;> simp [reverse,sign,h]
@[simp] theorem ArcData.reverse_label (a : ArcData) : a.reverse.label=a.label.neg := rfl

/-- A row of a table with its prepared source and target arcs and the charge of its edge. -/
structure PreparedRow where
  row : AffineTableRow
  source : PreparedArc
  target : PreparedArc
  charge : ℚ

namespace PreparedRow

/-- The core row: on the axes one and four the row itself; on the axes two and three the row
with the source and the target exchanged and reversed, on the axes four and one. -/
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
    lowerTarget := p.row.lowerTarget }

theorem core_phi (p : PreparedRow) (u : ℝ) : p.core.phi u=p.row.phi u := by
  cases h : p.row.positiveHalf <;>
    simp [core,CoreRow.phi,AnglePolynomial.phi,AnglePolynomial.signQ,
      AffineTableRow.phi,AffineTableRow.sign,h]

/-- The charged inequality of the row from the Lagrangian bound of its core row, through the
reversal on the axes two and three. -/
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

/-- The prepared arcs are those of the row in the table, at its level, and the charge is that of
the edge. -/
def Matches (p : PreparedRow) (M : AffineTableMeta) : Prop :=
  p.source.data=p.row.sourceArc M ∧ p.target.data=p.row.targetArc M ∧
  p.source.radius=M.radius ∧ p.target.radius=M.radius ∧ p.charge=M.charge p.row.edge

/-- The claim of the row from the Lagrangian bound of its core row, for a nonnegative multiplier
and arcs and charge matching the table. -/
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

end PreparedRow
end SquaresInCircles.Eight.Arithmetic
