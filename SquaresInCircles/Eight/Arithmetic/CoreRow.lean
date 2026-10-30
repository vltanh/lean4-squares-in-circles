module

public import SquaresInCircles.Eight.Arithmetic.AnglePolynomial

/-!
# Eight squares: core rows

A core row (`CoreRow`) is a row on the axis one or four (`axisFour`), with two prepared arcs. On
these two axes the coefficients of the source state in the charged cost less `λ` times the margin
do not depend on the angle: they are the rationals `Xs` and `Ys` (`source_coefficients`). The
Lagrangian bound of a core row (`CoreRow.Positive`) is that the constant term and the two linear
functions of the states together exceed the lower target, for all states of both arcs and all `u`
in the angle interval. With a nonnegative multiplier it gives the charged inequality wherever the
margin of the axis is nonnegative (`sound_of_positive`), by `lagrangian_identity`.

`PreparedRow.lean` reduces every row of a table to a core row, and `RowCheck.lean` proves the
Lagrangian bound of a core row by a fixed-point computation (`coreCheck_positive`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic

/-- The sign of the arc, as a rational. -/
def ArcData.signQ (a : ArcData) : ℚ := if a.positive then 1 else -1
theorem ArcData.signQ_cast (a : ArcData) : (a.signQ : ℝ)=a.sign := by
  cases h : a.positive <;> simp [signQ,sign,h]

/-- A row on the axis four (`axisFour`) or one, with prepared source and target arcs, the quarter
and the half of its angle, the angle interval, the multiplier, the charge of its edge and the
lower target. -/
structure CoreRow where
  source : PreparedArc
  target : PreparedArc
  axisFour : Bool
  quarter : ℕ
  positiveHalf : Bool
  angle : QInterval
  multiplier : ℚ
  charge : ℚ
  lowerTarget : ℚ

namespace CoreRow
open AnglePolynomial

def axis (r : CoreRow) : ForwardAxis := if r.axisFour then .four else .one
def phi (r : CoreRow) (u : ℝ) : ℝ := AnglePolynomial.phi r.quarter r.positiveHalf u
/-- The coefficient of `a` in the Lagrangian of a core row: `p - λ` on the axis four, `p` on the
axis one; `Ys` is that of `b`, `q` on the axis four and `q - λ σ` on the axis one. -/
def Xs (r : CoreRow) : ℚ :=
  if r.axisFour then r.source.data.label.p-r.multiplier else r.source.data.label.p
def Ys (r : CoreRow) : ℚ :=
  if r.axisFour then r.source.data.label.q
  else r.source.data.label.q-r.multiplier*r.source.data.signQ

/-- The coefficients of the source state are `Xs` and `Ys` at every angle. -/
theorem source_coefficients (r : CoreRow) (u : ℝ) :
    (r.Xs : ℝ)=sourceX r.axis r.source.data.label r.multiplier (r.phi u) ∧
    (r.Ys : ℝ)=sourceY r.axis r.source.data.label r.multiplier r.source.data.sign (r.phi u) := by
  cases h : r.axisFour <;>
    simp [Xs,Ys,axis,sourceX,sourceY,ArcData.signQ_cast,h]

/-- The strict Lagrangian bound of a core row: the constant term and the linear functions of the
two states exceed the lower target, for all states of both arcs and all `u` in the angle
interval. -/
def Positive (r : CoreRow) : Prop :=
  ∀ a b A B u : ℝ, r.source.data.Contains r.source.radius a b →
    r.target.data.Contains r.target.radius A B → r.angle.Mem u →
    (r.lowerTarget : ℝ) <
      lagrangianBase r.source.data.label r.target.data.label r.multiplier r.charge (r.phi u)+
      sourceX r.axis r.source.data.label r.multiplier (r.phi u)*a+
      sourceY r.axis r.source.data.label r.multiplier r.source.data.sign (r.phi u)*b+
      targetX r.axis r.target.data.label r.multiplier (r.phi u)*A+
      targetY r.axis r.target.data.label r.multiplier r.target.data.sign (r.phi u)*B

/-- The Lagrangian bound and a nonnegative multiplier give the charged inequality wherever
the forward margin is nonnegative. -/
theorem sound_of_positive {r : CoreRow} (hr : r.Positive) (hlam : 0 ≤ r.multiplier)
    {a b A B u : ℝ} (hsarc : r.source.data.Contains r.source.radius a b)
    (htarc : r.target.data.Contains r.target.radius A B) (hu : r.angle.Mem u)
    (haxis : 0≤forwardMargin r.axis r.source.data.sign r.target.data.sign a b A B (r.phi u)) :
    (r.lowerTarget : ℝ) < chargedCost r.source.data.label r.target.data.label
      r.charge a b A B (r.phi u) := by
  have hp := hr a b A B u hsarc htarc hu
  have hid := lagrangian_identity r.axis r.source.data.label r.target.data.label
    r.multiplier r.charge r.source.data.sign r.target.data.sign a b A B (r.phi u)
  have hlam' : (0:ℝ)≤r.multiplier := by exact_mod_cast hlam
  have hn := mul_nonneg hlam' haxis
  linarith

end CoreRow
end SquaresInCircles.Eight.Arithmetic
