import SquaresInCircles.Six.Construction
import SquaresInCircles.Six.Containing

/-!
# Targets of the six-square formalization

These are proposition DEFINITIONS, not theorem declarations. Their unrestricted
inhabitants now live in `Six/LowerBound.lean` and `Six/Uniqueness.lean`.
`Normalization.StrongCore` supplies a proof body for `StrongCentralBox`.
Compilation and kernel acceptance of the new six-square path remain deferred.

Keeping these exact targets separate prevents a conditional normalization
lemma, a generic stress implication, or the attaining example from being
mistaken for the unrestricted theorem. Do not import StrongCore here: it uses
the goal definition below, so that would create an import cycle.
-/

noncomputable section
namespace SquaresInCircles.Six.Goals

/-- The unrestricted lower-bound target, using the original packing predicate. -/
def LowerBound : Prop :=
  ∀ (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ),
    Packing S o R → Six.radius ≤ R

/-- The unrestricted equality-classification target. -/
def Uniqueness : Prop :=
  ∀ (S : Fin 6 → UnitSquare) (o : Point),
    Packing S o Six.radius → Congruent S o Six.model

/-- Proposition A in a frame where square 0 is the central square.
There are deliberately no pin, sector, canonical-bit, or A2 hypotheses. -/
def StrongCentralBox : Prop :=
  ∀ (S : Fin 6 → UnitSquare) (c : Point) (R : ℝ),
    Packing S (0, 0) R → R ^ 2 ≤ Six.qStar →
    S 0 = axisSquare c → openSquare (S 0) (0, 0) →
    0 ≤ c.1 → 0 ≤ c.2 →
    c.1 ≤ Normalization.c0 ∧ c.2 ≤ Normalization.c0

end SquaresInCircles.Six.Goals
