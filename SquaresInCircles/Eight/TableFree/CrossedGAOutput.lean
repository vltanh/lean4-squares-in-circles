module

public import SquaresInCircles.Eight.TableFree.HardCancelingOuterCycle

/-!
# An actual crossed GA-alignment output

Uncompiled source draft.  A temporary primary-circle lift does not
justify an original-circle nonincrease assertion.  The output records
the facts the construction actually supplies: containment at the same
q, every inherited strict A deficit, and a strict A deficit when G moves.
At zero G motion the original two points are retained literally.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree

structure CrossedGAData (q : ℝ) (H G A : SignedPoint) (r z : ℝ) where
  pointG : SignedPoint
  pointA : SignedPoint
  G_sorted : pointG.Sorted
  G_avoids : pointG.AvoidsCore
  G_contained : pointG.Contained q
  G_nonpos : pointG.y≤0
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_contained : pointA.Contained q
  A_tangent : pointA.y=A.y
  HG_zero : zeroFeasible H pointG r 0
  GA_hard : quarterFeasible pointG pointA 0 0
  A_strict : 0<z → pointA.circle<q
  A_loss : A.circle<q → pointA.circle<q

/-- The identity at zero motion belongs to the noncanceling alignment.
An HG2-to-HG0 owner conversion may still replace G when its frame is
already common, and therefore uses the base geometric data instead. -/
structure CrossedGAOutput (q : ℝ) (H G A : SignedPoint) (r z : ℝ)
    extends CrossedGAData q H G A r z where
  at_zero : z=0 → pointG=G ∧ pointA=A

end SquaresInCircles.Eight.TableFree
