module

public import SquaresInCircles.Eight.Frames.Signed.Coordinates

/-!
# Eight squares: a crossed GA-alignment output

A temporary lift of the primary circle gives no nonincrease of the original circle, so
`CrossedGAData` records what the construction supplies: containment at the same q, every
inherited strict A deficit (`A_loss`), and a strict A deficit when G moves (`A_strict`).
`CrossedGAOutput` adds that at zero G motion the two original points are kept.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

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

/-- The identity at zero motion belongs to the noncanceling alignment. An HG2-to-HG0 owner
conversion may move G even when its frame is already common, and so uses `CrossedGAData`. -/
structure CrossedGAOutput (q : ℝ) (H G A : SignedPoint) (r z : ℝ)
    extends CrossedGAData q H G A r z where
  at_zero : z=0 → pointG=G ∧ pointA=A

end SquaresInCircles.Eight
