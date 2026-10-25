module

public import SquaresInCircles.Eight.Words.Crossed.GAOutput

/-!
# Eight squares: reflecting an actual GA output back to the original BT side

Reflection is used on the local three-point
output only.  The resulting data fixes the original B tangent, records
its original strict circle deficit, and supplies literal BT2 and TD2
contacts.  In particular no assertion about a reflected E sign is used.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight

structure CrossedBTData (q : ℝ) (B T D : SignedPoint) (r z : ℝ) where
  pointT : SignedPoint
  pointB : SignedPoint
  T_sorted : pointT.Sorted
  T_avoids : pointT.AvoidsCore
  T_contained : pointT.Contained q
  T_nonneg : 0≤pointT.y
  B_sorted : pointB.Sorted
  B_avoids : pointB.AvoidsCore
  B_contained : pointB.Contained q
  B_tangent : pointB.y=B.y
  TD_two : zeroFeasible pointT D r 2
  BT_hard : quarterFeasible pointB pointT 0 2
  B_strict : 0<z → pointB.circle<q
  B_loss : B.circle<q → pointB.circle<q

structure CrossedBTOutput (q : ℝ) (B T D : SignedPoint) (r z : ℝ)
    extends CrossedBTData q B T D r z where
  at_zero : z=0 → pointT=T ∧ pointB=B

def CrossedGAData.reflectBT {q r z : ℝ} {B T D : SignedPoint}
    (O : CrossedGAData q D.reflect T.reflect B.reflect r z) :
    CrossedBTData q B T D r z where
  pointT := O.pointG.reflect
  pointB := O.pointA.reflect
  T_sorted := by simpa using O.G_sorted
  T_avoids := by simpa using O.G_avoids
  T_contained := by simpa using O.G_contained
  T_nonneg := by dsimp [SignedPoint.reflect]; linarith [O.G_nonpos]
  B_sorted := by simpa using O.A_sorted
  B_avoids := by simpa using O.A_avoids
  B_contained := by simpa using O.A_contained
  B_tangent := by
    have hy := O.A_tangent
    change O.pointA.y= -B.y at hy
    change -O.pointA.y=B.y
    linarith
  TD_two := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG r 0).2 O.HG_zero
  BT_hard := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointG O.pointA 0 0).2 O.GA_hard
  B_strict := fun h => by simpa using O.A_strict h
  B_loss := by
    intro h
    simpa using O.A_loss (by simpa using h)

def CrossedGAOutput.reflectBT {q r z : ℝ} {B T D : SignedPoint}
    (O : CrossedGAOutput q D.reflect T.reflect B.reflect r z) :
    CrossedBTOutput q B T D r z where
  toCrossedBTData := O.toCrossedGAData.reflectBT
  at_zero := by
    intro hz
    obtain ⟨hG,hA⟩ := O.at_zero hz
    constructor <;> simp [CrossedGAData.reflectBT,hG,hA]

end SquaresInCircles.Eight
