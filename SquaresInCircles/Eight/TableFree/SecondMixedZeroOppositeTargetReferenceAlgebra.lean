module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetCalculus

/-!
# Exact expression enclosures at the hand proof's named references

Uncompiled source draft.  The sine and cosine enclosures are alternating
Taylor bounds.  Radicals are bounded by the same proved positive-root
refinement used elsewhere in the table-free development.  Every box
retains its actual real expression in its type.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.ReferenceAlgebra
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra

def coreBox : Interval CoreAngleEndpoint.diagonal :=
  Interval.of_bounds ⟨core_diagonal_bounds.1.le,core_diagonal_bounds.2.le⟩
def outerBox : Interval outerDiagonal :=
  Interval.of_bounds ⟨ShortMixedZero.fine_diagonal_bounds.1.le,
    ShortMixedZero.fine_diagonal_bounds.2.le⟩
def sinBox (x : ℝ) (hx : 0≤x) : Interval (Real.sin x) :=
  Interval.of_bounds ⟨HighOrderTaylor.S15_le_sin hx,HighOrderTaylor.sin_le_S13 hx⟩
def cosBox (x : ℝ) (hx : 0≤x) : Interval (Real.cos x) :=
  Interval.of_bounds ⟨HighOrderTaylor.C14_le_cos hx,HighOrderTaylor.cos_le_C12 hx⟩

def diagonalBox (x : ℝ) (hx : 0≤x) : Interval (diagonal x) :=
  ((Interval.point (1/2)).add (((Interval.point (1/2)).sub coreBox).mul (cosBox x hx))).add ((coreBox.add (Interval.point (1/2))).mul (sinBox x hx))
def speedBox (x : ℝ) (hx : 0≤x) : Interval (speed x) :=
  ((coreBox.sub (Interval.point (1/2))).mul (sinBox x hx)).add ((coreBox.add (Interval.point (1/2))).mul (cosBox x hx))

def HBox (r : Row) (x : ℝ) (hx : 0≤x) (X : Interval (U (diagonal x))) : Interval (H r x) :=
  ((((Interval.point (-x)).add (Interval.point (c r))).add ((Interval.point (g r)).mul coreBox)).add (labelBox (F r) (diagonalBox x hx) X))
def H₁Box (r : Row) (x : ℝ) (hx : 0≤x) (X : Interval (U (diagonal x)))
    (hX : 0<X.lo) : Interval (H₁ r x) :=
  (Interval.point (-1)).add ((firstBox (F r) (diagonalBox x hx) X hX).mul (speedBox x hx))
def H₂Box (r : Row) (x : ℝ) (hx : 0≤x) (X : Interval (U (diagonal x)))
    (hX : 0<X.lo) : Interval (H₂ r x) :=
  ((secondBox (F r) (diagonalBox x hx) X hX).mul (speedBox x hx).square).add ((firstBox (F r) (diagonalBox x hx) X hX).mul ((Interval.point (1/2)).sub (diagonalBox x hx)))

def ratioDDDBox {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (ratioDDD y) := by
  let V := Y.add (Interval.point (1/2))
  let N := (Interval.point (3*Q0)).mul (X.square.add ((Interval.point 5).mul V.square))
  let D := X.cube.mul (X.square.mul X.square)
  have hD : 0<D.lo := Interval.mul_lo_pos (Interval.cube_lo_pos hX)
    (Interval.mul_lo_pos (Interval.square_lo_pos hX) (Interval.square_lo_pos hX))
  convert N.div D hD using 1
  dsimp [ratioDDD,U,N,D,V]
  congr 1
  ring

def fourthBox (L : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    Interval (L.d4 y) :=
  (((Interval.point (-4*L.s)).mul (ratioDDBox Y X hX)).sub
    (((Interval.point L.p).add ((Interval.point L.s).mul Y)).mul (ratioDDDBox Y X hX)))

def inverseBox {a B x : ℝ} (A : Interval a) (Y : Interval B) (S : Interval (Real.sin x))
    (C : Interval (Real.cos x)) (hC : 0<C.lo) : Interval (inverse a B x) :=
  ((Interval.point (1/2)).add (((Interval.point (1/2)).sub Y).div C hC)).add (((A.add (Interval.point (1/2))).mul S).div C hC)

def outerLabelBox (r : Row) : Interval ((F r).outer outerDiagonal) := by
  have he : U outerDiagonal=outerDiagonal+1/2 := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
  let X : Interval (U outerDiagonal) := by rw [he]; exact outerBox.add (Interval.point (1/2))
  exact labelBox (F r) outerBox X

def boundaryBox (r : Row) {a x : ℝ} (A : Interval a) (hx : 0≤x)
    (hC : 0<(cosBox x hx).lo) : Interval (boundary r a outerDiagonal x) :=
  ((((Interval.point (-x)).add (Interval.point (c r))).add
    ((Interval.point (g r)).mul (inverseBox A outerBox (sinBox x hx) (cosBox x hx) hC))).add (outerLabelBox r))

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.ReferenceAlgebra
