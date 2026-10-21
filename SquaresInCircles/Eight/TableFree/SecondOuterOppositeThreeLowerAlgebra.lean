module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerContact
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra

/-!
# Arithmetic transport for lower inverse formulas

Each enclosure carries a proof about its actual radical expression.
The operations below are used at named references or on one complete
analytic regime; there is no coordinate cover or sampled input.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerAlgebra
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open StationaryPrimitives (Interval)
open ReferenceAlgebra
open LowerInverse (q factor factorD factorDD)

def qBox {u : ℝ} (U : Interval u) : Interval (q u) :=
  (Interval.point (Q0+1)).sub ((Interval.point 2).mul U)

def factorBox {u : ℝ} (U : Interval u) (Q : Interval (q u))
    (hU : 0<U.lo) (hQ : 0<Q.lo) : Interval (factor u) :=
  ((Interval.point Q0).sub U).div (U.mul Q) (Interval.mul_lo_pos hU hQ)

def factorDBox {u : ℝ} (U : Interval u) (Q : Interval (q u))
    (hU : 0<U.lo) (hQ : 0<Q.lo) : Interval (factorD u) := by
  let N := (((Interval.point (4*Q0)).mul U).sub
    ((Interval.point 2).mul U.square)).sub (Interval.point (Q0*(Q0+1)))
  exact N.div (U.square.mul Q.square)
    (Interval.mul_lo_pos (Interval.square_lo_pos hU) (Interval.square_lo_pos hQ))

def factorDDBox {u : ℝ} (U : Interval u) (Q : Interval (q u))
    (hU : 0<U.lo) (hQ : 0<Q.lo) : Interval (factorDD u) := by
  let C := Interval.point (Q0+1)
  have hC : 0<C.lo := by norm_num [C,Interval.point,Q0]
  exact ((Interval.point (2*Q0)).div (C.mul U.cube)
    (Interval.mul_lo_pos hC (Interval.cube_lo_pos hU))).add
      ((Interval.point (8*(Q0-1))).div (C.mul Q.cube)
        (Interval.mul_lo_pos hC (Interval.cube_lo_pos hQ)))

def A1Box {y : ℝ} (R : Interval (ratio y)) (D : Interval (ratioD y))
    (DD : Interval (ratioDD y)) (Q : Interval (q (U y))) (hQ : 0<Q.lo) :
    Interval (LowerInverse.A1 y) := by
  let Z := ((((Interval.point 9).mul R).mul D).div Q.square (Interval.square_lo_pos hQ)).sub
    (((Interval.point 15).mul R.cube).div Q.cube (Interval.cube_lo_pos hQ))
  exact Z.sub (DD.div Q hQ)

def A3Box {y : ℝ} (R : Interval (ratio y)) (D : Interval (ratioD y))
    (Q : Interval (q (U y))) (hQ : 0<Q.lo) : Interval (LowerInverse.A3 y) :=
  ((((Interval.point 3).mul R).mul D).div Q.square (Interval.square_lo_pos hQ)).sub
    (((Interval.point 10).mul R.cube).div Q.cube (Interval.cube_lo_pos hQ))

def speedBox {z y : ℝ} (Z : Interval z) (Q : Interval (q (U y)))
    (s : ℝ) (hs : 0<s) (hr : 0≤(Q.sub Z.square).lo) : Interval (LowerInverse.speed z y) :=
  rootThree (Q.sub Z.square) s hs hr

def inverseFirstBox {z y : ℝ} (Z : Interval z) (X : Interval (U y))
    (R : Interval (ratio y)) (Q : Interval (q (U y)))
    (V : Interval (LowerInverse.speed z y))
    (hX : 0<X.lo) (hQ : 0<Q.lo) (hV : 0<V.lo) : Interval (LowerInverse.first z y) :=
  (factorBox X Q hX hQ).sub ((Z.mul R).div (Q.mul V) (Interval.mul_lo_pos hQ hV))

def inverseSecondBox {z y : ℝ} (Z : Interval z) (X : Interval (U y))
    (R : Interval (ratio y)) (D : Interval (ratioD y)) (Q : Interval (q (U y)))
    (V : Interval (LowerInverse.speed z y))
    (hX : 0<X.lo) (hQ : 0<Q.lo) (hV : 0<V.lo) : Interval (LowerInverse.second z y) := by
  let C := (D.sub (((Interval.point 2).mul R.square).div Q hQ)).sub
    (R.square.div V.square (Interval.square_lo_pos hV))
  exact ((R.mul (factorDBox X Q hX hQ)).neg).sub
    ((Z.div (Q.mul V) (Interval.mul_lo_pos hQ hV)).mul C)

def freeFirstBox (reverse : Bool) {b B : ℝ} (Y : Interval b) (X : Interval (U b))
    (V : Interval (LowerInverse.speed (b+1/2) B)) (hX : 0<X.lo) (hV : 0<V.lo) :
    Interval (LowerContact.freeFirst reverse b B) :=
  ((Interval.point 1).div V hV).sub (ReferenceAlgebra.firstBox (LowerContact.inner reverse) Y X hX)

def outerFirstBox (reverse : Bool) {b B : ℝ}
    (Z : Interval (b+1/2)) (Y : Interval B) (X : Interval (U B))
    (V : Interval (LowerInverse.speed (b+1/2) B))
    (hX : 0<X.lo) (hQ : 0<(qBox X).lo) (hV : 0<V.lo) :
    Interval (LowerContact.outerFirst reverse b B) :=
  (inverseFirstBox Z X (ratioBox Y X hX) (qBox X) V hX hQ hV).sub
    (ReferenceAlgebra.firstBox (LowerContact.outer reverse) Y X hX)

def outerSecondBox (reverse : Bool) {b B : ℝ}
    (Z : Interval (b+1/2)) (Y : Interval B) (X : Interval (U B))
    (V : Interval (LowerInverse.speed (b+1/2) B))
    (hX : 0<X.lo) (hQ : 0<(qBox X).lo) (hV : 0<V.lo) :
    Interval (LowerContact.outerSecond reverse b B) :=
  (inverseSecondBox Z X (ratioBox Y X hX) (ratioDBox X hX) (qBox X) V hX hQ hV).sub
    (ReferenceAlgebra.secondBox (LowerContact.outer reverse) Y X hX)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.LowerAlgebra
