module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerEnvelopeData

/-!
# Eight squares: exact arithmetic transport for the target envelope

These expressions retain the actual label and its circle radical.
They are used only at named endpoint and critical-root references.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open ReferenceAlgebra

def zBox {B : ℝ} (Y : Interval B) : Interval (z B) := Y.add (Interval.point (1/2))
def pBox {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) : Interval (p B) :=
  firstBox LLabel Y X hX
def ellBox {B : ℝ} (Y : Interval B) (X : Interval (U B)) (hX : 0<X.lo) : Interval (ell B) :=
  secondBox LLabel Y X hX
def SBox {B : ℝ} (Y : Interval B) (P : Interval (p B)) (hP : 0<P.lo) : Interval (S B) :=
  (zBox Y).square.add ((Interval.point 1).div P.square (Interval.square_lo_pos hP))
def hBox {B : ℝ} (Y : Interval B) (P : Interval (p B)) : Interval (h B) := (zBox Y).mul P
def h₁Box {B : ℝ} (Y : Interval B) (P : Interval (p B)) (E : Interval (ell B)) : Interval (h₁ B) :=
  P.add ((zBox Y).mul E)
def markerBox {B : ℝ} (P : Interval (p B)) (E : Interval (ell B)) : Interval (marker B) :=
  E.neg.sub ((Interval.point (3/2)).mul P)
def slopeRatioBox {B : ℝ} (P : Interval (p B)) (E : Interval (ell B))
    (hP : 0<P.lo) : Interval (slopeRatio B) := E.neg.div P.square (Interval.square_lo_pos hP)
def DBox {B : ℝ} (Y : Interval B) (P : Interval (p B)) (E : Interval (ell B))
    (hP : 0<P.lo) : Interval (D B) := (zBox Y).sub (E.div P.cube (Interval.cube_lo_pos hP))
def g₁Box {B : ℝ} (H : Interval (h B)) (Q : Interval (S B)) (hQ : 0<Q.lo) : Interval (g₁ B) :=
  H.neg.div ((Interval.point 2).mul Q) (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ)
def g₂Box {B : ℝ} (H : Interval (h B)) (H₁ : Interval (h₁ B))
    (Q : Interval (S B)) (D₀ : Interval (D B)) (hQ : 0<Q.lo) (hD : 0<D₀.lo) : Interval (g₂ B) :=
  (H.div ((Interval.point 2).mul Q.square)
    (Interval.mul_lo_pos (by norm_num [Interval.point]) (Interval.square_lo_pos hQ))).sub
    (H₁.div (((Interval.point 4).mul Q).mul D₀)
      (Interval.mul_lo_pos (Interval.mul_lo_pos (by norm_num [Interval.point]) hQ) hD))

end SquaresInCircles.Eight.SecondWord.OppositeThree.LowerEnvelope
