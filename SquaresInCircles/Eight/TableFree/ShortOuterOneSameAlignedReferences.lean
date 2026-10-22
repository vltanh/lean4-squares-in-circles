module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameData

/-!
# The named aligned values for the paired same-sign owners

Uncompiled transcription of the fixed substitutions in Sections 2 and 4
of `HAND_SHORT_WORD_SAME_SIGN_PRIMARY_COMPLETE_WITHOUT_TABLES.md`.
All enclosures remain attached to the actual circle roots. The only
interior reference is 517/10000; 1/80 is the stated initial-derivative
reference. No variable-domain grid is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Reference
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)
open StationaryPrimitives (Interval)
open SecondWord (U)
open SecondWord.OppositeThree.ReferenceAlgebra

def valueBox (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) : Interval (aligned r B) := by
  convert ((((((piBox.div (Interval.point 2) (by norm_num [Interval.point])).add
    (Interval.point (c r))).add
      ((Interval.point (p r)).mul ((Interval.point 1).sub Y))).sub
        ((Interval.point (q r)).mul (coordinate S))).sub
          ((Interval.point (P r)).mul (coordinate T))).add ((Interval.point (t r)).mul Y)
    using 1 <;> dsimp [aligned,source,target] <;> ring

def firstBox (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hT : 0<T.lo) (hS : 0<S.lo) :
    Interval (alignedD r B) := by
  convert ((((Interval.point (-p r)).sub
    ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).add
      ((Interval.point (P r)).mul (ratioBox Y T hT))).add (Interval.point (t r))) using 1 <;>
    dsimp [alignedD,sourceD,targetD] <;> ring

def angleBox (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hS : 0<S.lo) :
    Interval (initialAngle r B) := by
  convert (Interval.point 1).sub
    (((Interval.point (p r)).add
      ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).mul
        (T.sub (Interval.point 1))) using 1 <;>
    dsimp [initialAngle,sourceD,U] <;> ring

private macro "same_aligned_reference" : tactic => `(tactic|
  norm_num [valueBox,firstBox,angleBox,piBox,coordinate,shifted,radicand,rootThree,rootStep,
    ratioBox,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.div,Interval.inv,Q0,c,p,q,P,t,eta])

lemma diagonal_endpoints (r : Row) (hr : r=1 ∨ r=2) :
    (8981/10000:ℝ)<aligned r b0 := by
  let D := RoleFour.dBox
  let Y : Interval b0 := (Interval.point 1).sub D
  have hrad : 0≤(radicand Y).lo := by
    norm_num [Y,D,RoleFour.dBox,radicand,Interval.of_bounds,Interval.point,
      Interval.add,Interval.sub,Interval.neg,Interval.square,Interval.mul,Q0]
  let T := shifted Y (19/10) (by norm_num) hrad
  let S : Interval (U (1-b0)) := Interval.of_bounds
    (show U (1-b0)∈Icc (1399214065109/1000000000000:ℝ)
      (1399214065110/1000000000000) from by
        have hh : 1-b0=outerDiagonal := by dsimp [b0]; ring
        rw [hh,U,SameContact.arc_diagonal]
        constructor <;> linarith [ShortMixedZero.fine_diagonal_bounds.1,
          ShortMixedZero.fine_diagonal_bounds.2])
  have hlo : (8981/10000:ℝ)<(valueBox r Y T S).lo := by
    rcases hr with rfl | rfl <;>
      dsimp [Y,D,T,S] <;> norm_num [RoleFour.dBox] <;> same_aligned_reference
  exact hlo.trans_le (valueBox r Y T S).mem.1

lemma convex_reference :
    (89811/100000:ℝ)<aligned 0 (517/10000)-(alignedD 0 (517/10000))^2/2 := by
  let Y := Interval.point (517/10000:ℝ)
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (27/20) (by norm_num) hZ
  have hT : 0<T.lo := by dsimp [T,Y]; same_aligned_reference
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  let V := valueBox 0 Y T S
  let D := firstBox 0 Y T S hT hS
  let L := V.sub (D.square.mul (Interval.point (1/2)))
  have hlo : (89811/100000:ℝ)<L.lo := by
    dsimp [L,V,D,T,S,Z,Y]
    same_aligned_reference
  have hh := hlo.trans_le L.mem.1
  simpa only [div_eq_mul_inv] using hh

lemma eta_values (r : Row) : (89908/100000:ℝ)<aligned r eta := by
  let Y := Interval.point eta
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hlo : (89908/100000:ℝ)<(valueBox r Y T S).lo := by
    fin_cases r <;> dsimp [T,S,Z,Y] <;> same_aligned_reference
  exact hlo.trans_le (valueBox r Y T S).mem.1

lemma eta_derivative : alignedD 0 eta<0 := by
  let Y := Interval.point eta
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hT : 0<T.lo := by dsimp [T,Y]; same_aligned_reference
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  have hhi : (firstBox 0 Y T S hT hS).hi<0 := by
    dsimp [T,S,Z,Y]
    same_aligned_reference
  exact (firstBox 0 Y T S hT hS).mem.2.trans_lt hhi

lemma angle_zero (r : Row) : -(1/50:ℝ)<initialAngle r 0 := by
  let Y := Interval.point (0:ℝ)
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  have hlo : -(1/50:ℝ)<(angleBox r Y T S hS).lo := by
    fin_cases r <;> dsimp [T,S,Z,Y] <;> same_aligned_reference
  exact hlo.trans_le (angleBox r Y T S hS).mem.1

lemma angle_eta (r : Row) : 0<initialAngle r eta := by
  let Y := Interval.point eta
  let Z := (Interval.point 1).sub Y
  have hY : 0≤(radicand Y).lo := by dsimp [Y]; same_aligned_reference
  have hZ : 0≤(radicand Z).lo := by dsimp [Z,Y]; same_aligned_reference
  let T := shifted Y (19/10) (by norm_num) hY
  let S := shifted Z (13/10) (by norm_num) hZ
  have hS : 0<S.lo := by dsimp [S,Z,Y]; same_aligned_reference
  have hlo : 0<(angleBox r Y T S hS).lo := by
    fin_cases r <;> dsimp [T,S,Z,Y] <;> same_aligned_reference
  exact hlo.trans_le (angleBox r Y T S hS).mem.1

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Reference
