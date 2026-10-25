module

public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourScalars
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameData

/-!
# Eight squares: the named aligned values for the paired same-sign owners

All enclosures remain attached to the actual circle roots. The only
interior reference is 517/10000; 1/80 is the stated initial-derivative
reference. No variable-domain grid is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Reference
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
          ((Interval.point (P r)).mul (coordinate T))).add ((Interval.point (t r)).mul Y))
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

private lemma r87_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r87_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r87_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r87_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r87_mpr_lo r87_shifted_eq (congrArg _ r87_shifted_eq) _
private lemma r87_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r87_mpr_hi r87_shifted_eq (congrArg _ r87_shifted_eq) _

private lemma r87_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r87_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r87_mpr_lo r87_coordinate_eq (congrArg _ r87_coordinate_eq) _
private lemma r87_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r87_mpr_hi r87_coordinate_eq (congrArg _ r87_coordinate_eq) _

private lemma r87_value_eq (r : Row) {B : ℝ} : aligned r B =
    Real.pi/2+c r+p r*(1-B)-q r*arc (1-B)-P r*arc B+t r*B := by
  dsimp [aligned,source,target]; ring
private lemma r87_valueBox_lo (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) :
    (valueBox r Y T S).lo = ((((((piBox.div (Interval.point 2) (by norm_num [Interval.point])).add
      (Interval.point (c r))).add
        ((Interval.point (p r)).mul ((Interval.point 1).sub Y))).sub
          ((Interval.point (q r)).mul (coordinate S))).sub
            ((Interval.point (P r)).mul (coordinate T))).add ((Interval.point (t r)).mul Y)).lo :=
  r87_mpr_lo (r87_value_eq r) (congrArg _ (r87_value_eq r)) _

private lemma r87_first_eq (r : Row) {B : ℝ} : alignedD r B =
    -p r-q r*ratio (1-B)+P r*ratio B+t r := by
  dsimp [alignedD,sourceD,targetD]; ring
private lemma r87_firstBox_hi (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hT : 0<T.lo) (hS : 0<S.lo) :
    (firstBox r Y T S hT hS).hi = ((((Interval.point (-p r)).sub
      ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).add
        ((Interval.point (P r)).mul (ratioBox Y T hT))).add (Interval.point (t r))).hi :=
  r87_mpr_hi (r87_first_eq r) (congrArg _ (r87_first_eq r)) _
private lemma r87_firstBox_lo (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hT : 0<T.lo) (hS : 0<S.lo) :
    (firstBox r Y T S hT hS).lo = ((((Interval.point (-p r)).sub
      ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).add
        ((Interval.point (P r)).mul (ratioBox Y T hT))).add (Interval.point (t r))).lo :=
  r87_mpr_lo (r87_first_eq r) (congrArg _ (r87_first_eq r)) _

private lemma r87_angle_eq (r : Row) {B : ℝ} : initialAngle r B =
    1-(p r+q r*ratio (1-B))*(U B-1) := by
  dsimp [initialAngle,sourceD,U]; ring
private lemma r87_angleBox_lo (r : Row) {B : ℝ} (Y : Interval B)
    (T : Interval (U B)) (S : Interval (U (1-B))) (hS : 0<S.lo) :
    (angleBox r Y T S hS).lo = ((Interval.point 1).sub
      (((Interval.point (p r)).add
        ((Interval.point (q r)).mul (ratioBox ((Interval.point 1).sub Y) S hS))).mul
          (T.sub (Interval.point 1)))).lo :=
  r87_mpr_lo (r87_angle_eq r) (congrArg _ (r87_angle_eq r)) _

local macro "same_aligned_reference" : tactic => `(tactic|
  norm_num [r87_valueBox_lo,r87_firstBox_lo,r87_firstBox_hi,r87_angleBox_lo,piBox,
    r87_coordinate_lo,r87_coordinate_hi,r87_shifted_lo,r87_shifted_hi,radicand,rootThree,rootStep,
    ratioBox,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.div,Interval.inv,Q0,c,p,q,P,t,eta])

lemma diagonal_endpoints (r : Row) (hr : r=1 ∨ r=2) :
    (8981/10000:ℝ)<aligned r b0 := by
  let D := RoleFour.dBox
  let Y := (Interval.point 1).sub D
  have hrad : 0≤(radicand Y).lo := by
    norm_num [Y,D,RoleFour.dBox,radicand,Interval.of_bounds,Interval.point,
      Interval.add,Interval.sub,Interval.neg,Interval.square,Interval.mul,Q0]
  let T := shifted Y (19/10) (by norm_num) hrad
  let S : Interval (U (1-(1-outerDiagonal))) := Interval.of_bounds
    (show U (1-(1-outerDiagonal))∈Icc (1399214065109/1000000000000:ℝ)
      (1399214065110/1000000000000) from by
        have hh : 1-(1-outerDiagonal)=outerDiagonal := by ring
        have hd : outerDiagonal+1/2=Real.sqrt (Q0/2) := by dsimp [outerDiagonal]; ring
        rw [hh,U,SameContact.arc_diagonal,hd]
        constructor
        · exact Real.le_sqrt_of_sq_le (by norm_num [Q0])
        · rw [Real.sqrt_le_left (by norm_num)]; norm_num [Q0])
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
  linarith

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

lemma angle_zero (r : Row) : -(1/50:ℝ)< initialAngle r 0 := by
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

lemma angle_eta (r : Row) : 0< initialAngle r eta := by
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

end SquaresInCircles.Eight.ShortOuterOne.Same.Reference
