module

public import SquaresInCircles.Eight.Frames.High.HighVaryingCalculus
public import SquaresInCircles.Eight.Frames.Mid.HighTargetReferences

/-!
# Eight squares: two curvature endpoints and one tangent for the high/high support

The three norm cages follow by squaring positive rationals against the
literal quadratic norm.  The actual high endpoint and radius are enclosed
by their defining circle.  The comparisons below are fixed references for
the whole-interval derivative argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighVaryingReferences
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameHighHighVaryingCalculus
open StationaryPrimitives (Interval)
open FrameMidHighTargetReferences (aBox bBox)
open FrameMidHighVaryingReferences (rBox sinBox cosBox)

def xBox : Interval X := ((Interval.point 1).add aBox).sub bBox
def yBox : Interval Y := ((Interval.point 1).sub aBox).sub bBox

structure SupportIntervals (x : ℝ) where
  value : Interval (F x)
  first : Interval (Fd x)
  second : Interval (Fdd x)

def supportIntervals {x : ℝ} (hx : 0≤x)
    (Z : Interval (N x)) (hZ : 0<Z.lo) : SupportIntervals x := by
  let l := Interval.point (lam x)
  let small := Interval.point (9/100:ℝ)
  let m := Interval.point (2/5:ℝ)
  let mm := Interval.point (4/5:ℝ)
  let s := sinBox hx
  let c := cosBox hx
  let n1 := (Interval.point (T x)).div Z hZ
  let n2 := (Interval.point Delta).div Z.cube (Interval.cube_lo_pos hZ)
  refine ⟨?_,?_,?_⟩
  · exact ((((((((Interval.point x).add small).add ((Interval.point 2).mul l)).add ((Interval.point u).mul ((Interval.point 1).add aBox))).add ((Interval.point v).mul bBox)).add (((l.mul xBox).sub small).mul c)).add (((l.mul yBox).sub small).mul s)).sub (rBox.mul Z))
  · have hh := ((((Interval.point (1/5:ℝ)).add ((((l.mul yBox).sub small).sub (m.mul xBox)).mul c)).add ((((l.mul xBox).neg.add small).sub (m.mul yBox)).mul s)).sub (rBox.mul n1))
    convert hh using 1
    simp only [Fd,N1_formula]
    ring
  · have hh := (((((l.mul xBox).neg.add small).sub (mm.mul yBox)).mul c).add ((((l.mul yBox).neg.add small).add (mm.mul xBox)).mul s)).sub (rBox.mul n2)
    convert hh using 1
    simp only [Fdd,N2_formula]
    ring

theorem norm_reference {x l h : ℝ} (hl : 0<l) (hlh : l<h)
    (hl2 : l^2<(u+lam x)^2+(v-lam x)^2)
    (hh2 : (u+lam x)^2+(v-lam x)^2<h^2) : N x∈Icc l h := by
  have hn := N_pos x
  have hs := N_sq x
  constructor <;> nlinarith

def leftNorm : Interval (N (3/5)) := Interval.of_bounds
  (norm_reference (l := (58345671/100000000:ℝ)) (h := (58345673/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [lam,u,v]) (by norm_num [lam,u,v]))
def rightNorm : Interval (N (19/20)) := Interval.of_bounds
  (norm_reference (l := (46090109/100000000:ℝ)) (h := (46090111/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [lam,u,v]) (by norm_num [lam,u,v]))
def tangentNorm : Interval (N (4/5)) := Interval.of_bounds
  (norm_reference (l := (10152507/20000000:ℝ)) (h := (50762537/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [lam,u,v]) (by norm_num [lam,u,v]))

def leftReference := supportIntervals (show (0:ℝ)≤3/5 by norm_num)
  leftNorm (by norm_num [leftNorm,Interval.of_bounds])
def rightReference := supportIntervals (show (0:ℝ)≤19/20 by norm_num)
  rightNorm (by norm_num [rightNorm,Interval.of_bounds])
def tangentReference := supportIntervals (show (0:ℝ)≤4/5 by norm_num)
  tangentNorm (by norm_num [tangentNorm,Interval.of_bounds])

private lemma r55_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r55_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl

private lemma r55_bBox_lo : bBox.lo=((Interval.point (2/5:ℝ)).mul aBox).lo :=
  r55_mpr_lo b1_eq _ _
private lemma r55_bBox_hi : bBox.hi=((Interval.point (2/5:ℝ)).mul aBox).hi :=
  r55_mpr_hi b1_eq _ _

private lemma r55_first_lo {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).first.lo=
      ((((Interval.point (1/5:ℝ)).add (((((Interval.point (lam x)).mul yBox).sub
        (Interval.point (9/100:ℝ))).sub ((Interval.point (2/5:ℝ)).mul xBox)).mul (cosBox hx))).add
        (((((Interval.point (lam x)).mul xBox).neg.add (Interval.point (9/100:ℝ))).sub
          ((Interval.point (2/5:ℝ)).mul yBox)).mul (sinBox hx))).sub
        (rBox.mul ((Interval.point (T x)).div Z hZ))).lo := by
  dsimp only [supportIntervals]
  apply r55_mpr_lo
  simp only [Fd,N1_formula]
  ring
private lemma r55_first_hi {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).first.hi=
      ((((Interval.point (1/5:ℝ)).add (((((Interval.point (lam x)).mul yBox).sub
        (Interval.point (9/100:ℝ))).sub ((Interval.point (2/5:ℝ)).mul xBox)).mul (cosBox hx))).add
        (((((Interval.point (lam x)).mul xBox).neg.add (Interval.point (9/100:ℝ))).sub
          ((Interval.point (2/5:ℝ)).mul yBox)).mul (sinBox hx))).sub
        (rBox.mul ((Interval.point (T x)).div Z hZ))).hi := by
  dsimp only [supportIntervals]
  apply r55_mpr_hi
  simp only [Fd,N1_formula]
  ring
private lemma r55_second_lo {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).second.lo=
      (((((((Interval.point (lam x)).mul xBox).neg.add (Interval.point (9/100:ℝ))).sub
        ((Interval.point (4/5:ℝ)).mul yBox)).mul (cosBox hx)).add
        (((((Interval.point (lam x)).mul yBox).neg.add (Interval.point (9/100:ℝ))).add
          ((Interval.point (4/5:ℝ)).mul xBox)).mul (sinBox hx))).sub
        (rBox.mul ((Interval.point Delta).div Z.cube (Interval.cube_lo_pos hZ)))).lo := by
  dsimp only [supportIntervals]
  apply r55_mpr_lo
  simp only [Fdd,N2_formula]
  ring

private lemma r55_value_lo {x : ℝ} (hx : 0≤x) (Z : Interval (N x)) (hZ : 0<Z.lo) :
    (supportIntervals hx Z hZ).value.lo=
      ((((((((Interval.point x).add (Interval.point (9/100:ℝ))).add
        ((Interval.point 2).mul (Interval.point (lam x)))).add
        ((Interval.point u).mul ((Interval.point 1).add aBox))).add ((Interval.point v).mul bBox)).add
        ((((Interval.point (lam x)).mul xBox).sub (Interval.point (9/100:ℝ))).mul (cosBox hx))).add
        ((((Interval.point (lam x)).mul yBox).sub (Interval.point (9/100:ℝ))).mul (sinBox hx))).sub
        (rBox.mul Z)).lo := rfl

local macro "hh_varying_arithmetic" : tactic => `(tactic|
  norm_num [leftReference,rightReference,tangentReference,r55_first_lo,r55_first_hi,
    r55_second_lo,r55_value_lo,leftNorm,rightNorm,tangentNorm,aBox,r55_bBox_lo,r55_bBox_hi,
    rBox,xBox,yBox,sinBox,cosBox,lam,u,v,T,Delta,Interval.point,Interval.of_bounds,
    Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
    Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8])

theorem endpoint_curvatures : (1/2:ℝ)<Fdd (3/5) ∧ (1/2:ℝ)<Fdd (19/20) := by
  have hl : (1/2:ℝ)<leftReference.second.lo := by
    hh_varying_arithmetic
  have hr : (1/2:ℝ)<rightReference.second.lo := by
    hh_varying_arithmetic
  exact ⟨hl.trans_le leftReference.second.mem.1,hr.trans_le rightReference.second.mem.1⟩

theorem tangent_value : (911/1000:ℝ)<F (4/5) := by
  have hh : (911/1000:ℝ)<tangentReference.value.lo := by
    hh_varying_arithmetic
  exact hh.trans_le tangentReference.value.mem.1

theorem tangent_slope : |Fd (4/5)|<(1/250:ℝ) := by
  have hl : -(1/250:ℝ)<tangentReference.first.lo := by
    hh_varying_arithmetic
  have hr : tangentReference.first.hi<(1/250:ℝ) := by
    hh_varying_arithmetic
  exact abs_lt.mpr ⟨hl.trans_le tangentReference.first.mem.1,
    tangentReference.first.mem.2.trans_lt hr⟩

end SquaresInCircles.Eight.FrameHighHighVaryingReferences
