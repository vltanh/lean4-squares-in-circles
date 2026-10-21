module

public import SquaresInCircles.Eight.TableFree.FrameHighHighVaryingCalculus
public import SquaresInCircles.Eight.TableFree.FrameMidHighTargetReferences

/-!
# Two curvature endpoints and one tangent for the high/high support

The three norm cages follow by squaring positive rationals against the
literal quadratic norm.  The actual high endpoint and radius are enclosed
by their defining circle.  The comparisons below are fixed references for
the whole-interval derivative argument.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighHighVaryingReferences
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
  · exact ((((((((Interval.point x).add small).add ((Interval.point 2).mul l)).
      add ((Interval.point u).mul ((Interval.point 1).add aBox))).
      add ((Interval.point v).mul bBox)).
      add (((l.mul xBox).sub small).mul c)).
      add (((l.mul yBox).sub small).mul s)).sub (rBox.mul Z))
  · have hh := ((((Interval.point (1/5:ℝ)).
      add ((((l.mul yBox).sub small).sub (m.mul xBox)).mul c)).
      add ((((l.mul xBox).neg.add small).sub (m.mul yBox)).mul s)).sub (rBox.mul n1))
    convert hh using 1
    simp only [Fd,N1_formula]
  · have hh := (((((l.mul xBox).neg.add small).sub (mm.mul yBox)).mul c).
      add ((((l.mul yBox).neg.add small).add (mm.mul xBox)).mul s)).sub (rBox.mul n2)
    convert hh using 1
    simp only [Fdd,N2_formula]

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

theorem endpoint_curvatures : (1/2:ℝ)<Fdd (3/5) ∧ (1/2:ℝ)<Fdd (19/20) := by
  have hl : (1/2:ℝ)<leftReference.second.lo := by
    norm_num [leftReference,supportIntervals,leftNorm,aBox,bBox,rBox,xBox,yBox,
      sinBox,cosBox,lam,u,v,T,Delta,Interval.point,Interval.of_bounds,
      Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
      Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hr : (1/2:ℝ)<rightReference.second.lo := by
    norm_num [rightReference,supportIntervals,rightNorm,aBox,bBox,rBox,xBox,yBox,
      sinBox,cosBox,lam,u,v,T,Delta,Interval.point,Interval.of_bounds,
      Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
      Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact ⟨hl.trans_le leftReference.second.mem.1,hr.trans_le rightReference.second.mem.1⟩

theorem tangent_value : (911/1000:ℝ)<F (4/5) := by
  have hh : (911/1000:ℝ)<tangentReference.value.lo := by
    norm_num [tangentReference,supportIntervals,tangentNorm,aBox,bBox,rBox,xBox,yBox,
      sinBox,cosBox,lam,u,v,Interval.point,Interval.of_bounds,
      Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
      Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact hh.trans_le tangentReference.value.mem.1

theorem tangent_slope : |Fd (4/5)|<(1/250:ℝ) := by
  have hl : -(1/250:ℝ)<tangentReference.first.lo := by
    norm_num [tangentReference,supportIntervals,tangentNorm,aBox,bBox,rBox,xBox,yBox,
      sinBox,cosBox,lam,u,v,T,Delta,Interval.point,Interval.of_bounds,
      Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
      Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  have hr : tangentReference.first.hi<(1/250:ℝ) := by
    norm_num [tangentReference,supportIntervals,tangentNorm,aBox,bBox,rBox,xBox,yBox,
      sinBox,cosBox,lam,u,v,T,Delta,Interval.point,Interval.of_bounds,
      Interval.add,Interval.sub,Interval.neg,Interval.mul,Interval.div,Interval.inv,
      Interval.square,Interval.cube,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
      SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8]
  exact abs_lt.mpr ⟨hl.trans_le tangentReference.first.mem.1,
    tangentReference.first.mem.2.trans_lt hr⟩

end SquaresInCircles.Eight.TableFree.FrameHighHighVaryingReferences
