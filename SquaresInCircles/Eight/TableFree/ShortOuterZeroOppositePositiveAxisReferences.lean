module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositePositiveAxisSlopes

/-!
# The three named positive-axis endpoint checks

Uncompiled transcription of Section 3.2. The two convex-derivative
rows have negative final first derivative; the remaining row has a
negative final second derivative and positive final first derivative.
Every interval encloses the literal source contact and its exact speed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis.References
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (zeroSourceBox aBox)

abbrev sourceBox : Interval (b (7/10)) := by
  rw [same_source]
  exact zeroSourceBox (7/10) (by norm_num)

def rootBox : Interval (SecondWord.U (b (7/10))) :=
  shifted sourceBox (9/5) (by norm_num) (by
    norm_num [sourceBox,SecondWord.SameZero.PJ.Reference.zeroSourceBox,
      SecondWord.SameZero.PJ.Reference.aBox,SecondWord.SameZero.PJ.Reference.sinBox,
      SecondWord.SameZero.PJ.Reference.cosBox,radicand,
      Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
      Interval.mul,Interval.square,Q0,HighOrderTaylor.S17,HighOrderTaylor.S15,
      HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
      HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8])

def speedBox : Interval (speed (7/10)) :=
  SecondWord.OppositeZero.Reference.speedBox 0 (7/10) (by norm_num) (by norm_num)

macro "axis_reference_arithmetic" : tactic => `(tactic|
  norm_num [sourceBox,rootBox,speedBox,
    SecondWord.OppositeZero.Reference.speedBox,SecondWord.OppositeZero.Reference.rootAt,
    SecondWord.SameZero.PJ.Reference.zeroSourceBox,SecondWord.SameZero.PJ.Reference.aBox,
    SecondWord.SameZero.PJ.Reference.sinBox,SecondWord.SameZero.PJ.Reference.cosBox,
    rootThree,rootStep,shifted,radicand,labelBox,coordinate,ratioBox,ratioDBox,
    source,c,p,q,v,t,Q0,Interval.of_bounds,Interval.point,Interval.add,Interval.sub,
    Interval.neg,Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8])

lemma root_positive : 0<rootBox.lo := by axis_reference_arithmetic

def slopeBox (r : Row) : Interval (l r (b (7/10))) :=
  (Interval.point (q r)).sub ((Interval.point (p r)).mul
    (ratioBox sourceBox rootBox root_positive))

def firstBox (r : Row) : Interval (first r (7/10)) :=
  (Interval.point 1).sub ((slopeBox r).mul speedBox)

def secondBox (r : Row) : Interval (second r (7/10)) :=
  (((Interval.point (-p r)).mul (ratioDBox rootBox root_positive)).mul speedBox.square).
    sub ((slopeBox r).mul (sourceBox.sub (Interval.point (1/2))))

def valueBox (r : Row) : Interval (value r (7/10)) := by
  let V := (((Interval.point ((7/10:ℝ)+c r)).add (labelBox (source r) sourceBox rootBox)).
    add ((Interval.point (v r)).mul aBox))
  convert V using 1
  dsimp [value,plusCost,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  rw [ShortOuterOne.SameContact.arc_zero]
  ring

lemma one_final : first 1 (7/10)<-(9/12500:ℝ) ∧
    (229/250:ℝ)<value 1 (7/10) := by
  have hf : (firstBox 1).hi<-(9/12500:ℝ) := by
    dsimp [firstBox,slopeBox]
    axis_reference_arithmetic
  have hv : (229/250:ℝ)<(valueBox 1).lo := by
    dsimp [valueBox]
    axis_reference_arithmetic
  exact ⟨(firstBox 1).mem.2.trans_lt hf,hv.trans_le (valueBox 1).mem.1⟩

lemma two_final : first 2 (7/10)<-(21/1000:ℝ) ∧
    (951/1000:ℝ)<value 2 (7/10) := by
  have hf : (firstBox 2).hi<-(21/1000:ℝ) := by
    dsimp [firstBox,slopeBox]
    axis_reference_arithmetic
  have hv : (951/1000:ℝ)<(valueBox 2).lo := by
    dsimp [valueBox]
    axis_reference_arithmetic
  exact ⟨(firstBox 2).mem.2.trans_lt hf,hv.trans_le (valueBox 2).mem.1⟩

lemma four_final : second 4 (7/10)<-(3/20:ℝ) ∧
    (27/5000:ℝ)<first 4 (7/10) := by
  have hs : (secondBox 4).hi<-(3/20:ℝ) := by
    dsimp [secondBox,slopeBox]
    axis_reference_arithmetic
  have hf : (27/5000:ℝ)<(firstBox 4).lo := by
    dsimp [firstBox,slopeBox]
    axis_reference_arithmetic
  exact ⟨(secondBox 4).mem.2.trans_lt hs,hf.trans_le (firstBox 4).mem.1⟩

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite.Positive.Axis.References
