module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoLabels
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoTargetContact

/-!
# The original negative outer quarter edge and its four weak projections

The cost is the literal role-two source label minus the literal role-three
target label.  Each cut below is an algebraic rearrangement of one of
the original weak axes at the original common radius.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def value (b B φ : ℝ) : ℝ := φ-P b+T B
def upperTarget (a b x : ℝ) : ℝ :=
  1/2-(a-1/2)*Real.cos x-(b-1/2)*Real.sin x
def lowerSource (A B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x+(A+1/2)*Real.sin x
def upperSource (A B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x-(A-1/2)*Real.sin x

lemma source_mem {a b : ℝ} (hs : OuterState a b) : b∈Icc 0 outerDiagonal :=
  ⟨hs.1,(CommonQuarter.outer_bounds hs).2.2.2.1⟩

lemma primary_mem {a b : ℝ} (hs : OuterState a b) : a∈Icc outerDiagonal outerAxial :=
  ⟨(CommonQuarter.outer_bounds hs).1,(CommonQuarter.outer_bounds hs).2.1⟩

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 2 .outer .outer false false a b A B φ=value b B φ := by
  unfold value
  rw [show P b=PLabel.eval a b from PLabel.outer_actual hs,
    show T B=TLabel.eval A B from TLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,PLabel,TLabel,RoleLabel.eval]
  ring

lemma upper_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2+x)=(1+Real.cos x+Real.sin x)/2 := by
  rw [quarter_width (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩),
    abs_of_nonneg (positive_trig hx).2.2.1]

lemma lower_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2-x)=(1+Real.cos x+Real.sin x)/2 := by
  have hh := quarter_width (x := -x)
    (abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  simpa only [sub_eq_add_neg,Real.cos_neg,Real.sin_neg,abs_neg,
    abs_of_nonneg (positive_trig hx).2.2.1] using hh

lemma lower_target_cut {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    TargetContact.B b x≤B := by
  have hw := lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [TargetContact.B]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma upper_target_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2+x)) :
    upperTarget a b x≤B := by
  have hw := upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperTarget]
  linarith

lemma lower_source_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-x)) :
    lowerSource A B x≤a := by
  have hw := lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerSource]
  linarith

lemma upper_source_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    upperSource A B x≤a := by
  have hw := upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperSource]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo
