module

public import SquaresInCircles.Eight.TableFree.SecondOuterKBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoData

/-!
# The literal negative edge-three cost and its original projections

The source label is `T` and the target label is `K`, both evaluated on
the original common circle.  The weak owner inequalities are the same
physical projections as the preceding negative-quarter family.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

def TPrimaryLabel : RoleLabel := TLabel.primary

namespace NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

def value (b B φ : ℝ) : ℝ := φ-T b+K B

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer false false a b A B φ=value b B φ := by
  unfold value
  rw [show T b=TLabel.eval a b from TLabel.outer_actual hs,
    show K B=KLabel.eval A B from KLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,KLabel,RoleLabel.eval]
  ring

lemma lower_first_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x)) :
    b≤(A-1/2)*Real.cos x+(B-1/2)*Real.sin x-1/2 := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  linarith

lemma upper_first_implies_lower {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x) := by
  have hu := NegativeTwo.upper_width hx
  have hl := NegativeTwo.lower_width hx
  have hprod := mul_nonneg ht.1 (positive_trig hx).2.2.1
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hu] at hm
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hl]
  nlinarith

lemma primary_actual {a b : ℝ} (hs : OuterState a b) : TPrimaryLabel.outer a= -T b :=
  TLabel.primary_actual hs

end NegativeThree

end SquaresInCircles.Eight.TableFree.SecondWord
