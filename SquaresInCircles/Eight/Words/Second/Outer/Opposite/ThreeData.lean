module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLabels

/-!
# Eight squares: the literal opposite-sign edge-three pair

The source is the original negative role-three state and the target is
the original positive role-four state.  Every displayed contact bound
is obtained from its unchanged weak forward axis.  No active-contact
assumption is added to these original-coordinate statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def value (b B φ : ℝ) : ℝ := φ-T b-L B
abbrev bOne : ℝ := OppositeTwo.bOne
def lowerSecondary (y x : ℝ) : ℝ :=
  (arc y-1/2)*Real.cos x-(y+1/2)*Real.sin x-1/2
def upperSecondary (y x : ℝ) : ℝ :=
  (arc y-1/2)*Real.cos x+(y-1/2)*Real.sin x-1/2
def lowerPrimary (y x : ℝ) : ℝ :=
  1/2+(arc y+1/2)*Real.sin x+(y+1/2)*Real.cos x
def upperPrimary (y x : ℝ) : ℝ :=
  1/2+(y+1/2)*Real.cos x-(arc y-1/2)*Real.sin x

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer false true a b A B φ=value b B φ := by
  unfold value
  rw [show T b=TLabel.eval a b from TLabel.outer_actual hs,
    show L B=LLabel.eval A B from LLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,LLabel,RoleLabel.eval]
  ring

lemma lower_source_secondary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2-x)) :
    b≤lowerSecondary B x := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma upper_source_secondary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Real.pi/2+x)) :
    b≤upperSecondary B x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma lower_target_primary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2-x)) :
    lowerPrimary b x≤A := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma upper_target_primary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 1 a b A B (-1) 1 (Real.pi/2+x)) :
    upperPrimary b x≤A := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma lower_target_secondary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    B≤lowerSecondary b x := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma upper_target_secondary {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) 1 (Real.pi/2+x)) :
    B≤upperSecondary b x := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperSecondary]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma lower_source_primary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2-x)) :
    lowerPrimary B x≤a := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma upper_source_primary {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Real.pi/2+x)) :
    upperPrimary B x≤a := by
  have hw := NegativeTwo.upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperPrimary]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma lowerPrimary_zero (y : ℝ) : lowerPrimary y 0=1+y := by
  simp [lowerPrimary]
  ring
lemma upperPrimary_zero (y : ℝ) : upperPrimary y 0=1+y := by
  simp [upperPrimary]
  ring

end SquaresInCircles.Eight.SecondWord.OppositeThree
