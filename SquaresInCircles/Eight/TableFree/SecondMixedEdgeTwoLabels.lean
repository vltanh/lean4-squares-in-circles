module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeThreeLabels

/-!
# The four literal mixed role-two costs

The equalities retain the original circle points and both core pieces.
The reflected role-six cases use the common exact cost reflection.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo
open CommonQuarter CorePairGeometry Arithmetic

def g : ℝ := 103981/100000
def c : ℝ := 1/800

lemma core_primary_lower {a b : ℝ} (hs : CoreState a b) : CoreAngleEndpoint.diagonal≤a := by
  rcases hs with ⟨rfl,hb,hbu⟩ | ⟨hb,hba,hq⟩
  · linarith [CoreAngleEndpoint.diagonal_bounds.2]
  · exact (CoreAngleEndpoint.corner_diagonal hb hba hq).2

lemma core_outer_negative_negative {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 2 kind .outer false false a b A B φ=φ-c-g*b+T B := by
  rw [show T B=TLabel.eval A B from TLabel.outer_actual ht]
  cases kind <;> norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,RoleLabel.eval,g,c] at hk ⊢ <;> ring

lemma core_outer_negative_positive {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 2 kind .outer false true a b A B φ=φ-c-g*b-V B := by
  rw [show V B=VLabel.eval A B from VLabel.outer_actual ht]
  cases kind <;> norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,RoleLabel.eval,g,c] at hk ⊢ <;> ring

lemma outer_core_negative_negative {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) :
    cost 2 .outer kind false false a b A B φ=φ-P b+MixedThree.negativeCore A B := by
  rw [show P b=PLabel.eval a b from PLabel.outer_actual hs]
  cases kind <;> norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,PLabel,RoleLabel.eval,MixedThree.negativeCore] at hk ⊢ <;> ring

lemma outer_core_negative_positive {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) :
    cost 2 .outer kind false true a b A B φ=φ+1449/100000-P b-(1303/1250)*B := by
  rw [show P b=PLabel.eval a b from PLabel.outer_actual hs]
  cases kind <;> norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,PLabel,RoleLabel.eval] at hk ⊢ <;> ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo
