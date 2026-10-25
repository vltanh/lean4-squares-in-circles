module

public import SquaresInCircles.Eight.TableFree.SecondOuterVBounds
public import SquaresInCircles.Eight.TableFree.SecondOuterKBounds
public import SquaresInCircles.Eight.TableFree.CoreAngleEndpoint

/-!
# Literal edge-three labels on both closed core pieces

The core side and corner use the same role polynomial.  Each displayed
cost is an exact substitution of the original radial kind and signs;
the core upper bound is proved from the side or its actual corner
circle.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree
open CommonQuarter CorePairGeometry Arithmetic

def negativeCore (a b : ℝ) : ℝ :=
  11021/50000-(8623/25000)*a+(98439/100000)*b-(2667/50000)*b^2

lemma negative_core_upper {a b : ℝ} (hs : CoreState a b) :
    negativeCore a b≤11021/50000-(8623/25000)*(7/12)+(98439/100000)*b := by
  rcases hs with ⟨rfl,hb,hbu⟩ | ⟨hb,hba,hq⟩
  · dsimp [negativeCore]
    nlinarith [sq_nonneg b]
  · have ha := (CoreAngleEndpoint.corner_diagonal hb hba hq).2
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hb 2
    dsimp [negativeCore]
    nlinarith [CoreAngleEndpoint.diagonal_bounds.1]

lemma core_outer_positive_positive {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 3 kind .outer true true a b A B φ=
      φ-1449/100000+(1303/1250)*b-L B := by
  rw [show L B=LLabel.eval A B from LLabel.outer_actual ht]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,LLabel,RoleLabel.eval]
  all_goals ring

lemma core_outer_positive_negative {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 3 kind .outer true false a b A B φ=
      φ-1449/100000+(1303/1250)*b+K B := by
  rw [show K B=KLabel.eval A B from KLabel.outer_actual ht]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,KLabel,RoleLabel.eval]
  all_goals ring

lemma core_outer_negative_positive {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 3 kind .outer false true a b A B φ=φ-negativeCore a b-L B := by
  rw [show L B=LLabel.eval A B from LLabel.outer_actual ht]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,LLabel,RoleLabel.eval,negativeCore]
  all_goals ring

lemma core_outer_negative_negative {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 3 kind .outer false false a b A B φ=φ-negativeCore a b+K B := by
  rw [show K B=KLabel.eval A B from KLabel.outer_actual ht]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,KLabel,RoleLabel.eval,negativeCore]
  all_goals ring

lemma outer_core_positive_positive {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) :
    cost 3 .outer kind true true a b A B φ=
      φ+V b-497/10000-(94831/100000)*B := by
  rw [show V b=VLabel.eval a b from VLabel.outer_actual hs]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,RoleLabel.eval]
  all_goals ring

lemma outer_core_positive_negative {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) :
    cost 3 .outer kind true false a b A B φ=
      φ+V b+16823/100000+(7789/12500)*B := by
  rw [show V b=VLabel.eval a b from VLabel.outer_actual hs]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,VLabel,RoleLabel.eval]
  all_goals ring

lemma outer_core_negative_positive {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) :
    cost 3 .outer kind false true a b A B φ=
      φ-T b-497/10000-(94831/100000)*B := by
  rw [show T b=TLabel.eval a b from TLabel.outer_actual hs]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,RoleLabel.eval]
  all_goals ring

lemma outer_core_negative_negative {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) :
    cost 3 .outer kind false false a b A B φ=
      φ-T b+16823/100000+(7789/12500)*B := by
  rw [show T b=TLabel.eval a b from TLabel.outer_actual hs]
  cases kind
  · exact absurd rfl hk
  all_goals norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,RoleLabel.eval]
  all_goals ring

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree
