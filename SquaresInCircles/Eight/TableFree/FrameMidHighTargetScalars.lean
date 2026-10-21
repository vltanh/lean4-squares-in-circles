module

public import SquaresInCircles.Eight.TableFree.FrameMidHighTargetReferences

/-!
# Complete target-high circular support intervals

The first three supports are concave; the last is increasing.  Their
endpoint comparisons therefore supply the original strengthened bound
on all four closed intervals.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighTargetScalars
open FrameMidHighTargetCalculus FrameMidHighTargetReferences

theorem positive_lower {x : ℝ} (hx : x∈Icc (7/10:ℝ) (93/100)) :
    (4463/5000:ℝ)<F true true (7/20) x :=
  concave_gt_of_endpoints positive_concave hx positive_left positive_right

theorem negative_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (71/50)) :
    (4463/5000:ℝ)<F false false (2/5) x :=
  concave_gt_of_endpoints negative_concave hx negative_left negative_right

theorem opposite_before_lower {x : ℝ} (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50)) :
    (4463/5000:ℝ)<F false true (2/5) x :=
  concave_gt_of_endpoints opposite_concave hx opposite_left opposite_before_quarter

theorem opposite_after_lower {x : ℝ} (hx : x∈Icc (Real.pi/2+1/50) (171/100:ℝ)) :
    (4463/5000:ℝ)<after false true (2/5) x := by
  have hh := after_monotone ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  exact opposite_after_quarter.trans_le hh

end SquaresInCircles.Eight.TableFree.FrameMidHighTargetScalars
