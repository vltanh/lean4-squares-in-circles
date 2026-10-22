module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeSmallSide
public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeSide
public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeUpper

/-!
# All six original negative-core primary families

Uncompiled assembly. The lower half uses the two prescribed straight-side
arguments and the complete corner argument; the upper half uses its one
increasing whole-circle support. Both closed core pieces and all ties
are included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative
open CommonQuarter CorePairGeometry

theorem original (r : Row) (hr : Remaining r) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  cases upper
  · rcases ht with ⟨hA,hB0,hB1⟩|⟨hB,hBA,hcircle⟩
    · by_cases hsmall : SmallSide.Rows r
      · exact SmallSide.original r hsmall hs hA ⟨hB0,hB1⟩ hx hm
      · have hrow : SideChord.Rows r := by
          rcases (remaining_iff r).1 hr with h|h|h|h|h|h <;>
            simp_all [SmallSide.Rows,SideChord.Rows]
        exact SideChord.original_side r hr hrow hs hA hx hm
    · exact Corner.original_lower r hr hs hB hBA hcircle hx hm
  · exact Upper.original r hr hs ht hx hm

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative
