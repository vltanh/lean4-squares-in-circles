module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositiveInterior
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositiveUpper

/-!
# Eight squares: all original outer-to-positive-core primary contacts

The arguments are only
the exact intrinsic source/target signs, original endpoint states,
closed angle half, and the original weak source-primary separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    (upper : Bool) {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  cases upper
  · exact original_lower r ⟨hσ,hτ⟩ hs ht hx hm
  · exact original_upper r ⟨hσ,hτ⟩ hs ht hx hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterPositive
