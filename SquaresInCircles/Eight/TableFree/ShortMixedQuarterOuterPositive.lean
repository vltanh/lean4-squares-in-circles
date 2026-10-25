module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterPositiveUpper

/-!
# All original outer-to-positive-core primary contacts

Uncompiled source assembly of the complete continuous argument in
section 2 of the circle-and-side hand proof. The arguments are only
the exact intrinsic source/target signs, original endpoint states,
closed angle half, and the original weak source-primary separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry

theorem original (r : Row) (hσ : sourcePositive r=false) (hτ : targetPositive r=true)
    (upper : Bool) {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  cases upper
  · exact original_lower r ⟨hσ,hτ⟩ hs ht hx hm
  · exact original_upper r ⟨hσ,hτ⟩ hs ht hx hm

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
