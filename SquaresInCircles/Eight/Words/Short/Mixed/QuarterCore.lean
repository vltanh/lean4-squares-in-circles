module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCorePrimaryNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCorePrimaryPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCoreSecondaryNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCoreSecondaryPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterPrimaryReduction

/-!
# Eight squares: every original core-to-outer normalized quarter contact

The secondary and primary owners (`core_secondary`, `core_primary`) cover every row. The signs
of a primary source are reduced by pointwise dominance on the unchanged source state; the cyclic
label itself stays the same.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry

theorem core_secondary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  cases hτ : targetPositive r
  · exact CoreSecondaryNegative.original r hτ upper hs ht hx hm
  · exact CoreSecondaryPositive.original r hτ upper hs ht hx hm

theorem core_primary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<coreOuterCost r a b A B (angle upper x) := by
  have hσ := (primaryRow_signs r).1
  have hm' := (primary_constraint r a b A B (angle upper x)).2 hm
  have hred := core_cost_reduction (r:=r) (A:=A) (B:=B) (φ:=angle upper x) hs
  cases hτ : targetPositive (primaryRow r)
  · exact (CorePrimaryNegative.original (primaryRow r) hσ hτ upper hs ht hx hm').trans_le hred
  · exact (CorePrimaryPositive.original (primaryRow r) hσ hτ upper hs ht hx hm').trans_le hred

end SquaresInCircles.Eight.ShortWord.MixedQuarter
