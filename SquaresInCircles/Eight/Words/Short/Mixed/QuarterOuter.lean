module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterPositive
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterSecondary
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterPrimaryReduction

/-!
# Eight squares: every normalized outer-to-core quarter contact

The original primary sign dominance is applied only
to the pair inequality, on the same actual source coordinates. The
literal cyclic role labels remain the conclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry

theorem outer_primary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) := by
  have hσ := (primaryRow_signs r).1
  have hm' := (primary_constraint r a b A B (angle upper x)).2 hm
  have hred := outer_cost_reduction (r:=r) (A:=A) (B:=B) (φ:=angle upper x) hs
  cases hτ : targetPositive (primaryRow r)
  · exact (OuterNegative.original (primaryRow r) ⟨hσ,hτ⟩ upper hs ht hx hm').trans_le hred
  · exact (OuterPositive.original (primaryRow r) hσ hτ upper hs ht hx hm').trans_le hred

theorem outer_secondary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourceSecondary r a b A B (angle upper x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle upper x) :=
  OuterSecondary.original r upper hs ht hx hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter
