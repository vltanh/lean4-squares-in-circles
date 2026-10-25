module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerStrip
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerSupport

/-!
# Eight squares: the original lower target-secondary owner on its entire physical angle range

The short interval is concentrated on the original zero-target contact.
The complementary interval uses a single concave circle-support scalar.
Their common endpoint is included in both arguments.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  by_cases hshort : x≤1/100
  · exact LowerStrip.original hs ht ⟨hx.1,hshort⟩ hm
  · exact LowerSupport.original_tail hs ht ⟨by linarith,hx.2⟩ hm

end SquaresInCircles.Eight.SecondWord.OppositeTwo

