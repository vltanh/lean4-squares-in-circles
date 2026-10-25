module

public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeMinimum
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeHigh

/-!
# Eight squares: every original lower transverse negative-core owner

The exact small-target minimum and the large-target aligned deformation
cover the complete physical arc. The contact inequality is used only to
compare with the original source and target, including all weak ties.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower)

theorem transverse_original {a b A B φ : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ-B*Real.cos φ) :
    γ<value a b B φ := by
  have hc := original_contact hs ht hφ hsep
  have hmin : γ<C B φ := by
    by_cases he : B≤27/50
    · exact Minimum.contact_lower ⟨ht.1,he⟩ hφ hc.2.1
    · exact High.lower ht (by linarith) hφ hc.2.1
  exact hmin.trans_le hc.2.2.2.2

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
