module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetJContact
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetPContact
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetLContact

/-!
# All three opposite mixed zero target-secondary families

Uncompiled source draft.  This restores the original target after the
first-contact lower bound and then joins the two closed angle signs.
The physical radius, source point, target point, and weak owner are the
ones supplied to the theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target
open CommonQuarter CorePairGeometry Arithmetic

theorem negative_projection (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤-a*Real.sin x+b*Real.cos x+B) :
    (17953/20000:ℝ)<-x+c r+g r*b+(F r).outer B := by
  have hc : x∈angles := ⟨hx.1,(original_angle hs ht hx hm).le⟩
  have hcontact := original_contact hs ht hc hm
  have hrestore := original_cost r hs ht hc hm
  have hl : (17953/20000:ℝ)<-x+c r+g r*b+(F r).outer (contact a b x) := by
    fin_cases r
    · exact JContact.core hs hc hcontact.1.2
    · exact PContact.core hs hc hcontact.1.2
    · exact LContact.core hs hc hcontact.1.2
  exact hl.trans_le hrestore

theorem original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  by_cases hp : 0≤x
  · exact TargetPositive.original r hs ht ⟨hp,(abs_le.mp hx).2⟩ hm
  · have hx' : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hsin : Real.sin x≤0 := by
      have hh := (positive_trig hx').2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hx
    rw [abs_of_nonpos hsin] at hw
    have hprojection : pairWidth x≤a*Real.sin x+b*Real.cos x+B := by
      norm_num [Eight.forwardMargin] at hm
      linarith
    rw [hw] at hprojection
    have hh := negative_projection r hs ht hx' (by
      simp only [Real.sin_neg,Real.cos_neg,mul_neg,neg_neg]
      linarith)
    simpa only [neg_neg] using hh

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target
