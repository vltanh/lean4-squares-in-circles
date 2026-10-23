module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperMinimum

/-!
# All six original opposite-primary upper angle halves

Uncompiled assembly of the two complementary upper-primary hand notes.
The full contact region, its axial/diagonal junction and its possible
interior state minimum are covered before the original weak separator
is restored. No state or angle boundary hypothesis remains.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic

theorem contact_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (4489/5000:ℝ)<value r B x := by
  fin_cases r
  · have hh := zero_contact hd
    linarith
  · exact Minimum.one_contact hd
  · exact simple_contact 2 (Or.inl rfl) hd
  · exact simple_contact 3 (Or.inr (Or.inl rfl)) hd
  · exact simple_contact 4 (Or.inr (Or.inr (Or.inl rfl))) hd
  · exact simple_contact 5 (Or.inr (Or.inr (Or.inr rfl))) hd

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : width x≤a+A*Real.sin x-B*Real.cos x) :
    threshold r<cost r true a b A B x := by
  obtain ⟨D,hD,hbetter⟩ := original_to_contact r hs ht hx hm
  have hh := (contact_lower r hD).trans_le hbetter
  have hthreshold : threshold r<(4489/5000:ℝ) := by
    fin_cases r <;> norm_num [threshold]
  exact hthreshold.trans hh

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
