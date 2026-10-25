module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCapBound
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoDiagonalBound

/-!
# The original lower target-secondary owner

Every original weak separator reaches an actual contact on the same
circle.  Source-coordinate concavity reduces that contact to its four
genuine boundary types, all of which have now been proved with strict
scalar reserves.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic

lemma boundary_contact_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (w : BoundaryContact B) :
    (89777/100000:ℝ)<value w.b B (Real.pi/2-w.x) := by
  rcases w.boundary with hax | hdiag | halign | hcap
  · have hc : TargetContact.B 0 w.x=B := by simpa only [hax] using w.contact
    have hh := axial_contact_lower hB w.angle hc
    rw [hax]
    linarith
  · have hc : TargetContact.B outerDiagonal w.x=B := by
      simpa only [hdiag] using w.contact
    have hh := DiagonalSource.original_contact hB w.angle hc
    rw [hdiag]
    linarith
  · have hc : TargetContact.B w.b 0=B := by simpa only [halign] using w.contact
    have hh := aligned_contact_lower w.source hB hc
    rw [halign,sub_zero]
    linarith
  · have hc : TargetContact.B w.b (7/10)=B := by simpa only [hcap] using w.contact
    have hh := CapCurve.original_contact w.source hB hc
    rw [hcap]
    linarith

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨B',hB',w,hw⟩ := original_lower_boundary hs ht hx hm
  exact (boundary_contact_lower hB' w).trans_le hw

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo
