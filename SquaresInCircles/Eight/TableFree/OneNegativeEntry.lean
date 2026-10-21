module

public import SquaresInCircles.Eight.TableFree.OneNegativeAnchorOrder
public import SquaresInCircles.Eight.TableFree.OneNegativeCycleEntry
public import SquaresInCircles.Eight.TableFree.TD2Span

/-!
# Complete actual one-negative primary entry at the original radius

Uncompiled source draft.  The original .22 span follows from the actual
negative contact, and the H≤D alternative is excluded by the original
anchor-order theorem.  Every E radial kind and original E position is
already included in the constructive transport.  The result retains the
strict original-D circle loss and the complete actual hard input.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate

theorem NegativeTBarrier.false {q : ℝ} (I : NegativeTBarrier q) (hq : q≤qCap) : False := by
  have hh := SignedCycle.negative_BT_anchor_order hq I.necessary I.anchors_normal
    I.E_nonpos I.witnesses I.zero_signs I.TD_aligned I.negative_BT I.T_nonneg
    I.BT_secondary I.BT_unavailable I.GA_hard
  exact (not_lt_of_ge I.H_not_above) hh

namespace DirectNegativeT

/-- Fully constructive same-radius hard entry.  No span, H--D order,
near-H condition, mixed sign, or terminal exclusion is an input. -/
theorem one_negative_t_entry {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w)
    (hyE : (C.point E).y≤0) (hrE : (C.point E).Boundary q)
    (halign : C.theta T=C.theta D) (ht : C.theta D<C.theta B)
    (hyT : 0≤(C.point T).y) (hBT : C.Feasible B 3)
    (hnot : ¬C.Feasible B 2) (hGA : C.Feasible G 0) :
    Nonempty (HardTEntry q C w) := by
  have hspan := AlignedNegative.opposite_aligned_negative_span hn hqU ha w
    halign ht hyT hBT hnot hGA
  rcases one_negative_t_entry_of_span hn hqL hqU ha w hz hyE hrE hspan
    halign ht hyT hBT hnot hGA with hentry | ⟨I⟩
  · exact hentry
  · exact (I.false hqU).elim

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
