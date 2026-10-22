module

public import SquaresInCircles.Eight.TableFree.NegativeTerminalSharp
public import SquaresInCircles.Eight.TableFree.UniversalHardSharp

/-!
# Every genuine negative terminal loses an original rigid anchor

Uncompiled transcription of Sections 6.2--6.4 of
`HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md`. The universal hard
theorem supplies the circle equality of the actual transported anchor.
Consequently the one-negative rows need no sign hypothesis on the
opposite HG or TD error. The two-negative construction already retains
the first H loss through its second transport.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate ExactFamily GeometricModel

namespace SignedCycle

theorem HardInput.all_anchors_on {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) : AllAnchorsOn qStar I.cycle := by
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ := I.hard_sharp hqL hq
  exact hcircle

end SignedCycle

namespace AlignedNegative

/-- The strict loss is on the original H anchor. The hard theorem is
applied to this very descendant, with its actual retained E state. -/
theorem NegativeGEntry.false_at_sharp {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : NegativeGEntry q C w)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hH : (C.point H).Contained q) : False := by
  have hcircle := J.target.all_anchors_on hqL hq
  exact circle_loss_impossible (hH.trans hq) J.H_circle_loss
    (hcircle H (by simp [anchorVertices]))

/-- The complete G-negative/T-hard cell, with arbitrary opposite
outer error and either retained TD owner. -/
theorem negative_g_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnotGA : ¬I.cycle.Feasible G 0) (hBT : I.cycle.Feasible B 2) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := aligned_negative_boundary_entry I hqL hcap
    hHG htG hyG hGA hnotGA hBT
  exact J.false_at_sharp hqL hq (I.necessary.contained H)

end AlignedNegative

namespace DirectNegativeT

/-- The strict original D loss is incompatible with universal hard
rigidity, irrespective of the original or descendant HG error. -/
theorem HardTEntry.false_at_sharp {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : HardTEntry q C w)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hD : (C.point D).Contained q) : False := by
  have hcircle := J.input.all_anchors_on hqL hq
  exact circle_loss_impossible (hD.trans hq) J.D_circle_loss
    (hcircle D (by simp [anchorVertices]))

/-- The complete G-hard/T-negative cell. E is the original
nonpositive core or outer point, as required by the written transport. -/
theorem negative_t_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hyT : 0≤(I.cycle.point T).y) (hBT : I.cycle.Feasible B 3)
    (hnotBT : ¬I.cycle.Feasible B 2) (hGA : I.cycle.Feasible G 0) : False := by
  have hcap : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := one_negative_t_entry I.necessary hqL hcap I.anchors_normal
    I.witnesses I.zero_signs I.E_nonpos (I.radial E)
    hTD htT hyT hBT hnotBT hGA
  exact J.false_at_sharp hqL hq (I.necessary.contained D)

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
