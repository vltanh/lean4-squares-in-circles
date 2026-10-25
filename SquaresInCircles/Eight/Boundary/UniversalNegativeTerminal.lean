module

public import SquaresInCircles.Eight.Words.One.NegativeEntry
public import SquaresInCircles.Eight.Boundary.UniversalHardSharp

/-!
# Eight squares: the negative terminal cases

The anchors of a hard input at a level `qLow ≤ q ≤ qStar` lie on the circle of squared radius
`qStar` (`HardInput.all_anchors_on`, from `HardInput.hard_sharp`). Each negative terminal case of
a normalized boundary input leads to a hard input at which the anchor H, or D, has a strict loss
against that circle, which is impossible (`NegativeGEntry.false_at_sharp`,
`HardTEntry.false_at_sharp`). So neither the case of G negative and T hard
(`negative_g_impossible`) nor that of G hard and T negative (`negative_t_impossible`) occurs,
whatever the error of the opposite edge, T–D or H–G.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate Stationary GeometricModel

namespace SignedCycle

theorem HardInput.all_anchors_on {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qStar) : AllAnchorsOn qStar I.cycle := by
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ := I.hard_sharp hqL hq
  exact hcircle

end SignedCycle

namespace AlignedNegative

/-- A negative G entry at a level in `[qLow, qStar]` is impossible: the anchor H of its target
hard input, which keeps the E of the cycle, lies on the circle of `qStar`, while the entry gives H
a strict loss. -/
theorem NegativeGEntry.false_at_sharp {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : NegativeGEntry q C w)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hH : (C.point H).Contained q) : False := by
  have hcircle := J.target.all_anchors_on hqL hq
  exact circle_loss_impossible (hH.trans hq) J.H_circle_loss
    (hcircle H (by simp [anchorVertices]))

/-- The case of G negative and T hard does not occur: G on the frame of H with `θA < θH` and
`yG ≤ 0`, G–A separated along the axis one but not zero, and B–T along the axis two, for any
error and either owner of T–D. -/
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

/-- A hard T entry at a level in `[qLow, qStar]` is impossible: the anchor D of its hard input
lies on the circle of `qStar`, while the entry gives D a strict loss, whatever the error of
H–G. -/
theorem HardTEntry.false_at_sharp {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : HardTEntry q C w)
    (hqL : qLow≤q) (hq : q≤qStar)
    (hD : (C.point D).Contained q) : False := by
  have hcircle := J.input.all_anchors_on hqL hq
  exact circle_loss_impossible (hD.trans hq) J.D_circle_loss
    (hcircle D (by simp [anchorVertices]))

/-- The case of G hard and T negative does not occur: T on the frame of D with `θD < θB` and
`yT ≥ 0`, B–T separated along the axis three but not two, and G–A along the axis zero. E is the
point of the input, on the core or on the outer circle, with `y ≤ 0`. -/
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
end SquaresInCircles.Eight
