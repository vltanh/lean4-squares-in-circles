module

public import SquaresInCircles.Eight.TableFree.NonpositiveOuterSharp
public import SquaresInCircles.Eight.TableFree.BothNegativeSpan
public import SquaresInCircles.Eight.TableFree.OneNegativeEntry

/-!
# Original H/D losses exclude genuine negative terminal cells

Uncompiled source draft.  A negative-primary entry pays on the actual H
or D anchor.  The nonpositive hard terminal puts that same descendant
anchor on the sharp circle.  Its strict inequality against the original
contained point is impossible.  In the two-negative cell the second
conversion keeps the first H loss, and both original losses are available.
Neither free intermediate is used as an equality obstruction.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate ExactFamily GeometricModel

namespace SignedCycle

theorem HardInput.nonpositive_outer_all_anchors_on {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T) :
    AllAnchorsOn qStar I.cycle := by
  obtain ⟨_,_,_,_,_,_,_,_,hcircle,_⟩ :=
    I.nonpositive_outer_sharp hqL hqq hGH hDT
  exact hcircle

end SignedCycle

namespace AlignedNegative

/-- The paid H circle survives every E preparation.  The opposite
nonpositive outer order is literally unchanged by the G-only entry. -/
theorem NegativeGEntry.false_of_nonpositive_TD {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : NegativeGEntry q C w)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (hH : (C.point H).Contained q)
    (hDT : C.theta D≤C.theta T) : False := by
  have hD := J.unchanged D (by decide) (by decide) (by decide)
  have hT := J.unchanged T (by decide) (by decide) (by decide)
  have hJDT : J.target.cycle.theta D≤J.target.cycle.theta T := by
    rw [hD.2,hT.2]
    exact hDT
  have hcircle := J.target.nonpositive_outer_all_anchors_on hqL hqq
    J.aligned.symm.le hJDT
  exact circle_loss_impossible (hH.trans hqq) J.H_circle_loss
    (hcircle H (by simp [anchorVertices]))

/-- Every genuine G-negative primary with a nonpositive opposite outer
error is strictly above the sharp ceiling.  The actual original E may
have either boundary kind or any frame position. -/
theorem negative_g_nonpositive_TD_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hyG : (I.cycle.point G).y≤0) (hGA : I.cycle.Feasible G 1)
    (hnotGA : ¬I.cycle.Feasible G 0) (hBT : I.cycle.Feasible B 2)
    (hDT : I.cycle.theta D≤I.cycle.theta T) : False := by
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := aligned_negative_boundary_entry I hqL hcap hHG htG hyG hGA hnotGA hBT
  exact J.false_of_nonpositive_TD hqL hqq (I.necessary.contained H) hDT

/-- Both actual anchor losses are independently incompatible with the
hard sharp terminal.  In particular no source-circle equality is
assumed for the first transported H point. -/
theorem BothNegativeEntry.false {q : ℝ} {C : SignedCycle} {w : C.Witnesses}
    (J : BothNegativeEntry q C w) (hqL : qLow≤q) (hqq : q≤qStar)
    (hH : (C.point H).Contained q) : False := by
  have hcircle := J.target.nonpositive_outer_all_anchors_on hqL hqq
    J.HG_aligned.symm.le J.TD_aligned.le
  exact circle_loss_impossible (hH.trans hqq) J.H_circle_loss
    (hcircle H (by simp [anchorVertices]))

/-- Full G-negative/T-negative terminal exclusion at the source radius.
The original span and intermediate signs are proved by the entry, and
the contradiction is charged to the original H anchor. -/
theorem both_negative_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (htG : I.cycle.theta A<I.cycle.theta H)
    (hGA : I.cycle.Feasible G 1) (hnotGA : ¬I.cycle.Feasible G 0)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hBT : I.cycle.Feasible B 3) (hnotBT : ¬I.cycle.Feasible B 2) : False := by
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := both_negative_hard_entry I hqL hcap
    hHG htG hGA hnotGA hTD htT hBT hnotBT
  exact J.false hqL hqq (I.necessary.contained H)

end AlignedNegative

namespace DirectNegativeT

/-- The complete T entry keeps H/G point and frame data, so a previously
nonpositive HG error remains in the sharp nonpositive hard domain. -/
theorem HardTEntry.false_of_nonpositive_HG {q : ℝ} {C : SignedCycle}
    {w : C.Witnesses} (J : HardTEntry q C w)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (hD : (C.point D).Contained q)
    (hGH : C.theta G≤C.theta H) : False := by
  have hH := J.unchanged H (by decide) (by decide) (by decide)
  have hG := J.unchanged G (by decide) (by decide) (by decide)
  have hJGH : J.input.cycle.theta G≤J.input.cycle.theta H := by
    rw [hG.2,hH.2]
    exact hGH
  have hcircle := J.input.nonpositive_outer_all_anchors_on hqL hqq
    hJGH J.TD_aligned.ge
  exact circle_loss_impossible (hD.trans hqq) J.D_circle_loss
    (hcircle D (by simp [anchorVertices]))

/-- The G-hard/T-negative terminal is excluded on its actual D loss,
with no assumption on the original E position or middle frame. -/
theorem negative_t_nonpositive_HG_impossible {q : ℝ}
    (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqq : q≤qStar)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (htT : I.cycle.theta D<I.cycle.theta B)
    (hyT : 0≤(I.cycle.point T).y) (hBT : I.cycle.Feasible B 3)
    (hnotBT : ¬I.cycle.Feasible B 2) (hGA : I.cycle.Feasible G 0)
    (hGH : I.cycle.theta G≤I.cycle.theta H) : False := by
  have hcap : q≤qCap := hqq.trans qStar_limits.2.2.le
  obtain ⟨J⟩ := one_negative_t_entry I.necessary hqL hcap I.anchors_normal
    I.witnesses I.zero_signs I.E_nonpos (I.radial E)
    hTD htT hyT hBT hnotBT hGA
  exact J.false_of_nonpositive_HG hqL hqq (I.necessary.contained D) hGH

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
