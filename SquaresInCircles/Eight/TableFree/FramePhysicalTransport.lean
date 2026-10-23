module

public import SquaresInCircles.Eight.TableFree.FrameConcentration

/-!
# Frame concentration at the original physical radius

The auxiliary circle is used only to prove the orientation-tour budget.
Its canonical angles agree exactly with those of the source cycle.  The
resulting lift and both signed variations therefore belong to the source
radius, source square records, and every original weak separating axis.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.FramePhysicalTransport
open Candidate

theorem canonical_eq {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (hR : RadiusExpansion C D) (i : Vertex) : D.canonicalAngle i=C.canonicalAngle i := by
  simp only [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,hR.same_rays,hR.same_tangents]

theorem charge_eq {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (hR : RadiusExpansion C D) :
    (∑ i,periodicFrameCost (D.canonicalAngle (next i)-D.canonicalAngle i))=
      ∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  simp only [canonical_eq hR]

theorem charge_budget_of_expansion {q : ℝ} {C : BoundaryCycle q}
    {D : BoundaryCycle Q0} (hR : RadiusExpansion C D) :
    (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425 := by
  rw [← charge_eq hR]
  exact FrameConcentration.charge_budget D

def auxiliary {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    BoundaryCycle Q0 :=
  C.expand ⟨hq.1,hq.2.trans (by norm_num [Q0])⟩ (by norm_num [Q0]) hq.2

theorem auxiliary_expansion {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    RadiusExpansion C (auxiliary C hq) :=
  C.expand_spec ⟨hq.1,hq.2.trans (by norm_num [Q0])⟩ (by norm_num [Q0]) hq.2

@[simp] theorem auxiliary_selected {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) : (auxiliary C hq).selected=C.selected := rfl

/-- The only radius transport used by G1 preserves every source owner. -/
theorem auxiliary_all_axes {q : ℝ} (C : BoundaryCycle q)
    (hq : q∈Icc (5/2:ℝ) Q0) (i : Vertex) (axis : SignedAxis)
    (ha : axis.Feasible (C.square i) (C.square (next i))) :
    axis.Feasible ((auxiliary C hq).square i) ((auxiliary C hq).square (next i)) :=
  (auxiliary_expansion C hq).preserves_all_axes i axis ha

theorem charge_budget {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425 :=
  charge_budget_of_expansion (auxiliary_expansion C hq)

theorem quarter_lift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    Nonempty (QuarterLift C) := by
  obtain ⟨F⟩ := FrameConcentration.quarter_lift (auxiliary C hq)
  exact ⟨F.pullback (auxiliary_expansion C hq)⟩

theorem lift_variations {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0)
    (F : QuarterLift C) :
    positiveVariation F.theta<frameCap ∧ negativeVariation F.theta<frameCap :=
  FrameConcentration.lift_variations_of_cost F (charge_budget C hq)

theorem concentrated {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    ∃ F : QuarterLift C,
      positiveVariation F.theta<frameCap ∧ negativeVariation F.theta<frameCap := by
  obtain ⟨F⟩ := quarter_lift C hq
  exact ⟨F,lift_variations C hq F⟩

def quarterPushforward {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : QuarterLift C) (hR : RadiusExpansion C D) : QuarterLift D where
  theta := F.theta
  quarter := F.quarter
  left := F.left
  diameter := F.diameter
  small := F.small
  theta_range := F.theta_range
  represents i := by
    change D.canonicalAngle i=_
    rw [canonical_eq hR]
    exact F.represents i

theorem quarterPushforward_word {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : QuarterLift C) (hR : RadiusExpansion C D)
    (hC : ∀ i,19/25<angleGap C.beta i) (hD : ∀ i,19/25<angleGap D.beta i) :
    (quarterPushforward F hR).word hD pi_lt_22_over_7=F.word hC pi_lt_22_over_7 := by
  funext i
  apply Fin.ext
  rfl

def candidatePushforward {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : Candidate.Frame C) (hR : RadiusExpansion C D) (hr : r≤Q0) : Candidate.Frame D where
  theta := F.theta
  theta_A := F.theta_A
  canonical_eq i := by rw [canonical_eq hR]; exact F.canonical_eq i
  spread := F.spread
  gap_lower i := by simpa only [hR.same_rays] using F.gap_lower i
  gap_upper i := by simpa only [hR.same_rays] using F.gap_upper i
  forward_complete := boundary_forward_complete D hr

theorem candidate_variations {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    positiveVariation (SignedCycle.atFrame F).theta<frameCap ∧
      negativeVariation (SignedCycle.atFrame F).theta<frameCap :=
  atFrame_variations_of_actual_cost F (charge_budget C hq)

/-- All the geometric and variation data concern the original q-cycle;
the normal-owner and anchor classifications are separate later theorems. -/
theorem original_signed_data {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    (SignedCycle.atFrame F).Necessary q ∧
    (SignedCycle.atFrame F).Ordered ∧
    (SignedCycle.atFrame F).StrictSpread ∧
    positiveVariation (SignedCycle.atFrame F).theta<frameCap ∧
    negativeVariation (SignedCycle.atFrame F).theta<frameCap ∧
    (∀ i,((SignedCycle.atFrame F).point i).Boundary q) ∧
    (∀ i,(SignedCycle.atFrame F).actualSquare i=C.square i) := by
  have hv := candidate_variations F hq
  exact ⟨SignedCycle.atFrame_necessary F,SignedCycle.atFrame_ordered F,
    SignedCycle.atFrame_strictSpread F,hv.1,hv.2,SignedCycle.atFrame_boundary F,
    SignedCycle.atFrame_actualSquare F⟩

theorem original_selected_owner {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) :
    C.selected i=forwardAxis (SignedCycle.retainedOwner F i) ∧
    (SignedCycle.atFrame F).Feasible i (SignedCycle.retainedOwner F i) ∧
    (forwardAxis (SignedCycle.retainedOwner F i)).normal
      ((SignedCycle.atFrame F).actualSquare i) ((SignedCycle.atFrame F).actualSquare (next i))=
        (C.selected i).normal (C.square i) (C.square (next i)) :=
  ⟨SignedCycle.retainedOwner_axis F i,SignedCycle.retainedOwner_feasible F i,
    SignedCycle.retainedOwner_normal F i⟩

theorem every_original_forward_owner {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (i : Vertex) (j : Fin 4) :
    (SignedCycle.atFrame F).Feasible i j ↔
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) :=
  SignedCycle.atFrame_feasible F i j

end SquaresInCircles.Eight.TableFree.FramePhysicalTransport
