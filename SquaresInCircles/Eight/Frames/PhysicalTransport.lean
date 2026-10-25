module

public import SquaresInCircles.Eight.Boundary.Bridge
public import SquaresInCircles.Eight.Frames.Concentration

/-!
# Eight squares: frame concentration at the original physical radius

The auxiliary circle is used only to prove the orientation-tour budget.
Its canonical angles agree exactly with those of the source cycle.  The
resulting lift and both signed variations therefore belong to the source
radius, source square records, and every original weak separating axis.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.FramePhysicalTransport
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

theorem charge_budget {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425 :=
  charge_budget_of_expansion (auxiliary_expansion C hq)

theorem quarter_lift {q : ℝ} (C : BoundaryCycle q) (hq : q∈Icc (5/2:ℝ) Q0) :
    Nonempty (QuarterLift C) := by
  obtain ⟨F⟩ := FrameConcentration.quarter_lift (auxiliary C hq)
  exact ⟨F.pullback (auxiliary_expansion C hq)⟩

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

end SquaresInCircles.Eight.FramePhysicalTransport
