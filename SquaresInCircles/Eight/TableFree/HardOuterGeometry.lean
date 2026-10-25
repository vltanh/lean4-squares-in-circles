module

public import SquaresInCircles.Eight.TableFree.ZeroSignedCharge

/-!
# Reflection of the local hard geometry and its proved endpoint budget

Uncompiled source draft.  A full physical reflection reverses E's tangent.
The local outer arguments do not need a newly normalized E: they use only
the strict numerical H/D/E budget already proved on the actual source.
That budget is invariant under reflection.  This record retains the
necessary geometry, actual owners and hard axes together with that
derived inequality, and makes no assertion about the reflected E sign.
The eventual three-point output is reflected back before changing the
original hard cycle, so its original E and mixed witnesses stay fixed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

structure HardOuterGeometry (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  anchors_normal : cycle.NormalAnchors
  witnesses : cycle.Witnesses
  GA_hard : cycle.Feasible G 0
  BT_hard : cycle.Feasible B 2
  zero_signs : cycle.ZeroSignImplications witnesses
  endpoint_bound : q≤qCap →
    (cycle.point H).y-(cycle.point D).y-EndpointRotationPenalty.charge*(cycle.theta H-cycle.theta D)+S0<2-epsilon

/-- The local budget is proved from the original mixed witnesses before
the reflection.  It is not an additional assumption on a hard source. -/
def HardInput.outerGeometry {q : ℝ} (I : HardInput q) : HardOuterGeometry q where
  cycle := I.cycle
  necessary := I.necessary
  anchors_normal := I.anchors_normal
  witnesses := I.witnesses
  GA_hard := I.GA_hard
  BT_hard := I.BT_hard
  zero_signs := I.zero_signs
  endpoint_bound hq := SignedCycle.endpoint_budget hq I.necessary I.anchors_normal I.E_nonpos I.witnesses

def HardOuterGeometry.reflected {q : ℝ} (I : HardOuterGeometry q) :
    HardOuterGeometry q where
  cycle := I.cycle.reflected
  necessary := I.necessary.reflected
  anchors_normal := reflected_normal I.anchors_normal
  witnesses := I.witnesses.reflected
  GA_hard := by
    have hh := (reflected_feasible I.cycle G 2).2
      (by simpa [reflectedIndex,next,G,B] using I.BT_hard)
    simpa [reflectedOwner] using hh
  BT_hard := by
    have hh := (reflected_feasible I.cycle B 0).2
      (by simpa [reflectedIndex,next,B,G] using I.GA_hard)
    simpa [reflectedOwner] using hh
  zero_signs := {
    HG_canceling := by
      intro h
      have hT : I.witnesses.owner T=0 := by
        have hh : reflectedOwner (I.witnesses.owner T)=2 := by
          simpa [Witnesses.reflected,reflectedIndex,next,H,T] using h
        generalize I.witnesses.owner T=j at hh ⊢
        fin_cases j <;> simp_all [reflectedOwner]
      have hy := I.zero_signs.TD_canceling hT
      simpa [SignedCycle.reflected,reflectedIndex,G,T,SignedPoint.reflect]
        using neg_neg_of_pos hy
    TD_canceling := by
      intro h
      have hG : I.witnesses.owner H=2 := by
        have hh : reflectedOwner (I.witnesses.owner H)=0 := by
          simpa [Witnesses.reflected,reflectedIndex,next,H,T] using h
        generalize I.witnesses.owner H=j at hh ⊢
        fin_cases j <;> simp_all [reflectedOwner]
      have hy := I.zero_signs.HG_canceling hG
      simpa [SignedCycle.reflected,reflectedIndex,G,T,SignedPoint.reflect]
        using neg_pos.mpr hy }
  endpoint_bound := by
    intro hq
    have hh := I.endpoint_bound hq
    change -(I.cycle.point D).y-(-(I.cycle.point H).y)-
      EndpointRotationPenalty.charge*((I.cycle.theta B-I.cycle.theta D)-
        (I.cycle.theta B-I.cycle.theta H))+S0<2-epsilon
    linarith

end SquaresInCircles.Eight.TableFree.SignedCycle
