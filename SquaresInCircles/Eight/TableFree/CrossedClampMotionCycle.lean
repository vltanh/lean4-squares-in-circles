module

public import SquaresInCircles.Eight.TableFree.CrossedClampMotion
public import SquaresInCircles.Eight.TableFree.CrossedClampEntry
public import SquaresInCircles.Eight.TableFree.CrossedClampCycle

/-!
# The common-frame clamp on the actual seven-point cycle

Uncompiled source draft.  Original HG, GA and BT contacts supply the
initial cap sum.  The signed TD charge and original endpoint budget
supply the invariant boundary budget.  The strict continuation produces
actual middle points at the first endpoint.  Reaching T first would
contradict the proved intermediate order on that actual descendant, so
the motion reaches H with both middle anchors strictly below q.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem HardOuterGeometry.common_clamp_motion {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap) (C : CommonFrameEntry I) :
    CrossedClampMotion.Data q (I.cycle.point H).y (I.cycle.point T).y
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta A-I.cycle.theta T) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let u := I.cycle.theta A-I.cycle.theta T
  have hr : r∈Ioc (0:ℝ) (1/25) := ⟨sub_pos.mpr C.H_before,C.short_error.le⟩
  have hu : u∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr C.T_before,(le_abs_self u).trans (I.necessary.spread A T)⟩
  have hri : r∈Icc (0:ℝ) (1/25) := ⟨hr.1.le,hr.2⟩
  have hui : u∈Icc 0 frameCap := ⟨hu.1.le,hu.2⟩
  have S : CrossedClampInverse.Domain q (I.cycle.point H).y :=
    ⟨hqL,hq,C.H_tangent⟩
  have hHG : zeroFeasible (I.cycle.point H) (I.cycle.point G) r 0 := by
    simpa [r,Feasible,slack,edge,word,delta,next,H,G,C.GA_aligned,
      zeroFeasible,sub_nonneg] using C.HG_zero
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) 0 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,C.GA_aligned,
      quarterFeasible,sub_nonneg] using I.GA_hard
  have hAcap := CrossedClampInverse.original_middle_cap S hri
    (I.necessary.sorted G) (I.necessary.contained G) C.G_nonpos
    (I.necessary.contained A) I.anchors_normal.A_nonneg hHG hGA
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-u) 2 := by
    rw [show -u=I.cycle.theta T-I.cycle.theta B by
      dsimp [u]; rw [←C.AB_aligned]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  have hBTref : quarterFeasible (I.cycle.point T).reflect
      (I.cycle.point B).reflect (-u) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ (-u) 2).2 hBT
  have hBTscalar := SignedOppositeHardEnvelope.negative_hard_contact hui hBTref
  simp only [SignedPoint.reflect,neg_neg] at hBTscalar
  have hcontact : 1/2+(I.cycle.point T).y≤
      ((I.cycle.point B).a+1/2-1)*Real.cos u-
        (-(I.cycle.point B).y+1/2)*Real.sin u := by
    convert hBTscalar using 1 <;> ring
  have hBcircle : ((I.cycle.point B).a+1/2)^2+
      (-(I.cycle.point B).y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonpos I.anchors_normal.B_nonpos] using I.necessary.contained B
  have hBfloor : 1/2≤ -(I.cycle.point B).y+1/2 := by
    linarith [I.anchors_normal.B_nonpos]
  have hB : MiddleHardCap.Feasible q (1/2+(I.cycle.point T).y) :=
    MiddleHardCap.feasible_of_contact hq (by linarith [C.T_positive]) hui
      hBfloor hcontact hBcircle
  have hBcap := MiddleHardCap.cap_majorizes hB hui
    (show 0≤ -(I.cycle.point B).y+1/2 by linarith) hcontact hBcircle
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal
    I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+charge*(r-u)<1-S0 := by
    dsimp [r,u,epsilon] at *
    linarith
  refine ⟨S,hB,hr,hu,C.T_positive.le,hBfloor.trans hBcap,?_,hbudget⟩
  linarith [C.tangent_sum]

/-- The unchanged H frame is reached by actual source points at q.
No artificial endpoint-order or contact-feasibility premise is needed. -/
theorem HardOuterGeometry.common_clamp_data {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap) (C : CommonFrameEntry I) :
    Nonempty (CrossedClampData q (I.cycle.point H) (I.cycle.point T) 0
      (I.cycle.theta H-I.cycle.theta T)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let u := I.cycle.theta A-I.cycle.theta T
  have M := I.common_clamp_motion hqL hq C
  change CrossedClampMotion.Data q (I.cycle.point H).y (I.cycle.point T).y r u at M
  have hm : 0<min r u := lt_min M.r_mem.1 M.u_mem.1
  obtain ⟨O⟩ := M.realize (show min r u∈Ioc 0 (min r u) from ⟨hm,le_rfl⟩)
  have hur : r<u := by
    by_contra! hle
    have hmin : min r u=u := min_eq_right hle
    have hβ : I.cycle.theta T∈Icc (I.cycle.theta H) (I.cycle.theta A) := by
      dsimp [r,u] at hle
      exact ⟨by linarith,C.T_before.le⟩
    have O' : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
        (I.cycle.theta T-I.cycle.theta H) (I.cycle.theta T-I.cycle.theta T) := by
      convert O using 1 <;> rw [hmin] <;> dsimp [r,u] <;> ring
    have hbad := I.crossedClamp_after_T hq hβ O'
    exact (lt_irrefl _ hbad)
  have hmin : min r u=r := min_eq_left hur.le
  refine ⟨?_⟩
  convert O using 1 <;> rw [hmin] <;> dsimp [r,u] <;> ring

end SquaresInCircles.Eight.TableFree.SignedCycle
