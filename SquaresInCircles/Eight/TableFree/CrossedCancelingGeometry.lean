module

public import SquaresInCircles.Eight.TableFree.CrossedCancelingConstruction
public import SquaresInCircles.Eight.TableFree.CrossedLargeConstruction
public import SquaresInCircles.Eight.TableFree.CrossedGACycle
public import SquaresInCircles.Eight.TableFree.WrongSignCapture

/-!
# Crossed large HG2 reduction on the actual hard source

Uncompiled source draft.  The original larger-middle sign theorem and
one-tenth opposite capture supply every sign bound used by the local
construction.  The new actual HG0 contact then enters the proved large
crossing capture at the same q.  Original H/B/T/D/E data and every
inherited anchor deficit are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate EndpointRotationPenalty EndpointBudgetScalars

theorem HardOuterGeometry.crossed_HG2_large_data {q : ℝ}
    (I : HardOuterGeometry q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 2)
    (hT : -(1/10:ℝ)<(I.cycle.point T).y) :
    Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  let r := I.cycle.theta A-I.cycle.theta H
  let z := I.cycle.theta G-I.cycle.theta A
  let u := I.cycle.theta A-I.cycle.theta T
  have hr : r∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hHA,(le_abs_self r).trans (I.necessary.spread A H)⟩
  have hz : z∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hAG,(le_abs_self z).trans (I.necessary.spread G A)⟩
  have hu : u∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hTA,(le_abs_self u).trans (I.necessary.spread A T)⟩
  have hspan : z+r≤frameCap := by
    have hh := (le_abs_self (I.cycle.theta G-I.cycle.theta H)).trans (I.necessary.spread G H)
    dsimp [z,r]
    linarith
  have hG := I.large_middle_G_negative hq hAB hnorm hTA hAG hlarge
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) (z+r) 2 := by
    convert hHG using 1 <;>
      simp [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,z,r] <;> ring
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-z) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,z] using I.GA_hard
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T) (-u) 2 := by
    rw [show -u=I.cycle.theta T-I.cycle.theta B by dsimp [u]; rw [←hAB]; ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible] using I.BT_hard
  have hTD := (signed_outer_charges hq I.necessary I.anchors_normal I.witnesses I.zero_signs).2
  have hep := I.endpoint_bound hq
  have hbudget : (I.cycle.point H).y-(I.cycle.point T).y+EndpointRotationPenalty.charge*(r-u)<1-S0 := by
    dsimp [r,u,epsilon] at *
    linarith
  exact CrossedCancelingConstruction.actual_output hqL hq
    (I.necessary.sorted H) (I.necessary.sorted A) (I.necessary.sorted B)
    (I.necessary.core A) (I.necessary.contained H) (I.necessary.contained A)
    (I.necessary.contained B) I.anchors_normal.H_nonneg hlarge I.anchors_normal.B_nonpos
    hG.le hT hnorm hr hz hu hspan hHG' hGA' hBT' hbudget

theorem HardInput.crossed_HG2_large_output {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hHA : I.cycle.theta H<I.cycle.theta A)
    (hlarge : 1/2≤(I.cycle.point A).y) (hHG : I.cycle.Feasible H 2) :
    I.cycle.theta A-I.cycle.theta H<1/25 ∧
      Nonempty (CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
        (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) := by
  obtain ⟨O⟩ := I.outerGeometry.crossed_HG2_large_data hqL hq hAB hnorm hTA hAG hHA
    hlarge hHG (I.small_intermediate_signs hq).2
  let J := I.fromCrossedGAData hAB O
  have hAB' : J.cycle.theta A=J.cycle.theta B := hAB
  have hsum' : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change O.pointA.y-(I.cycle.point B).y=1
    rw [O.A_tangent]
    exact hnorm
  have hlarge' : 1/2≤(J.cycle.point A).y := by
    change 1/2≤O.pointA.y
    rw [O.A_tangent]
    exact hlarge
  have hHG' : J.cycle.Feasible H 0 := by
    simpa [J,HardInput.fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,
      delta,next,H,G,A,zeroFeasible,HardInput.outerGeometry] using O.HG_zero
  have hcap := J.crossed_HG0_large_reserve hqL hq hAB' hsum' hTA le_rfl hHA.le hlarge' hHG'
  exact ⟨hcap.1,⟨O⟩⟩

end SquaresInCircles.Eight.TableFree.SignedCycle
