module

public import SquaresInCircles.Eight.Words.Crossed.BTOutput
public import SquaresInCircles.Eight.Owners.Hard.OuterGeometry

/-!
# Eight squares: the BT-side move at the original E

In `crossedBTCycle`, T moves to B's original frame and only the T and B points change. The
selected AB axis is kept at the common frame; the output selects BT2 and TD2
(`HardInput.fromCrossedBTData`). Every other original physical witness, the H, D and E points and
frames, and the strict endpoint budget carry over.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

def crossedBTCycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,C.point G,C.point A,Q,P,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,C.theta A,C.theta B,C.theta B,C.theta D,C.theta E]

theorem crossedBTCycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (crossedBTCycle C P Q).theta i=if i=T then C.theta B else C.theta i := by
  fin_cases i <;> simp [crossedBTCycle,H,G,A,B,T,D,E]

theorem crossedBTCycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (crossedBTCycle C P Q).Spread := by
  intro i j
  rw [crossedBTCycle_theta,crossedBTCycle_theta]
  by_cases hi : i=T <;> by_cases hj : j=T
  · simpa [hi,hj] using h B B
  · simpa [hi,hj] using h B j
  · simpa [hi,hj] using h i B
  · simpa [hi,hj] using h i j

def Witnesses.crossedBTData {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : CrossedBTData q (C.point B) (C.point T) (C.point D)
      (C.theta D-C.theta B) (C.theta B-C.theta T)) :
    (crossedBTCycle C O.pointT O.pointB).Witnesses where
  owner i := if i=B ∨ i=T then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,H,G,B,T] using w.feasible H
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,G,A,B,T] using w.feasible G
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      have hAB' : C.theta 3=C.theta 2 := hAB.symm
      have hBt : O.pointB.y=(C.point 3).y := O.B_tangent
      rcases hj with hj | hj <;>
        simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,A,B,T,
          hAB',hj,zeroProjection,hBt] using w.feasible A
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,
        quarterFeasible,sub_nonneg] using O.BT_hard
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
        zeroFeasible,sub_nonneg] using O.TD_two
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,E] using w.feasible D
    · simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=B ∨ i=T
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,B,T]
    · simpa [hi] using w.allowed i

def HardOuterGeometry.fromCrossedBTData {q : ℝ} (I : HardOuterGeometry q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) :
    HardOuterGeometry q where
  cycle := crossedBTCycle I.cycle O.pointT O.pointB
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact I.necessary.sorted G
      · exact I.necessary.sorted A
      · exact O.B_sorted
      · exact O.T_sorted
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact I.necessary.contained G
      · exact I.necessary.contained A
      · exact O.B_contained
      · exact O.T_contained
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact I.necessary.core G
      · exact I.necessary.core A
      · exact O.B_avoids
      · exact O.T_avoids
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedBTCycle_spread I.necessary.spread O.pointT O.pointB }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := by simpa [crossedBTCycle,B,O.B_tangent] using I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedBTData hAB O
  GA_hard := by
    simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,
      quarterFeasible,sub_nonneg] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by
        simpa [Witnesses.crossedBTData,H,T,B] using hh
      exact I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      simp [Witnesses.crossedBTData,B,T] at hh }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

def HardInput.fromCrossedBTData {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) :
    HardInput q where
  cycle := (I.outerGeometry.fromCrossedBTData hAB O).cycle
  necessary := (I.outerGeometry.fromCrossedBTData hAB O).necessary
  anchors_normal := (I.outerGeometry.fromCrossedBTData hAB O).anchors_normal
  E_nonpos := I.E_nonpos
  witnesses := (I.outerGeometry.fromCrossedBTData hAB O).witnesses
  GA_hard := (I.outerGeometry.fromCrossedBTData hAB O).GA_hard
  BT_hard := (I.outerGeometry.fromCrossedBTData hAB O).BT_hard
  zero_signs := (I.outerGeometry.fromCrossedBTData hAB O).zero_signs
  E_radial := I.E_radial

end SignedCycle
end SquaresInCircles.Eight
