module

public import SquaresInCircles.Eight.Words.Crossed.GAOutput
public import SquaresInCircles.Eight.Owners.Hard.OuterGeometry

/-!
# Eight squares: lifting the crossed GA output to the hard cycle

In `crossedGACycle` only the G frame and the G and A points change. The original common AB frame
keeps its selected weak zero axis because A's tangent is fixed. HG0 and GA0 are the contacts of
the output (`HardInput.fromCrossedGAData`); all other selected physical axes and the original E
point are kept.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

def crossedGACycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,P,Q,C.point B,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta A,C.theta A,C.theta B,C.theta T,C.theta D,C.theta E]

theorem crossedGACycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (crossedGACycle C P Q).theta i=if i=G then C.theta A else C.theta i := by
  fin_cases i <;> simp [crossedGACycle,H,G,A,B,T,D,E]

theorem crossedGACycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (crossedGACycle C P Q).Spread := by
  intro i j
  rw [crossedGACycle_theta,crossedGACycle_theta]
  by_cases hi : i=G <;> by_cases hj : j=G
  · simpa [hi,hj] using h A A
  · simpa [hi,hj] using h A j
  · simpa [hi,hj] using h i A
  · simpa [hi,hj] using h i j

def Witnesses.crossedGAData {q : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : CrossedGAData q (C.point H) (C.point G) (C.point A)
      (C.theta A-C.theta H) (C.theta G-C.theta A)) :
    (crossedGACycle C O.pointG O.pointA).Witnesses where
  owner i := if i=H ∨ i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
        zeroFeasible,sub_nonneg] using O.HG_zero
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
        quarterFeasible,sub_nonneg] using O.GA_hard
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      have hAB' : C.theta 3=C.theta 2 := hAB.symm
      have hAt : O.pointA.y=(C.point 2).y := O.A_tangent
      rcases hj with hj | hj <;>
        simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
          hAB',hj,zeroProjection,hAt] using w.feasible A
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,B,T] using w.feasible B
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,T,D] using w.feasible T
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,D,E] using w.feasible D
    · simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,E] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=H ∨ i=G
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,H,G]
    · simpa [hi] using w.allowed i

def HardInput.fromCrossedGAData {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) : HardInput q where
  cycle := crossedGACycle I.cycle O.pointG O.pointA
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact I.necessary.sorted B
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_contained
      · exact I.necessary.contained B
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_avoids
      · exact O.A_avoids
      · exact I.necessary.core B
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedGACycle_spread I.necessary.spread O.pointG O.pointA }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := by simpa [crossedGACycle,A,O.A_tangent] using I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.crossedGAData hAB O
  GA_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
      quarterFeasible,sub_nonneg] using O.GA_hard
  BT_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      simp [Witnesses.crossedGAData,H,G] at hh
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.crossedGAData,H,T,G] using hh
      exact I.zero_signs.TD_canceling hj }
  E_radial := I.E_radial

/-- The same geometric move, before an E sign is chosen. Its strict endpoint budget is the
budget of the source: H, D and E, and their frames, have not moved. -/
def HardOuterGeometry.fromCrossedGAData {q : ℝ} (I : HardOuterGeometry q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) :
    HardOuterGeometry q where
  cycle := crossedGACycle I.cycle O.pointG O.pointA
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact I.necessary.sorted B
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_contained
      · exact I.necessary.contained B
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_avoids
      · exact O.A_avoids
      · exact I.necessary.core B
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedGACycle_spread I.necessary.spread O.pointG O.pointA }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := by simpa [crossedGACycle,A,O.A_tangent] using I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedGAData hAB O
  GA_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
      quarterFeasible,sub_nonneg] using O.GA_hard
  BT_hard := by
    simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      simp [Witnesses.crossedGAData,H,G] at hh
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by
        simpa [Witnesses.crossedGAData,H,T,G] using hh
      exact I.zero_signs.TD_canceling hj }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

end SignedCycle
end SquaresInCircles.Eight
