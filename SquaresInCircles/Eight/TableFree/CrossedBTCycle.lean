module

public import SquaresInCircles.Eight.TableFree.CrossedBTOutput
public import SquaresInCircles.Eight.TableFree.CrossedGACycle

/-!
# The actual BT-side replacement at the original E

Uncompiled source draft.  T moves to B's original frame and only T/B
points change.  The selected AB axis is retained at the common frame;
the proved output selects BT2 and TD2.  Every other original physical
witness, H/D/E point and frame, and the strict endpoint budget survives.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

def crossedBTCycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,C.point G,C.point A,Q,P,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,C.theta A,C.theta B,C.theta B,C.theta D,C.theta E]

theorem crossedBTCycle_point_unchanged (C : SignedCycle) (P Q : SignedPoint)
    (i : Vertex) (hiT : i≠T) (hiB : i≠B) :
    (crossedBTCycle C P Q).point i=C.point i := by
  fin_cases i <;> simp [crossedBTCycle,H,G,A,B,T,D,E] at hiT hiB ⊢

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

def HardInput.fromCrossedBT {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTOutput q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) : HardInput q :=
  I.fromCrossedBTData hAB O.toCrossedBTData

theorem HardOuterGeometry.fromCrossedBTData_preserves_loss {q : ℝ}
    (I : HardOuterGeometry q) (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T))
    (i : Vertex) (hi : i∈anchorVertices) (hbelow : (I.cycle.point i).circle<q) :
    ((I.fromCrossedBTData hAB O).cycle.point i).circle<q := by
  by_cases hiB : i=B
  · subst i
    exact O.B_loss hbelow
  have hiT : i≠T := by
    intro h
    subst i
    simp [anchorVertices,H,T,A,B,D,E] at hi
  change ((crossedBTCycle I.cycle O.pointT O.pointB).point i).circle<q
  rw [crossedBTCycle_point_unchanged I.cycle O.pointT O.pointB i hiT hiB]
  exact hbelow

theorem HardInput.fromCrossedBTData_preserves_loss {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T))
    (i : Vertex) (hi : i∈anchorVertices) (hbelow : (I.cycle.point i).circle<q) :
    ((I.fromCrossedBTData hAB O).cycle.point i).circle<q :=
  I.outerGeometry.fromCrossedBTData_preserves_loss hAB O i hi hbelow

theorem HardInput.fromCrossedBTData_strict_B {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T))
    (hmove : I.cycle.theta T<I.cycle.theta B) :
    ((I.fromCrossedBTData hAB O).cycle.point B).circle<q :=
  O.B_strict (sub_pos.mpr hmove)

theorem HardInput.fromCrossedBTData_BT_aligned {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTData q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T)) :
    (I.fromCrossedBTData hAB O).cycle.theta T=(I.fromCrossedBTData hAB O).cycle.theta B ∧
      (I.fromCrossedBTData hAB O).cycle.theta A=(I.fromCrossedBTData hAB O).cycle.theta B ∧
      (I.fromCrossedBTData hAB O).cycle.Feasible T 2 := by
  refine ⟨rfl,hAB,?_⟩
  simpa [fromCrossedBTData,HardOuterGeometry.fromCrossedBTData,
    HardInput.outerGeometry,crossedBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
    zeroFeasible,sub_nonneg] using O.TD_two

theorem HardInput.fromCrossedBT_at_zero {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedBTOutput q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta B) (I.cycle.theta B-I.cycle.theta T))
    (hzero : I.cycle.theta B=I.cycle.theta T) : (I.fromCrossedBT hAB O).cycle=I.cycle := by
  obtain ⟨hT,hB⟩ := O.at_zero (sub_eq_zero.mpr hzero)
  have hp : (I.fromCrossedBT hAB O).cycle.point=I.cycle.point := by
    funext i
    fin_cases i <;>
      simp [fromCrossedBT,fromCrossedBTData,HardOuterGeometry.fromCrossedBTData,
        HardInput.outerGeometry,crossedBTCycle,hT,hB,H,G,A,B,T,D,E]
  have hz : I.cycle.theta 3=I.cycle.theta 4 := hzero
  have ht : (I.fromCrossedBT hAB O).cycle.theta=I.cycle.theta := by
    funext i
    fin_cases i <;>
      simp [fromCrossedBT,fromCrossedBTData,HardOuterGeometry.fromCrossedBTData,
        HardInput.outerGeometry,crossedBTCycle,hz,H,G,A,B,T,D,E]
  exact congrArg₂ SignedCycle.mk hp ht

end SignedCycle
end SquaresInCircles.Eight.TableFree
