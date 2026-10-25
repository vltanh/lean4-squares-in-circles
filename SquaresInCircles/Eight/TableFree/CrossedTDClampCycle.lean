module

public import SquaresInCircles.Eight.TableFree.CrossedClampCycle

/-!
# Reflecting the common-frame clamp back to the original TD side

Uncompiled source draft.  The reflected local output moves only T/A/B.
The original H/G/D/E and their frames remain literal source data, and
the original H/D/E budget remains valid.  Both actual middle circles
are strictly below q, independently of any earlier source deficits.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

structure CrossedTDClampData (q : ℝ) (G D : SignedPoint) (r u : ℝ) where
  pointT : SignedPoint
  pointA : SignedPoint
  pointB : SignedPoint
  T_sorted : pointT.Sorted
  T_avoids : pointT.AvoidsCore
  T_contained : pointT.Contained q
  T_nonneg : 0≤pointT.y
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_strict : pointA.circle<q
  A_nonneg : 0≤pointA.y
  B_sorted : pointB.Sorted
  B_avoids : pointB.AvoidsCore
  B_strict : pointB.circle<q
  B_nonpos : pointB.y≤0
  tangent_sum : pointA.y-pointB.y=1
  TD_two : zeroFeasible pointT D r 2
  BT_hard : quarterFeasible pointB pointT 0 2
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  GA_hard : quarterFeasible G pointA (-u) 0

def CrossedClampData.reflectTD {q r u : ℝ} {G D : SignedPoint}
    (O : CrossedClampData q D.reflect G.reflect r u) :
    CrossedTDClampData q G D r u where
  pointT := O.pointG.reflect
  pointA := O.pointB.reflect
  pointB := O.pointA.reflect
  T_sorted := by simpa using O.G_sorted
  T_avoids := by simpa using O.G_avoids
  T_contained := by simpa using O.G_contained
  T_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr O.G_nonpos
  A_sorted := by simpa using O.B_sorted
  A_avoids := by simpa using O.B_avoids
  A_strict := by simpa using O.B_strict
  A_nonneg := by simpa [SignedPoint.reflect] using neg_nonneg.mpr O.B_nonpos
  B_sorted := by simpa using O.A_sorted
  B_avoids := by simpa using O.A_avoids
  B_strict := by simpa using O.A_strict
  B_nonpos := by simpa [SignedPoint.reflect] using neg_nonpos.mpr O.A_nonneg
  tangent_sum := by
    dsimp [SignedPoint.reflect]
    linarith [O.tangent_sum]
  TD_two := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG r 0).2 O.HG_zero
  BT_hard := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointG O.pointA 0 0).2 O.GA_hard
  AB_zero := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect O.pointA O.pointB 0 2).2 O.AB_two
  AB_two := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect O.pointA O.pointB 0 0).2 O.AB_zero
  GA_hard := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointB G.reflect (-u) 2).2 O.BT_hard

namespace SignedCycle
open Candidate

def crossedTDClampCycle (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ) : SignedCycle where
  point := ![C.point H,C.point G,Q,R,P,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,β,β,β,C.theta D,C.theta E]

theorem crossedTDClampCycle_point_unchanged (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ)
    (i : Vertex) (hiT : i≠T) (hiA : i≠A) (hiB : i≠B) :
    (crossedTDClampCycle C P Q R β).point i=C.point i := by
  fin_cases i <;> simp [crossedTDClampCycle,H,G,A,B,T,D,E] at hiT hiA hiB ⊢

theorem crossedTDClampCycle_theta (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ) (i : Vertex) :
    (crossedTDClampCycle C P Q R β).theta i=
      if i=T ∨ i=A ∨ i=B then β else C.theta i := by
  fin_cases i <;> simp [crossedTDClampCycle,H,G,A,B,T,D,E]

theorem crossedTDClampCycle_spread {C : SignedCycle} (hC : C.Spread)
    (P Q R : SignedPoint) {β : ℝ} (hβ : β∈Icc (C.theta B) (C.theta D)) :
    (crossedTDClampCycle C P Q R β).Spread := by
  have hb (i : Vertex) : |β-C.theta i|≤frameCap := by
    have hB := abs_le.mp (hC B i)
    have hD := abs_le.mp (hC D i)
    apply abs_le.mpr
    constructor <;> linarith [hβ.1,hβ.2]
  intro i j
  rw [crossedTDClampCycle_theta,crossedTDClampCycle_theta]
  by_cases hi : i=T ∨ i=A ∨ i=B <;> by_cases hj : j=T ∨ j=A ∨ j=B
  · simp [hi,hj,frameCap]; norm_num
  · simpa [hi,hj] using hb j
  · simpa [hi,hj,abs_sub_comm] using hb i
  · simpa [hi,hj] using hC i j

def Witnesses.crossedTDClamp {q β : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (O : CrossedTDClampData q (C.point G) (C.point D)
      (C.theta D-β) (C.theta G-β)) :
    (crossedTDClampCycle C O.pointT O.pointA O.pointB β).Witnesses where
  owner i := if i=B ∨ i=T then 2 else if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,T] using w.feasible H
    · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,A,B,T,
        quarterFeasible,sub_nonneg,neg_sub] using O.GA_hard
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,A,B,T,hj,
          zeroFeasible,sub_nonneg] using O.AB_zero
      · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,A,B,T,hj,
          zeroFeasible,sub_nonneg] using O.AB_two
    · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,B,T,
        quarterFeasible,sub_nonneg] using O.BT_hard
    · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,B,T,D,
        zeroFeasible,sub_nonneg] using O.TD_two
    · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,B,T,D,E] using w.feasible D
    · simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,B,T,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=B ∨ i=T
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,G,B,T]
    by_cases hiG : i=G
    · subst i
      norm_num [normalOwners,G,B,T]
    · simpa [hi,hiG] using w.allowed i

def HardOuterGeometry.fromCrossedTDClamp {q β : ℝ} (I : HardOuterGeometry q)
    (hβ : β∈Icc (I.cycle.theta B) (I.cycle.theta D))
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-β) (I.cycle.theta G-β)) : HardOuterGeometry q where
  cycle := crossedTDClampCycle I.cycle O.pointT O.pointA O.pointB β
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact I.necessary.sorted G
      · exact O.A_sorted
      · exact O.B_sorted
      · exact O.T_sorted
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact I.necessary.contained G
      · exact O.A_strict.le
      · exact O.B_strict.le
      · exact O.T_contained
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact I.necessary.core G
      · exact O.A_avoids
      · exact O.B_avoids
      · exact O.T_avoids
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedTDClampCycle_spread I.necessary.spread O.pointT O.pointA O.pointB hβ }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := O.A_nonneg
    B_nonpos := O.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedTDClamp O
  GA_hard := by
    simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,G,A,
      quarterFeasible,sub_nonneg,neg_sub] using O.GA_hard
  BT_hard := by
    simpa [crossedTDClampCycle,Feasible,slack,edge,word,delta,next,B,T,
      quarterFeasible,sub_nonneg] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by
        simpa [Witnesses.crossedTDClamp,H,G,B,T] using hh
      exact I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      simp [Witnesses.crossedTDClamp,B,T] at hh }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

def HardInput.fromCrossedTDClamp {q β : ℝ} (I : HardInput q)
    (hβ : β∈Icc (I.cycle.theta B) (I.cycle.theta D))
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-β) (I.cycle.theta G-β)) : HardInput q where
  cycle := (I.outerGeometry.fromCrossedTDClamp hβ O).cycle
  necessary := (I.outerGeometry.fromCrossedTDClamp hβ O).necessary
  anchors_normal := (I.outerGeometry.fromCrossedTDClamp hβ O).anchors_normal
  E_nonpos := I.E_nonpos
  witnesses := (I.outerGeometry.fromCrossedTDClamp hβ O).witnesses
  GA_hard := (I.outerGeometry.fromCrossedTDClamp hβ O).GA_hard
  BT_hard := (I.outerGeometry.fromCrossedTDClamp hβ O).BT_hard
  zero_signs := (I.outerGeometry.fromCrossedTDClamp hβ O).zero_signs
  E_radial := I.E_radial

theorem HardOuterGeometry.fromCrossedTDClamp_preserves_loss {q β : ℝ}
    (I : HardOuterGeometry q) (hβ : β∈Icc (I.cycle.theta B) (I.cycle.theta D))
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-β) (I.cycle.theta G-β))
    (i : Vertex) (hi : i∈anchorVertices) (hloss : (I.cycle.point i).circle<q) :
    ((I.fromCrossedTDClamp hβ O).cycle.point i).circle<q := by
  by_cases hiA : i=A
  · subst i
    exact O.A_strict
  by_cases hiB : i=B
  · subst i
    exact O.B_strict
  have hiT : i≠T := by
    intro h
    subst i
    simp [anchorVertices,H,T,A,B,D,E] at hi
  change ((crossedTDClampCycle I.cycle O.pointT O.pointA O.pointB β).point i).circle<q
  rw [crossedTDClampCycle_point_unchanged I.cycle O.pointT O.pointA O.pointB β i hiT hiA hiB]
  exact hloss

theorem HardInput.fromCrossedTDClamp_preserves_loss {q β : ℝ}
    (I : HardInput q) (hβ : β∈Icc (I.cycle.theta B) (I.cycle.theta D))
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-β) (I.cycle.theta G-β))
    (i : Vertex) (hi : i∈anchorVertices) (hloss : (I.cycle.point i).circle<q) :
    ((I.fromCrossedTDClamp hβ O).cycle.point i).circle<q :=
  I.outerGeometry.fromCrossedTDClamp_preserves_loss hβ O i hi hloss

theorem HardOuterGeometry.crossedTDClamp_before_G {q β : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hβ : β∈Icc (I.cycle.theta B) (I.cycle.theta D))
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-β) (I.cycle.theta G-β)) : β<I.cycle.theta G :=
  (I.fromCrossedTDClamp hβ O).intermediate_order hq

theorem HardInput.fromCrossedTDClamp_properties {q β : ℝ}
    (I : HardInput q) (hβ : β∈Icc (I.cycle.theta B) (I.cycle.theta D))
    (O : CrossedTDClampData q (I.cycle.point G) (I.cycle.point D)
      (I.cycle.theta D-β) (I.cycle.theta G-β)) :
    let J := I.fromCrossedTDClamp hβ O
    J.cycle.theta T=β ∧ J.cycle.theta A=β ∧ J.cycle.theta B=β ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point A).circle<q ∧ (J.cycle.point B).circle<q ∧
      (∀ i,i≠T → i≠A → i≠B →
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  refine ⟨rfl,rfl,rfl,O.tangent_sum,O.A_strict,O.B_strict,?_⟩
  intro i hiT hiA hiB
  constructor
  · exact crossedTDClampCycle_point_unchanged I.cycle O.pointT O.pointA O.pointB β i hiT hiA hiB
  · change (crossedTDClampCycle I.cycle O.pointT O.pointA O.pointB β).theta i=I.cycle.theta i
    simp [crossedTDClampCycle_theta,hiT,hiA,hiB]

end SignedCycle
end SquaresInCircles.Eight.TableFree
