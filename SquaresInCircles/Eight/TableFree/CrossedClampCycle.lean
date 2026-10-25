module

public import SquaresInCircles.Eight.TableFree.CrossedClampData
public import SquaresInCircles.Eight.TableFree.HardOuterOrder

/-!
# Actual cycle realization of the crossed common-frame clamp

Uncompiled source draft.  G/A/B acquire the common frame inside the
original H/A interval.  H/T/D/E, their frames, and the retained TD/DE/EH
witnesses stay fixed.  The local invariant endpoint budget therefore
survives even after physical reflection.  Strict middle losses are at
the actual source q, independently of earlier deficits.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate

def crossedClampCycle (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ) : SignedCycle where
  point := ![C.point H,P,Q,R,C.point T,C.point D,C.point E]
  theta := ![C.theta H,β,β,β,C.theta T,C.theta D,C.theta E]

theorem crossedClampCycle_point_unchanged (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ)
    (i : Vertex) (hiG : i≠G) (hiA : i≠A) (hiB : i≠B) :
    (crossedClampCycle C P Q R β).point i=C.point i := by
  fin_cases i <;> simp [crossedClampCycle,H,G,A,B,T,D,E] at hiG hiA hiB ⊢

theorem crossedClampCycle_theta (C : SignedCycle) (P Q R : SignedPoint) (β : ℝ) (i : Vertex) :
    (crossedClampCycle C P Q R β).theta i=
      if i=G ∨ i=A ∨ i=B then β else C.theta i := by
  fin_cases i <;> simp [crossedClampCycle,H,G,A,B,T,D,E]

theorem crossedClampCycle_spread {C : SignedCycle} (hC : C.Spread)
    (P Q R : SignedPoint) {β : ℝ} (hβ : β∈Icc (C.theta H) (C.theta A)) :
    (crossedClampCycle C P Q R β).Spread := by
  have hb (i : Vertex) : |β-C.theta i|≤frameCap := by
    have hh := abs_le.mp (hC H i)
    have ha := abs_le.mp (hC A i)
    apply abs_le.mpr
    constructor <;> linarith [hβ.1,hβ.2]
  intro i j
  rw [crossedClampCycle_theta,crossedClampCycle_theta]
  by_cases hi : i=G ∨ i=A ∨ i=B <;> by_cases hj : j=G ∨ j=A ∨ j=B
  · simp [hi,hj,frameCap]; norm_num
  · simpa [hi,hj] using hb j
  · simpa [hi,hj,abs_sub_comm] using hb i
  · simpa [hi,hj] using hC i j

def Witnesses.crossedClamp {q β : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (O : CrossedClampData q (C.point H) (C.point T)
      (β-C.theta H) (β-C.theta T)) :
    (crossedClampCycle C O.pointG O.pointA O.pointB β).Witnesses where
  owner i := if i=H ∨ i=G then 0 else if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
        zeroFeasible,sub_nonneg] using O.HG_zero
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
        quarterFeasible,sub_nonneg] using O.GA_hard
    · have hj : w.owner 2=0 ∨ w.owner 2=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,hj,
          zeroFeasible,sub_nonneg] using O.AB_zero
      · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,A,B,hj,
          zeroFeasible,sub_nonneg] using O.AB_two
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,T,
        quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,T,D] using w.feasible T
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,D,E] using w.feasible D
    · simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,H,G,B,E] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=H ∨ i=G
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,H,G,B]
    by_cases hiB : i=B
    · subst i
      norm_num [normalOwners,H,G,B]
    · simpa [hi,hiB] using w.allowed i

def HardOuterGeometry.fromCrossedClamp {q β : ℝ} (I : HardOuterGeometry q)
    (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) : HardOuterGeometry q where
  cycle := crossedClampCycle I.cycle O.pointG O.pointA O.pointB β
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact O.B_sorted
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_strict.le
      · exact O.B_strict.le
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_avoids
      · exact O.A_avoids
      · exact O.B_avoids
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := crossedClampCycle_spread I.necessary.spread O.pointG O.pointA O.pointB hβ }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := O.A_nonneg
    B_nonpos := O.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  witnesses := I.witnesses.crossedClamp O
  GA_hard := by
    simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,G,A,
      quarterFeasible,sub_nonneg] using O.GA_hard
  BT_hard := by
    simpa [crossedClampCycle,Feasible,slack,edge,word,delta,next,B,T,
      quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      simp [Witnesses.crossedClamp,H,G] at hh
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by
        simpa [Witnesses.crossedClamp,H,G,B,T] using hh
      exact I.zero_signs.TD_canceling hj }
  endpoint_bound := by
    intro hq
    exact I.endpoint_bound hq

def HardInput.fromCrossedClamp {q β : ℝ} (I : HardInput q)
    (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) : HardInput q where
  cycle := (I.outerGeometry.fromCrossedClamp hβ O).cycle
  necessary := (I.outerGeometry.fromCrossedClamp hβ O).necessary
  anchors_normal := (I.outerGeometry.fromCrossedClamp hβ O).anchors_normal
  E_nonpos := I.E_nonpos
  witnesses := (I.outerGeometry.fromCrossedClamp hβ O).witnesses
  GA_hard := (I.outerGeometry.fromCrossedClamp hβ O).GA_hard
  BT_hard := (I.outerGeometry.fromCrossedClamp hβ O).BT_hard
  zero_signs := (I.outerGeometry.fromCrossedClamp hβ O).zero_signs
  E_radial := I.E_radial

theorem HardOuterGeometry.fromCrossedClamp_preserves_loss {q β : ℝ}
    (I : HardOuterGeometry q) (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T))
    (i : Vertex) (hi : i∈anchorVertices) (hloss : (I.cycle.point i).circle<q) :
    ((I.fromCrossedClamp hβ O).cycle.point i).circle<q := by
  by_cases hiA : i=A
  · subst i
    exact O.A_strict
  by_cases hiB : i=B
  · subst i
    exact O.B_strict
  have hiG : i≠G := by
    intro h
    subst i
    simp [anchorVertices,H,G,A,B,D,E] at hi
  change ((crossedClampCycle I.cycle O.pointG O.pointA O.pointB β).point i).circle<q
  rw [crossedClampCycle_point_unchanged I.cycle O.pointG O.pointA O.pointB β i hiG hiA hiB]
  exact hloss

theorem HardInput.fromCrossedClamp_preserves_loss {q β : ℝ}
    (I : HardInput q) (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T))
    (i : Vertex) (hi : i∈anchorVertices) (hloss : (I.cycle.point i).circle<q) :
    ((I.fromCrossedClamp hβ O).cycle.point i).circle<q :=
  I.outerGeometry.fromCrossedClamp_preserves_loss hβ O i hi hloss

/-- Any realized cap-sum state is still strictly above the unchanged T
frame.  In particular the continuation cannot reach T before H. -/
theorem HardOuterGeometry.crossedClamp_after_T {q β : ℝ}
    (I : HardOuterGeometry q) (hq : q≤qCap)
    (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) : I.cycle.theta T<β :=
  (I.fromCrossedClamp hβ O).intermediate_order hq

theorem HardInput.fromCrossedClamp_properties {q β : ℝ}
    (I : HardInput q) (hβ : β∈Icc (I.cycle.theta H) (I.cycle.theta A))
    (O : CrossedClampData q (I.cycle.point H) (I.cycle.point T)
      (β-I.cycle.theta H) (β-I.cycle.theta T)) :
    let J := I.fromCrossedClamp hβ O
    J.cycle.theta G=β ∧ J.cycle.theta A=β ∧ J.cycle.theta B=β ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point A).circle<q ∧ (J.cycle.point B).circle<q ∧
      (∀ i,i≠G → i≠A → i≠B →
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  refine ⟨rfl,rfl,rfl,O.tangent_sum,O.A_strict,O.B_strict,?_⟩
  intro i hiG hiA hiB
  constructor
  · exact crossedClampCycle_point_unchanged I.cycle O.pointG O.pointA O.pointB β i hiG hiA hiB
  · change (crossedClampCycle I.cycle O.pointG O.pointA O.pointB β).theta i=I.cycle.theta i
    simp [crossedClampCycle_theta,hiG,hiA,hiB]

end SquaresInCircles.Eight.TableFree.SignedCycle
