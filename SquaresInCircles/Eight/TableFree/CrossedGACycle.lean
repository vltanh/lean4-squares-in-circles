module

public import SquaresInCircles.Eight.TableFree.CrossedGAOutput

/-!
# Lifting the crossed GA output to the actual hard cycle

Uncompiled source draft.  Only the G frame and the G/A points change.
The original common AB frame retains its selected weak zero axis because
A's tangent is fixed.  HG0 and GA0 are the actual proved output contacts;
all other selected physical axes and the original E point are retained.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

def crossedGACycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,P,Q,C.point B,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta A,C.theta A,C.theta B,C.theta T,C.theta D,C.theta E]

theorem crossedGACycle_point_unchanged (C : SignedCycle) (P Q : SignedPoint)
    (i : Vertex) (hiG : i≠G) (hiA : i≠A) :
    (crossedGACycle C P Q).point i=C.point i := by
  fin_cases i <;> simp [crossedGACycle,H,G,A,B,T,D,E] at hiG hiA ⊢

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
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj <;>
        simpa [crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,B,
          hAB,hj,zeroProjection,O.A_tangent] using w.feasible A
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

def HardInput.fromCrossedGA {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) : HardInput q :=
  I.fromCrossedGAData hAB O.toCrossedGAData

theorem HardInput.fromCrossedGAData_preserves_loss {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A))
    (i : Vertex) (hi : i∈anchorVertices) (hbelow : (I.cycle.point i).circle<q) :
    ((I.fromCrossedGAData hAB O).cycle.point i).circle<q := by
  by_cases hiA : i=A
  · subst i
    exact O.A_loss hbelow
  have hiG : i≠G := by
    intro h
    subst i
    simp [anchorVertices,H,G,A,B,D,E] at hi
  change ((crossedGACycle I.cycle O.pointG O.pointA).point i).circle<q
  rw [crossedGACycle_point_unchanged I.cycle O.pointG O.pointA i hiG hiA]
  exact hbelow

theorem HardInput.fromCrossedGAData_strict_A {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAData q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A))
    (hmove : I.cycle.theta A<I.cycle.theta G) :
    ((I.fromCrossedGAData hAB O).cycle.point A).circle<q :=
  O.A_strict (sub_pos.mpr hmove)

theorem HardInput.fromCrossedGA_GA_aligned {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A)) :
    (I.fromCrossedGA hAB O).cycle.theta G=(I.fromCrossedGA hAB O).cycle.theta A ∧
      (I.fromCrossedGA hAB O).cycle.theta A=(I.fromCrossedGA hAB O).cycle.theta B ∧
      (I.fromCrossedGA hAB O).cycle.Feasible H 0 := by
  refine ⟨rfl,hAB,?_⟩
  simpa [fromCrossedGA,fromCrossedGAData,crossedGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
    zeroFeasible,sub_nonneg] using O.HG_zero

theorem HardInput.fromCrossedGA_preserves_loss {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A))
    (i : Vertex) (hi : i∈anchorVertices) (hbelow : (I.cycle.point i).circle<q) :
    ((I.fromCrossedGA hAB O).cycle.point i).circle<q := by
  by_cases hiA : i=A
  · subst i
    exact O.A_loss hbelow
  have hiG : i≠G := by
    intro h
    subst i
    simp [anchorVertices,H,G,A,B,D,E] at hi
  change ((crossedGACycle I.cycle O.pointG O.pointA).point i).circle<q
  rw [crossedGACycle_point_unchanged I.cycle O.pointG O.pointA i hiG hiA]
  exact hbelow

theorem HardInput.fromCrossedGA_strict_A {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A))
    (hmove : I.cycle.theta A<I.cycle.theta G) :
    ((I.fromCrossedGA hAB O).cycle.point A).circle<q :=
  O.A_strict (sub_pos.mpr hmove)

theorem HardInput.fromCrossedGA_at_zero {q : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : CrossedGAOutput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta H) (I.cycle.theta G-I.cycle.theta A))
    (hzero : I.cycle.theta G=I.cycle.theta A) : (I.fromCrossedGA hAB O).cycle=I.cycle := by
  obtain ⟨hG,hA⟩ := O.at_zero (sub_eq_zero.mpr hzero)
  have hp : (I.fromCrossedGA hAB O).cycle.point=I.cycle.point := by
    funext i
    fin_cases i <;> simp [fromCrossedGA,fromCrossedGAData,crossedGACycle,hG,hA,H,G,A,B,T,D,E]
  have ht : (I.fromCrossedGA hAB O).cycle.theta=I.cycle.theta := by
    funext i
    fin_cases i <;> simp [fromCrossedGA,fromCrossedGAData,crossedGACycle,hzero,H,G,A,B,T,D,E]
  exact congrArg₂ SignedCycle.mk hp ht

end SignedCycle
end SquaresInCircles.Eight.TableFree
