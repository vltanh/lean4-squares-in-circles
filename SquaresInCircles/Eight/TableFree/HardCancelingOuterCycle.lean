module

public import SquaresInCircles.Eight.TableFree.HardCancelingOuter
public import SquaresInCircles.Eight.TableFree.HardMiddleAlignment

/-!
# Actual hard-cycle lifts of the two canceling outer alignments

Uncompiled draft.  These constructions use the original HG2 or TD0 axis
and retain the selected AB0/AB2 axis at the common middle frame.  Every
other selected witness is literally retained.  Only the free intermediate
and its adjacent middle anchor change, and strict loss is recorded on
that anchor's original circle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardCancelingOuter
namespace SignedCycle

def alignGACycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,P,Q,C.point B,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta H,C.theta A,C.theta B,C.theta T,C.theta D,C.theta E]

theorem alignGACycle_unchanged (C : SignedCycle) (P Q : SignedPoint)
    (i : Vertex) (hiG : i≠G) (hiA : i≠A) :
    (alignGACycle C P Q).point i=C.point i ∧
      (alignGACycle C P Q).theta i=C.theta i := by
  fin_cases i <;> simp [alignGACycle,H,G,A,B,T,D,E] at hiG hiA ⊢

theorem alignGACycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (alignGACycle C P Q).theta i=if i=G then C.theta H else C.theta i := by
  fin_cases i <;> simp [alignGACycle,H,G,A,B,T,D,E]

theorem alignGACycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (alignGACycle C P Q).Spread := by
  intro i j
  rw [alignGACycle_theta,alignGACycle_theta]
  by_cases hi : i=G <;> by_cases hj : j=G
  · simpa [hi,hj] using h H H
  · simpa [hi,hj] using h H j
  · simpa [hi,hj] using h i H
  · simpa [hi,hj] using h i j

def Witnesses.alignGA {q t : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : GAlignment q (C.point H) (C.point A)
      (C.theta H-C.theta A) t) :
    (alignGACycle C O.pointG O.pointA).Witnesses where
  owner i := if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · have hj : w.owner H=0 ∨ w.owner H=2 := by
        simpa [normalOwners,H] using w.allowed H
      rcases hj with hj | hj
      · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
          hj,zeroFeasible,sub_nonneg] using O.HG_zero
      · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
          hj,zeroFeasible,sub_nonneg] using O.HG_two
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
        quarterFeasible,sub_nonneg,neg_sub] using O.GA_hard
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj <;>
        simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,A,B,
          hAB,hj,zeroProjection,O.A_tangent] using w.feasible A
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,B,T] using w.feasible B
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,T,D] using w.feasible T
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,D,E] using w.feasible D
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=G
    · subst i; norm_num [normalOwners,G]
    · simpa [hi] using w.allowed i

def HardInput.fromCancelingHG {q t : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A) t) :
    HardInput q where
  cycle := alignGACycle I.cycle O.pointG O.pointA
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
      · exact O.A_circle.trans (I.necessary.contained A)
      · exact I.necessary.contained B
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_core.ge
      · exact O.A_avoids
      · exact I.necessary.core B
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := alignGACycle_spread I.necessary.spread O.pointG O.pointA }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := by simpa [alignGACycle,A,O.A_tangent] using I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.alignGA hAB O
  GA_hard := by
    simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
      quarterFeasible,sub_nonneg,neg_sub] using O.GA_hard
  BT_hard := by
    simpa [alignGACycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro _
      change O.pointG.y<0
      linarith [O.G_normal]
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.alignGA,T,G] using hh
      exact I.zero_signs.TD_canceling hj }
  E_radial := I.E_radial

theorem HardInput.canceling_HG_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 2) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A) (I.cycle.theta G-I.cycle.theta A)) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread H A
    refine ⟨by linarith,?_⟩
    dsimp [frameCap] at hh
    linarith [le_abs_self (I.cycle.theta H-I.cycle.theta A)]
  have ht : I.cycle.theta G-I.cycle.theta A∈
      Icc 0 (I.cycle.theta H-I.cycle.theta A) := by constructor <;> linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 2 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  exact actual_G_alignment hqL hq (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A) (I.necessary.contained H)
    (I.necessary.contained A) I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg
    hΘ ht hHG' hGA'

/-- A nonpositive canceling HG error is removed in the actual hard class.
The construction spends half its contact reserve on A's original circle. -/
theorem HardInput.align_nonpositive_HG2 {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 2) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta G<I.cycle.theta H → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.canceling_HG_output hqL hq hAG hGH hHG
  refine ⟨I.fromCancelingHG hAB O,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · exact hAB
  · exact O.A_tangent
  · intro i hi
    by_cases hiA : i=A
    · subst i; exact O.A_circle
    by_cases hiG : i=G
    · subst i; simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1).le
  · intro hstrict
    refine ⟨A,by simp [anchorVertices],?_⟩
    exact O.A_strict (by linarith)
  · intro i hi
    change (alignGACycle I.cycle O.pointG O.pointA).theta i=I.cycle.theta i
    simp [alignGACycle_theta,hi]
  · intro i hiG hiA
    exact (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1

def alignBTCycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,C.point G,C.point A,Q,P,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,C.theta A,C.theta B,C.theta D,C.theta D,C.theta E]

theorem alignBTCycle_unchanged (C : SignedCycle) (P Q : SignedPoint)
    (i : Vertex) (hiT : i≠T) (hiB : i≠B) :
    (alignBTCycle C P Q).point i=C.point i ∧
      (alignBTCycle C P Q).theta i=C.theta i := by
  fin_cases i <;> simp [alignBTCycle,H,G,A,B,T,D,E] at hiT hiB ⊢

theorem alignBTCycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (alignBTCycle C P Q).theta i=if i=T then C.theta D else C.theta i := by
  fin_cases i <;> simp [alignBTCycle,H,G,A,B,T,D,E]

theorem alignBTCycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (alignBTCycle C P Q).Spread := by
  intro i j
  rw [alignBTCycle_theta,alignBTCycle_theta]
  by_cases hi : i=T <;> by_cases hj : j=T
  · simpa [hi,hj] using h D D
  · simpa [hi,hj] using h D j
  · simpa [hi,hj] using h i D
  · simpa [hi,hj] using h i j

def Witnesses.alignBT {q t : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : TAlignment q (C.point B) (C.point D)
      (C.theta B-C.theta D) t) :
    (alignBTCycle C O.pointT O.pointB).Witnesses where
  owner i := if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,H,G] using w.feasible H
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,G,A] using w.feasible G
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj <;>
        simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,A,B,
          hAB,hj,zeroProjection,O.B_tangent] using w.feasible A
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
        quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
    · have hj : w.owner T=0 ∨ w.owner T=2 := by
        simpa [normalOwners,T] using w.allowed T
      rcases hj with hj | hj
      · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
          hj,zeroFeasible,sub_nonneg] using O.TD_zero
      · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
          hj,zeroFeasible,sub_nonneg] using O.TD_two
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,D,E] using w.feasible D
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=B
    · subst i; norm_num [normalOwners,B]
    · simpa [hi] using w.allowed i

def HardInput.fromCancelingTD {q t : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D) t) :
    HardInput q where
  cycle := alignBTCycle I.cycle O.pointT O.pointB
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
      · exact O.B_circle.trans (I.necessary.contained B)
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
      · exact O.T_core.ge
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := alignBTCycle_spread I.necessary.spread O.pointT O.pointB }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := by simpa [alignBTCycle,B,O.B_tangent] using I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.alignBT hAB O
  GA_hard := by
    simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
      quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.alignBT,H,B] using hh
      exact I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro _
      change 0<O.pointT.y
      linarith [O.T_normal] }
  E_radial := I.E_radial

theorem HardInput.canceling_TD_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 0) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D) (I.cycle.theta B-I.cycle.theta T)) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B D
    refine ⟨by linarith,?_⟩
    dsimp [frameCap] at hh
    linarith [le_abs_self (I.cycle.theta B-I.cycle.theta D)]
  have ht : I.cycle.theta B-I.cycle.theta T∈
      Icc 0 (I.cycle.theta B-I.cycle.theta D) := by constructor <;> linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 0 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  exact actual_T_alignment hqL hq (I.necessary.sorted B) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D) (I.necessary.contained B)
    (I.necessary.contained D) I.anchors_normal.B_nonpos I.anchors_normal.D_nonpos
    hΘ ht hBT' hTD'

/-- The exact TD0 dual, leaving H, G, A, D and E unchanged. -/
theorem HardInput.align_nonpositive_TD0 {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 0) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta D<I.cycle.theta T → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.canceling_TD_output hqL hq hDT hTB hTD
  refine ⟨I.fromCancelingTD hAB O,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · exact hAB
  · exact O.B_tangent
  · intro i hi
    by_cases hiB : i=B
    · subst i; exact O.B_circle
    by_cases hiT : i=T
    · subst i; simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1).le
  · intro hstrict
    refine ⟨B,by simp [anchorVertices],?_⟩
    exact O.B_strict (by linarith)
  · intro i hi
    change (alignBTCycle I.cycle O.pointT O.pointB).theta i=I.cycle.theta i
    simp [alignBTCycle_theta,hi]
  · intro i hiT hiB
    exact (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1

/-- The two independent actual reductions can be performed together.
Their losses are compared with the two separate original A/B circles. -/
theorem HardInput.align_nonpositive_canceling_outer {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 2) (hTD : I.cycle.Feasible T 0) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y-(J.cycle.point B).y=
        (I.cycle.point A).y-(I.cycle.point B).y ∧
      (J.cycle.point G).y< -(1/10 : ℝ) ∧ (1/10 : ℝ)<(J.cycle.point T).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta G<I.cycle.theta H ∨ I.cycle.theta D<I.cycle.theta T) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i∈({H,D,E} : Finset Vertex) →
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨OG⟩ := I.canceling_HG_output hqL hq hAG hGH hHG
  obtain ⟨OT⟩ := I.canceling_TD_output hqL hq hDT hTB hTD
  let K := I.fromCancelingHG hAB OG
  let J := K.fromCancelingTD hAB OT
  refine ⟨J,rfl,rfl,hAB,?_,OG.G_normal,OT.T_normal,?_,?_,?_⟩
  · change OG.pointA.y-OT.pointB.y=(I.cycle.point A).y-(I.cycle.point B).y
    rw [OG.A_tangent,OT.B_tangent]
  · intro i hi
    fin_cases i
    · exact le_rfl
    · simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact OG.A_circle
    · exact OT.B_circle
    · simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact le_rfl
    · exact le_rfl
  · rintro (hg | ht)
    · exact ⟨A,by simp [anchorVertices],OG.A_strict (by linarith)⟩
    · exact ⟨B,by simp [anchorVertices],OT.B_strict (by linarith)⟩
  · intro i hi
    fin_cases i <;> simp [H,G,A,B,T,D,E] at hi ⊢
    all_goals rfl

end SignedCycle
end SquaresInCircles.Eight.TableFree
