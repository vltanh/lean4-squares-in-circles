module

public import SquaresInCircles.Eight.TableFree.HardSplitLoss
public import SquaresInCircles.Eight.TableFree.NecessaryCycle

/-!
# Applying the hard split to the actual necessary seven-cycle

Uncompiled draft.  The three zero-edge alignments and the position of the
common A/B frame are explicit source hypotheses.  From them the original
HG and TD witnesses force the transverse bounds required by the cap
construction.  The move retains H,G,T,D,E, all four unaffected neighboring
witnesses, and the actual radius.  Interior strictness is charged to A and
B, which are anchors.

This is the concrete aligned-pair gate inside the hard reduction.  It does
not infer the source alignments from an unrestricted `HardInput`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate HardSplitCap
namespace SignedCycle

def replaceMiddle (C : SignedCycle) (P R : SignedPoint) (β : ℝ) : SignedCycle where
  point := ![C.point H,C.point G,P,R,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,β,β,C.theta T,C.theta D,C.theta E]

theorem replaceMiddle_unchanged (C : SignedCycle) (P R : SignedPoint) (β : ℝ)
    (i : Vertex) (hi : i ≠ A) (hj : i ≠ B) :
    (replaceMiddle C P R β).point i=C.point i ∧
      (replaceMiddle C P R β).theta i=C.theta i := by
  fin_cases i <;> simp_all [replaceMiddle,H,G,A,B,T,D,E]

theorem replaceMiddle_spread {C : SignedCycle} {P R : SignedPoint} {β : ℝ}
    (h : C.Spread) (hβ : β=C.theta G ∨ β=C.theta T) :
    (replaceMiddle C P R β).Spread := by
  have hf (i : Vertex) : (replaceMiddle C P R β).theta i=
      if i=A ∨ i=B then β else C.theta i := by
    fin_cases i <;> simp [replaceMiddle,H,G,A,B,T,D,E]
  rcases hβ with hβ | hβ
  · intro i j
    rw [hf i,hf j,hβ]
    split_ifs <;> exact h _ _
  · intro i j
    rw [hf i,hf j,hβ]
    split_ifs <;> exact h _ _

theorem replaceMiddle_unaffected {C : SignedCycle} {P R : SignedPoint} {β : ℝ}
    {i : Vertex} (hi : i=H ∨ i=T ∨ i=D ∨ i=E) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible i j ↔ C.Feasible i j := by
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem replaceMiddle_slack_unaffected {C : SignedCycle} {P R : SignedPoint} {β : ℝ}
    {i : Vertex} (hi : i=H ∨ i=T ∨ i=D ∨ i=E) (j : Fin 4) :
    (replaceMiddle C P R β).slack i j=C.slack i j := by
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem replaceMiddle_GA (C : SignedCycle) (P R : SignedPoint) (β : ℝ) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible G j ↔
      quarterFeasible (C.point G) P (β-C.theta G) j := by
  simp [Feasible,slack,edge,replaceMiddle,Candidate.word,next,delta,G,A,
    quarterFeasible,sub_nonneg]

theorem replaceMiddle_BT (C : SignedCycle) (P R : SignedPoint) (β : ℝ) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible B j ↔
      quarterFeasible R (C.point T) (C.theta T-β) j := by
  simp [Feasible,slack,edge,replaceMiddle,Candidate.word,next,delta,B,T,
    quarterFeasible,sub_nonneg]

theorem replaceMiddle_AB (C : SignedCycle) (P R : SignedPoint) (β : ℝ) (j : Fin 4) :
    (replaceMiddle C P R β).Feasible A j ↔ zeroFeasible P R 0 j := by
  simp [Feasible,slack,edge,replaceMiddle,Candidate.word,next,delta,A,B,
    zeroFeasible,sub_nonneg]

def Witnesses.replaceMiddle {C : SignedCycle} (w : C.Witnesses)
    (P R : SignedPoint) (β : ℝ)
    (hGA : quarterFeasible (C.point G) P (β-C.theta G) 0)
    (hBT : quarterFeasible R (C.point T) (C.theta T-β) 2)
    (hAB0 : zeroFeasible P R 0 0) (hAB2 : zeroFeasible P R 0 2) :
    (SignedCycle.replaceMiddle C P R β).Witnesses where
  owner := ![w.owner H,0,w.owner A,2,w.owner T,w.owner D,w.owner E]
  feasible := by
    intro i
    fin_cases i
    · exact (replaceMiddle_unaffected (Or.inl rfl) _).2 (w.feasible H)
    · exact (replaceMiddle_GA C P R β 0).2 hGA
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      rcases hj with hj | hj
      · exact (replaceMiddle_AB C P R β _).2 (by simpa [hj] using hAB0)
      · exact (replaceMiddle_AB C P R β _).2 (by simpa [hj] using hAB2)
    · exact (replaceMiddle_BT C P R β 2).2 hBT
    · exact (replaceMiddle_unaffected (Or.inr (Or.inl rfl)) _).2 (w.feasible T)
    · exact (replaceMiddle_unaffected (Or.inr (Or.inr (Or.inl rfl))) _).2 (w.feasible D)
    · exact (replaceMiddle_unaffected (Or.inr (Or.inr (Or.inr rfl))) _).2 (w.feasible E)
  allowed := by
    intro i
    fin_cases i
    · exact w.allowed H
    · norm_num [normalOwners,G]
    · exact w.allowed A
    · norm_num [normalOwners,B]
    · exact w.allowed T
    · exact w.allowed D
    · exact w.allowed E

def HardInput.replaceMiddle {q : ℝ} (I : HardInput q)
    (P R : SignedPoint) (β : ℝ)
    (hβ : β=I.cycle.theta G ∨ β=I.cycle.theta T)
    (hsP : P.Sorted) (hsR : R.Sorted)
    (hcP : P.AvoidsCore) (hcR : R.AvoidsCore)
    (hnP : 0 ≤ P.y) (hnR : R.y ≤ 0)
    (hqP : P.circle ≤ (I.cycle.point A).circle)
    (hqR : R.circle ≤ (I.cycle.point B).circle)
    (hGA : quarterFeasible (I.cycle.point G) P (β-I.cycle.theta G) 0)
    (hBT : quarterFeasible R (I.cycle.point T) (I.cycle.theta T-β) 2)
    (hAB0 : zeroFeasible P R 0 0) (hAB2 : zeroFeasible P R 0 2) : HardInput q where
  cycle := SignedCycle.replaceMiddle I.cycle P R β
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact I.necessary.sorted G
      · exact hsP
      · exact hsR
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact I.necessary.contained G
      · exact hqP.trans (I.necessary.contained A)
      · exact hqR.trans (I.necessary.contained B)
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact I.necessary.core G
      · exact hcP
      · exact hcR
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := replaceMiddle_spread I.necessary.spread hβ }
  anchors_normal := ⟨I.anchors_normal.H_nonneg,hnP,hnR,I.anchors_normal.D_nonpos⟩
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.replaceMiddle P R β hGA hBT hAB0 hAB2
  GA_hard := (replaceMiddle_GA I.cycle P R β 0).2 hGA
  BT_hard := (replaceMiddle_BT I.cycle P R β 2).2 hBT
  zero_signs := {
    HG_canceling := by intro h; exact I.zero_signs.HG_canceling h
    TD_canceling := by intro h; exact I.zero_signs.TD_canceling h }
  E_radial := I.E_radial

/-- At the three actual aligned zero edges, either original transverse
owner has the same projection.  The outer anchors need only containment. -/
theorem HardInput.aligned_pair_bounds {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D) :
    (I.cycle.point G).y < -(1/10 : ℝ) ∧
      (1/10 : ℝ) < (I.cycle.point T).y ∧
      zeroFeasible (I.cycle.point A) (I.cycle.point B) 0 0 := by
  have hHGw : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      (I.cycle.theta G-I.cycle.theta H) (I.witnesses.owner H) := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,H,G,zeroFeasible,sub_nonneg]
      using I.witnesses.feasible H
  have hTDw : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta T) (I.witnesses.owner T) := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,T,D,zeroFeasible,sub_nonneg]
      using I.witnesses.feasible T
  have hABw : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) (I.witnesses.owner A) := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,A,B,zeroFeasible,sub_nonneg]
      using I.witnesses.feasible A
  rw [hHG,sub_self] at hHGw
  rw [hTD,sub_self] at hTDw
  rw [hAB,sub_self] at hABw
  have hHowner : I.witnesses.owner H=0 ∨ I.witnesses.owner H=2 := by
    simpa [normalOwners,H] using I.witnesses.allowed H
  have hTowner : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
    simpa [normalOwners,T] using I.witnesses.allowed T
  have hAowner : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hHsep : 1 ≤ (I.cycle.point H).y-(I.cycle.point G).y := by
    rcases hHowner with hj | hj <;>
      simpa [hj,zeroFeasible,zeroProjection] using hHGw
  have hTsep : 1 ≤ (I.cycle.point T).y-(I.cycle.point D).y := by
    rcases hTowner with hj | hj <;>
      simpa [hj,zeroFeasible,zeroProjection] using hTDw
  have hHbound := (SignedPoint.coordinate_bounds (I.necessary.sorted H)
    (I.necessary.core H) (I.necessary.contained H) hq).2.2
  have hDbound := (SignedPoint.coordinate_bounds (I.necessary.sorted D)
    (I.necessary.core D) (I.necessary.contained D) hq).2.2
  refine ⟨?_,?_,?_⟩
  · linarith [le_abs_self (I.cycle.point H).y]
  · linarith [neg_le_abs (I.cycle.point D).y]
  · rcases hAowner with hj | hj <;>
      simpa [hj,zeroFeasible,zeroProjection] using hABw

theorem HardInput.aligned_pair_endpoint {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A ≤ I.cycle.theta G)
    (hright : I.cycle.theta T ≤ I.cycle.theta A) :
    Nonempty (HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) := by
  obtain ⟨hyG,hyT,hABw⟩ := I.aligned_pair_bounds hq hHG hAB hTD
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,G,A,
      quarterFeasible,sub_nonneg,neg_sub] using I.GA_hard
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta A-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,next,delta,B,T,hAB,
      quarterFeasible,sub_nonneg,neg_sub] using I.BT_hard
  have hspan : (I.cycle.theta G-I.cycle.theta A)+
      (I.cycle.theta A-I.cycle.theta T) ≤ 7/10 := by
    have hh := I.necessary.spread G T
    have ha := le_abs_self (I.cycle.theta G-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  exact actual_pair_endpoint ((I.necessary.contained A).trans hq)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyG.le hyT.le (sub_nonneg.mpr hleft)
    (sub_nonneg.mpr hright) hspan hGA hBT hABw

private theorem pair_endpoint_frames (C : SignedCycle)
    (O : HardSplitCap.PairEndpoint (C.point G) (C.point A) (C.point B) (C.point T)
      (C.theta G-C.theta A) (C.theta A-C.theta T)) :
    (C.theta G-O.angleA=C.theta G ∨ C.theta G-O.angleA=C.theta T) ∧
      (C.theta G-O.angleA)-C.theta G= -O.angleA ∧
      C.theta T-(C.theta G-O.angleA)= -O.angleB := by
  refine ⟨?_,by ring,?_⟩
  · rcases O.endpoint with h | h
    · left; linarith [h.1]
    · right; linarith [h.1]
  · linarith [O.span]

/-- Put the new common A/B frame at the selected original G/T frame.
Every other point and frame remains literally the source point and frame. -/
def HardInput.fromPair {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    HardInput q := by
  let hf := pair_endpoint_frames I.cycle O
  refine I.replaceMiddle O.pointA O.pointB (I.cycle.theta G-O.angleA) hf.1
    O.sorted_A O.sorted_B O.avoids_A O.avoids_B O.normal_A.le O.normal_B.le
    O.circle_A.le O.circle_B.le ?_ ?_ O.AB_zero O.AB_two
  · unfold quarterFeasible
    rw [hf.2.1]
    exact O.GA_exact.symm.le
  · unfold quarterFeasible
    rw [hf.2.2]
    exact O.BT_exact.symm.le

theorem HardInput.fromPair_unchanged {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    (i : Vertex) (hi : i ≠ A) (hj : i ≠ B) :
    ((I.fromPair O).cycle.point i=I.cycle.point i) ∧
      ((I.fromPair O).cycle.theta i=I.cycle.theta i) :=
  replaceMiddle_unchanged I.cycle O.pointA O.pointB (I.cycle.theta G-O.angleA) i hi hj

theorem HardInput.fromPair_circles {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    (i : Vertex) : ((I.fromPair O).cycle.point i).circle=(I.cycle.point i).circle := by
  fin_cases i
  · rfl
  · rfl
  · exact O.circle_A
  · exact O.circle_B
  · rfl
  · rfl
  · rfl

theorem HardInput.fromPair_endpoint {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    (I.fromPair O).cycle.theta A=(I.fromPair O).cycle.theta G ∨
      (I.fromPair O).cycle.theta A=(I.fromPair O).cycle.theta T :=
  (pair_endpoint_frames I.cycle O).1

theorem HardInput.fromPair_source_slack {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.PairEndpoint
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    {i : Vertex} (hi : i=H ∨ i=T ∨ i=D ∨ i=E) (j : Fin 4) :
    (I.fromPair O).cycle.slack i j=I.cycle.slack i j :=
  replaceMiddle_slack_unaffected hi j

def HardInput.fromImprovement {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    HardInput q := by
  let hf := pair_endpoint_frames I.cycle O.base
  refine I.replaceMiddle O.pointA O.pointB (I.cycle.theta G-O.base.angleA) hf.1
    O.sorted_A O.sorted_B O.avoids_A O.avoids_B O.normal_A.le O.normal_B.le
    O.circle_A.le O.circle_B.le ?_ ?_ O.AB_zero O.AB_two
  · unfold quarterFeasible
    rw [hf.2.1]
    exact O.GA_exact.symm.le
  · unfold quarterFeasible
    rw [hf.2.2]
    exact O.BT_exact.symm.le

theorem HardInput.fromImprovement_unchanged {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    (i : Vertex) (hi : i ≠ A) (hj : i ≠ B) :
    ((I.fromImprovement O).cycle.point i=I.cycle.point i) ∧
      ((I.fromImprovement O).cycle.theta i=I.cycle.theta i) :=
  replaceMiddle_unchanged I.cycle O.pointA O.pointB (I.cycle.theta G-O.base.angleA) i hi hj

theorem HardInput.fromImprovement_nonincrease {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    AnchorNonincrease I.cycle (I.fromImprovement O).cycle := by
  intro i hi
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · exact O.circle_A.le
  · exact O.circle_B.le
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

theorem HardInput.fromImprovement_strict_A {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    ((I.fromImprovement O).cycle.point A).circle < (I.cycle.point A).circle := O.circle_A

theorem HardInput.fromImprovement_strict_B {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T)) :
    ((I.fromImprovement O).cycle.point B).circle < (I.cycle.point B).circle := O.circle_B

theorem HardInput.fromImprovement_source_slack {q : ℝ} (I : HardInput q)
    (O : HardSplitCap.InteriorImprovement
      (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta A) (I.cycle.theta A-I.cycle.theta T))
    {i : Vertex} (hi : i=H ∨ i=T ∨ i=D ∨ i=E) (j : Fin 4) :
    (I.fromImprovement O).cycle.slack i j=I.cycle.slack i j :=
  replaceMiddle_slack_unaffected hi j

/-- The endpoint split is an actual same-radius hard descendant.  All
five other centers and frames are kept, not reconstructed afterward. -/
theorem HardInput.exists_split_aligned {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A ≤ I.cycle.theta G)
    (hright : I.cycle.theta T ≤ I.cycle.theta A) :
    ∃ J : HardInput q,
      (J.cycle.theta A=J.cycle.theta G ∨ J.cycle.theta A=J.cycle.theta T) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (∀ i, (J.cycle.point i).circle=(I.cycle.point i).circle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.aligned_pair_endpoint hq hHG hAB hTD hleft hright
  exact ⟨I.fromPair O,I.fromPair_endpoint O,rfl,I.fromPair_circles O,
    I.fromPair_unchanged O⟩

/-- If the source common frame is strictly between G and T, the concrete
hard descendant has strict loss at both middle anchors. -/
theorem HardInput.exists_split_strict_loss {q : ℝ} (I : HardInput q) (hq : q ≤ qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A < I.cycle.theta G)
    (hright : I.cycle.theta T < I.cycle.theta A) :
    ∃ J : HardInput q,
      (J.cycle.theta A=J.cycle.theta G ∨ J.cycle.theta A=J.cycle.theta T) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.aligned_pair_endpoint hq hHG hAB hTD hleft.le hright.le
  obtain ⟨P⟩ := HardSplitCap.improve_interior O (sub_pos.mpr hleft) (sub_pos.mpr hright)
  refine ⟨I.fromImprovement P,(pair_endpoint_frames I.cycle P.base).1,rfl,
    I.fromImprovement_nonincrease P,?_,I.fromImprovement_strict_A P,
    I.fromImprovement_strict_B P,I.fromImprovement_unchanged P⟩
  exact ⟨A,by simp [anchorVertices],I.fromImprovement_strict_A P⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
