module

public import SquaresInCircles.Eight.TableFree.MiddleAAdvanceContraction
public import SquaresInCircles.Eight.TableFree.MiddleAboveReflectedCycle

/-!
# Positive AB0 alignment in the ordered intermediate sector

Uncompiled draft.  The same-original-circle A advance is lifted to full
hard cycles.  Moving A to B closes the ordinary positive branch.  In the
crossing sector `A < T ≤ G < B`, advancing A to G and then applying the
original B contraction closes the remaining branch.  The two actual
anchor circle losses compose; the source G/T/H/D/E data stay fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate MiddleAAdvanceContraction
namespace SignedCycle

def replaceAAt (C : SignedCycle) (P : SignedPoint) (ρ : ℝ) : SignedCycle :=
  replacePoint C A P ρ

theorem replaceAAt_unchanged (C : SignedCycle) (P : SignedPoint) (ρ : ℝ)
    (i : Vertex) (hi : i ≠ A) :
    (replaceAAt C P ρ).point i=C.point i ∧ (replaceAAt C P ρ).theta i=C.theta i := by
  simp [replaceAAt,replacePoint,hi]

theorem replaceAAt_spread {C : SignedCycle} (h : C.Spread) (P : SignedPoint) {ρ : ℝ}
    (hρ : ρ=C.theta B ∨ ρ=C.theta G) : (replaceAAt C P ρ).Spread := by
  rcases hρ with rfl | rfl
  · exact replaceA_spread h P
  · intro i j
    by_cases hi : i=A <;> by_cases hj : j=A
    · subst i; subst j
      simpa [replaceAAt,replacePoint] using h G G
    · subst i
      simpa [replaceAAt,replacePoint,hj] using h G j
    · subst j
      simpa [replaceAAt,replacePoint,hi] using h i G
    · simpa [replaceAAt,replacePoint,hi,hj] using h i j

theorem replaceAAt_GA (C : SignedCycle) (P : SignedPoint) (ρ : ℝ) (j : Fin 4) :
    (replaceAAt C P ρ).Feasible G j ↔
      quarterFeasible (C.point G) P (ρ-C.theta G) j := by
  simp [replaceAAt,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,G,A,
    quarterFeasible,sub_nonneg]

theorem replaceAAt_AB (C : SignedCycle) (P : SignedPoint) (ρ : ℝ) (j : Fin 4) :
    (replaceAAt C P ρ).Feasible A j ↔
      zeroFeasible P (C.point B) (C.theta B-ρ) j := by
  simp [replaceAAt,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,
    zeroFeasible,sub_nonneg]

def Witnesses.replaceAUp {C : SignedCycle} (w : C.Witnesses) {ρ : ℝ}
    (O : AAdvance (C.point G) (C.point A) (C.point B) (C.theta G-ρ) (C.theta B-ρ)) :
    (SignedCycle.replaceAAt C O.point ρ).Witnesses where
  owner i := if i=G ∨ i=A then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := A) (by decide : H ≠ A)
        (by decide : next H ≠ A)).2 (w.feasible H)
    · apply (replaceAAt_GA C O.point ρ 0).2
      unfold quarterFeasible
      simpa only [neg_sub] using O.GA_exact.symm.le
    · exact (replaceAAt_AB C O.point ρ 0).2 O.AB
    · exact (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
        (by decide : next B ≠ A)).2 (w.feasible B)
    · exact (replacePoint_other_feasible (v := A) (by decide : T ≠ A)
        (by decide : next T ≠ A)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := A) (by decide : D ≠ A)
        (by decide : next D ≠ A)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := A) (by decide : E ≠ A)
        (by decide : next E ≠ A)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=G ∨ i=A
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,G,A]
    · simpa [hi] using w.allowed i

def HardInput.fromAAdvance {q : ℝ} (I : HardInput q) {ρ : ℝ}
    (hρ : ρ=I.cycle.theta B ∨ ρ=I.cycle.theta G)
    (O : AAdvance (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-ρ) (I.cycle.theta B-ρ)) : HardInput q where
  cycle := SignedCycle.replaceAAt I.cycle O.point ρ
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceAAt,replacePoint] using O.sorted
      · simpa [replaceAAt,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained A)
        simpa [replaceAAt,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceAAt,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceAAt,replacePoint] using O.avoids
      · simpa [replaceAAt,replacePoint,hi] using I.necessary.core i
    spread := replaceAAt_spread I.necessary.spread O.point hρ }
  anchors_normal := by
    constructor
    · simpa [replaceAAt,replacePoint,H,A] using I.anchors_normal.H_nonneg
    · simpa [replaceAAt,replacePoint] using O.normal
    · simpa [replaceAAt,replacePoint,B,A] using I.anchors_normal.B_nonpos
    · simpa [replaceAAt,replacePoint,D,A] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceAAt,replacePoint,E,A] using I.E_nonpos
  witnesses := I.witnesses.replaceAUp O
  GA_hard := by
    apply (replaceAAt_GA I.cycle O.point ρ 0).2
    unfold quarterFeasible
    simpa only [neg_sub] using O.GA_exact.symm.le
  BT_hard := (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
    (by decide : next B ≠ A)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceAUp,H,G,A] using hh
      simpa [replaceAAt,replacePoint,G,A] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceAUp,T,G,A] using hh
      simpa [replaceAAt,replacePoint,T,A] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceAAt,replacePoint,H,D,E,A] using I.E_radial

/-- A concrete advance to an original neighboring frame, with no hidden
loss in the radius or in the actual nonincident owner witnesses. -/
theorem HardInput.advance_A_to_frame {q ρ : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hρ : ρ=I.cycle.theta B ∨ ρ=I.cycle.theta G)
    (hm : I.cycle.theta A < ρ) (hρG : ρ ≤ I.cycle.theta G)
    (hρB : ρ ≤ I.cycle.theta B) (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=ρ ∧ J.cycle.Feasible A 0 ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have hr : I.cycle.theta G-I.cycle.theta A ∈ Icc 0 (7/10 : ℝ) := by
    constructor
    · linarith
    · have hh := I.necessary.spread G A
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
      dsimp [frameCap] at hh
      linarith
  have hd : I.cycle.theta B-I.cycle.theta A ∈ Icc 0 (7/10 : ℝ) := by
    constructor
    · linarith
    · have hh := I.necessary.spread B A
      have ha := le_abs_self (I.cycle.theta B-I.cycle.theta A)
      dsimp [frameCap] at hh
      linarith
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hAB' : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hBa : (I.cycle.point B).a ≤ 283/200 :=
    (SignedPoint.coordinate_bounds (I.necessary.sorted B) (I.necessary.core B)
      (I.necessary.contained B) hq).2.1.le
  obtain ⟨O⟩ := actual_A_advance ((I.necessary.contained A).trans hq)
    I.anchors_normal.A_nonneg hBa I.anchors_normal.B_nonpos hyG hr hd
    (sub_pos.mpr hm)
    (show ρ-I.cycle.theta A ≤ I.cycle.theta G-I.cycle.theta A by linarith)
    (show ρ-I.cycle.theta A ≤ I.cycle.theta B-I.cycle.theta A by linarith) hGA' hAB'
  have ht : (I.cycle.theta G-I.cycle.theta A)-(ρ-I.cycle.theta A)=I.cycle.theta G-ρ := by ring
  have he : (I.cycle.theta B-I.cycle.theta A)-(ρ-I.cycle.theta A)=I.cycle.theta B-ρ := by ring
  rw [ht,he] at O
  refine ⟨I.fromAAdvance hρ O,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromAAdvance,replaceAAt,replacePoint]
  · exact (replaceAAt_AB I.cycle O.point ρ 0).2 O.AB
  · simpa [HardInput.fromAAdvance,replaceAAt,replacePoint] using O.circle_lt
  · intro i hi
    by_cases ha : i=A
    · subst i
      simpa [HardInput.fromAAdvance,replaceAAt,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceAAt_unchanged I.cycle O.point ρ i ha).1).le
  · refine ⟨A,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromAAdvance,replaceAAt,replacePoint] using O.circle_lt
  · exact replaceAAt_unchanged I.cycle O.point ρ

/-- Every positive original AB0 error aligns under the actual G/T order.
The common frame may still need the separate exterior-frame clamp. -/
theorem HardInput.align_positive_AB0_ordered {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hd : I.cycle.theta A < I.cycle.theta B) (hAB : I.cycle.Feasible A 0) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hTA : I.cycle.theta T ≤ I.cycle.theta A
  · obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_positive_AB0 hq hyT hd hTA hAB
    refine ⟨J,halign,hgap.symm.le,hnon,hstrict,?_⟩
    intro i hiA hiB
    exact hfixed i hiB
  · have hAT : I.cycle.theta A < I.cycle.theta T := lt_of_not_ge hTA
    by_cases hBG : I.cycle.theta B ≤ I.cycle.theta G
    · obtain ⟨J,hframe,hABJ,hloss,hnon,hstrict,hfixed⟩ :=
        I.advance_A_to_frame hq hyG (Or.inl rfl) hd hBG le_rfl hAB
      have hB := (hfixed B (by decide : B≠A)).2
      have halign : J.cycle.theta A=J.cycle.theta B := hframe.trans hB.symm
      have hgap : 1 ≤ (J.cycle.point A).y-(J.cycle.point B).y := by
        simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,halign,
          zeroProjection,sub_nonneg] using hABJ
      refine ⟨J,halign,hgap,hnon,hstrict,?_⟩
      intro i hiA hiB
      exact hfixed i hiA
    · have hGB : I.cycle.theta G < I.cycle.theta B := lt_of_not_ge hBG
      obtain ⟨J,hframe,hABJ,hlossA,hnonJ,hstrictJ,hfixedJ⟩ :=
        I.advance_A_to_frame hq hyG (Or.inr rfl) (hAT.trans_le hGT) le_rfl hGB.le hAB
      have hB := hfixedJ B (by decide : B≠A)
      have hT := hfixedJ T (by decide : T≠A)
      have hTJ : J.cycle.theta T ≤ J.cycle.theta A := by rw [hT.2,hframe]; exact hGT
      have hdJ : J.cycle.theta A < J.cycle.theta B := by rw [hframe,hB.2]; exact hGB
      have hyTJ : -(1/10 : ℝ) ≤ (J.cycle.point T).y := by rw [hT.1]; exact hyT
      obtain ⟨K,halign,hframeK,hgap,hlossB,hnonK,hstrictK,hfixedK⟩ :=
        J.align_positive_AB0 hq hyTJ hdJ hTJ hABJ
      refine ⟨K,halign,hgap.symm.le,hnonJ.trans hnonK,hstrictJ.then_nonincrease hnonK,?_⟩
      intro i hiA hiB
      exact ⟨((hfixedK i hiB).1).trans ((hfixedJ i hiA).1),
        ((hfixedK i hiB).2).trans ((hfixedJ i hiA).2)⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
