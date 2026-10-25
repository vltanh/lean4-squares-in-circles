module

public import SquaresInCircles.Eight.Owners.Hard.SplitCycle
public import SquaresInCircles.Eight.Words.Middle.AAdvanceContraction
public import SquaresInCircles.Eight.Words.Middle.PhysicalStress
public import SquaresInCircles.Eight.Words.Middle.ReflectedCycle

/-!
# Eight squares: complete middle canonicalization in the ordered intermediate sector

The original hard cycle is transformed to a common
A/B frame inside the unchanged G/T interval with exact transverse gap
one.  All actual middle-circle comparisons are nonincreasing.  A source
frame error, exterior common frame, or excess common gap creates strict
loss at an original middle anchor, so each is available for equality
pullback.  The global G/T order and one-tenth sign reserves remain explicit
front-end hypotheses.
-/

section
/-!
## Positive AB0 alignment in the ordered intermediate sector

The same-original-circle A advance is lifted to full
hard cycles.  Moving A to B closes the ordinary positive branch.  In the
crossing sector `A < T ≤ G < B`, advancing A to G and then applying the
original B contraction closes the remaining branch.  The two actual
anchor circle losses compose; the source G/T/H/D/E data stay fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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
      have h0 : J.cycle.theta 3-J.cycle.theta 2=0 := by
        change J.cycle.theta B-J.cycle.theta A=0
        rw [halign,sub_self]
      have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
      have hgap : 1 ≤ (J.cycle.point A).y-(J.cycle.point B).y := by
        simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,h0,hW,
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
end SquaresInCircles.Eight
end
end
end

section
/-!
## The reflected crossing middle contraction

The AB2 owner is kept through local reflection of the crossing formula
(`HardInput.reflected_crossing_middle_contraction`). Thus B at or below G suffices for a direct
A contraction, also when A starts strictly above G (`HardInput.align_nonzero_AB2_B_below_G`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddlePositiveContraction MiddleReflectedContraction
namespace SignedCycle

theorem HardInput.reflected_crossing_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hBG : I.cycle.theta B ≤ I.cycle.theta G)
    (hGA : I.cycle.theta G ≤ I.cycle.theta A)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) := by
  have hGAsrc : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hABsrc : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hABref : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
      (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
    simpa [reflectedOwner,neg_sub] using (zeroFeasible_reflect _ _ _ 2).2 hABsrc
  have hBTref : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
      ((I.cycle.theta A-I.cycle.theta B)-(I.cycle.theta G-I.cycle.theta B)) 2 := by
    rw [show (I.cycle.theta A-I.cycle.theta B)-
      (I.cycle.theta G-I.cycle.theta B)=I.cycle.theta A-I.cycle.theta G by ring]
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 0).2 hGAsrc
  have hdu : I.cycle.theta A-I.cycle.theta B ≤ 7/10 := by
    have hh := I.necessary.spread A B
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta B)
    dsimp [frameCap] at hh
    linarith
  obtain ⟨O⟩ := MiddleCrossingContraction.actual_B_contraction
    (by simpa using I.necessary.sorted B)
    (by simpa using I.necessary.core B)
    (by simpa using (I.necessary.contained B).trans hq)
    (by simpa using I.necessary.sorted A)
    (by simpa using (I.necessary.contained A).trans hq)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg)
    (show -(1/10 : ℝ) ≤ (I.cycle.point G).reflect.y by
      dsimp [SignedPoint.reflect]; linarith)
    (sub_pos.mpr hd) (sub_nonneg.mpr hBG)
    (show I.cycle.theta G-I.cycle.theta B ≤ I.cycle.theta A-I.cycle.theta B by linarith)
    hdu hABref hBTref
  exact ⟨reflectB O⟩

/-- A may lie on either side of G in this direct AB2 result. -/
theorem HardInput.middle_AB2_contraction_below_G {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hBG : I.cycle.theta B ≤ I.cycle.theta G)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta G-I.cycle.theta B)) := by
  rcases le_total (I.cycle.theta A) (I.cycle.theta G) with hAG | hGA
  · exact I.reflected_middle_contraction hq hyG (max_le hAG hBG) hne hAB
  · have hd : I.cycle.theta B < I.cycle.theta A := by
      rcases lt_or_gt_of_ne hne with hab | hba
      · linarith
      · exact hba
    exact I.reflected_crossing_middle_contraction hq hyG hd hBG hGA hAB

theorem HardInput.align_nonzero_AB2_B_below_G {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hBG : I.cycle.theta B ≤ I.cycle.theta G)
    (hne : I.cycle.theta A ≠ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta A=I.cycle.theta B ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.middle_AB2_contraction_below_G hq hyG hBG hne hAB
  refine ⟨I.fromReflectedMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromReflectedMiddle,replaceA,replacePoint,A,B]
  · simp [HardInput.fromReflectedMiddle,replaceA,replacePoint]
  · simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint,A,B] using O.AB_exact
  · simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint] using O.circle_lt
  · intro i hi
    by_cases ha : i=A
    · subst i
      simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceA_unchanged I.cycle O.point i ha).1).le
  · refine ⟨A,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromReflectedMiddle,replaceA,replacePoint] using O.circle_lt
  · exact replaceA_unchanged I.cycle O.point

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Negative AB2 errors in every frame order

The last negative-AB2 sector is the exact local
reflection of the explicit below-T AB0 construction.  Its full hard
descendant changes A alone, including when the aligned frame is above G.
The final theorem covers either original AB owner for every negative
middle error and retains strict original anchor-circle loss.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddleBelowContraction

namespace MiddleAboveContraction

structure AWeakContraction (G A B : SignedPoint) (δ : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : 0 < point.y
  circle_lt : point.circle < A.circle
  AB_gap : 1 ≤ point.y-B.y
  AB_zero : zeroFeasible point B 0 0
  AB_two : zeroFeasible point B 0 2
  GA : quarterFeasible G point δ 0

def reflectBWeak {G A B : SignedPoint} {δ : ℝ}
    (O : BWeakContraction B.reflect A.reflect G.reflect δ) : AWeakContraction G A B δ where
  point := O.point.reflect
  sorted := by simpa using O.sorted
  avoids := by simpa using O.avoids
  normal := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal
  circle_lt := by simpa using O.circle_lt
  AB_gap := by
    have hh := O.AB_gap
    dsimp [SignedPoint.reflect] at hh ⊢
    linarith
  AB_zero := (zeroFeasible_reflect O.point.reflect B 0 0).1
    (by simpa [reflectedOwner] using O.AB_two)
  AB_two := (zeroFeasible_reflect O.point.reflect B 0 2).1
    (by simpa [reflectedOwner] using O.AB_zero)
  GA := (quarterFeasible_reflect G O.point.reflect δ 0).1
    (by simpa [reflectedOwner] using O.BT)

end MiddleAboveContraction

open MiddleAboveContraction
namespace SignedCycle

def Witnesses.replaceAWeak {C : SignedCycle} (w : C.Witnesses)
    (O : AWeakContraction (C.point G) (C.point A) (C.point B) (C.theta B-C.theta G)) :
    (SignedCycle.replaceA C O.point).Witnesses where
  owner i := if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := A) (by decide : H ≠ A)
        (by decide : next H ≠ A)).2 (w.feasible H)
    · exact (replaceA_GA C O.point 0).2 O.GA
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      simp only [A] at hj
      rcases hj with hj | hj
      · exact (replaceA_AB C O.point _).2 (by simpa [hj,G] using O.AB_zero)
      · exact (replaceA_AB C O.point _).2 (by simpa [hj,G] using O.AB_two)
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
    by_cases hi : i=G
    · subst i; norm_num [normalOwners,G]
    · simpa [hi] using w.allowed i

def HardInput.fromAboveMiddle {q : ℝ} (I : HardInput q)
    (O : AWeakContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta G)) : HardInput q where
  cycle := SignedCycle.replaceA I.cycle O.point
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.sorted
      · simpa [replaceA,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=A
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained A)
        simpa [replaceA,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceA,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=A
      · subst i; simpa [replaceA,replacePoint] using O.avoids
      · simpa [replaceA,replacePoint,hi] using I.necessary.core i
    spread := replaceA_spread I.necessary.spread O.point }
  anchors_normal := by
    constructor
    · simpa [replaceA,replacePoint,H,A] using I.anchors_normal.H_nonneg
    · simpa [replaceA,replacePoint] using O.normal.le
    · simpa [replaceA,replacePoint,B,A] using I.anchors_normal.B_nonpos
    · simpa [replaceA,replacePoint,D,A] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceA,replacePoint,E,A] using I.E_nonpos
  witnesses := I.witnesses.replaceAWeak O
  GA_hard := (replaceA_GA I.cycle O.point 0).2 O.GA
  BT_hard := (replacePoint_other_feasible (v := A) (by decide : B ≠ A)
    (by decide : next B ≠ A)).2 I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceAWeak,H,G] using hh
      simpa [replaceA,replacePoint,G,A] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceAWeak,T,G] using hh
      simpa [replaceA,replacePoint,T,A] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceA,replacePoint,H,D,E,A] using I.E_radial

theorem HardInput.above_middle_contraction {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hGB : I.cycle.theta G ≤ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    Nonempty (AWeakContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta G)) := by
  have hGAsrc : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hABsrc : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hABref : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
      (-(I.cycle.theta A-I.cycle.theta B)) 0 := by
    simpa [reflectedOwner,neg_sub] using (zeroFeasible_reflect _ _ _ 2).2 hABsrc
  have hBTref : quarterFeasible (I.cycle.point A).reflect (I.cycle.point G).reflect
      ((I.cycle.theta B-I.cycle.theta G)+(I.cycle.theta A-I.cycle.theta B)) 2 := by
    rw [show (I.cycle.theta B-I.cycle.theta G)+
      (I.cycle.theta A-I.cycle.theta B)=I.cycle.theta A-I.cycle.theta G by ring]
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 0).2 hGAsrc
  have hspan : (I.cycle.theta B-I.cycle.theta G)+
      (I.cycle.theta A-I.cycle.theta B) ≤ 7/10 := by
    have hh := I.necessary.spread A G
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta G)
    dsimp [frameCap] at hh
    linarith
  obtain ⟨O⟩ := MiddleBelowContraction.actual_B_contraction
    (by simpa using I.necessary.sorted B)
    (by simpa using I.necessary.core B)
    (by simpa using (I.necessary.contained B).trans hq)
    (by simpa using I.necessary.sorted A)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg)
    (show -(1/10 : ℝ) ≤ (I.cycle.point G).reflect.y by
      dsimp [SignedPoint.reflect]; linarith)
    (sub_pos.mpr hd) (sub_nonneg.mpr hGB) hspan hABref hBTref
  exact ⟨reflectBWeak O⟩

theorem HardInput.align_negative_AB2_above_G {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hGB : I.cycle.theta G ≤ I.cycle.theta B)
    (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta A=I.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨O⟩ := I.above_middle_contraction hq hyG hd hGB hAB
  refine ⟨I.fromAboveMiddle O,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromAboveMiddle,replaceA,replacePoint,A,B]
  · simp [HardInput.fromAboveMiddle,replaceA,replacePoint]
  · simpa [HardInput.fromAboveMiddle,replaceA,replacePoint,A,B] using O.AB_gap
  · simpa [HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt
  · intro i hi
    by_cases ha : i=A
    · subst i
      simpa [HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceA_unchanged I.cycle O.point i ha).1).le
  · refine ⟨A,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt
  · exact replaceA_unchanged I.cycle O.point

theorem HardInput.align_negative_AB2_all_orders {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hd : I.cycle.theta B < I.cycle.theta A)
    (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧ J.cycle.theta A=I.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  rcases le_total (I.cycle.theta B) (I.cycle.theta G) with hBG | hGB
  · obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_nonzero_AB2_B_below_G hq hyG hBG (ne_of_gt hd) hAB
    exact ⟨J,halign,hframe,hgap.symm.le,hloss,hnon,hstrict,hfixed⟩
  · exact I.align_negative_AB2_above_G hq hyG hd hGB hAB

/-- The original physical owner, rather than a relabeling assumption,
chooses the A or B contraction for every negative middle error. -/
theorem HardInput.align_negative_AB_all_owners {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hd : I.cycle.theta B < I.cycle.theta A) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.theta A=I.cycle.theta A ∨ J.cycle.theta A=I.cycle.theta B) ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  rcases hj with hj | hj
  · have hAB : I.cycle.Feasible A 0 := by simpa [hj] using I.witnesses.feasible A
    obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_negative_AB0_all_orders hq hyT hd hAB
    refine ⟨J,halign,Or.inl (halign.trans hframe),hgap,hnon,hstrict,?_⟩
    intro i hiA hiB
    exact hfixed i hiB
  · have hAB : I.cycle.Feasible A 2 := by simpa [hj] using I.witnesses.feasible A
    obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_negative_AB2_all_orders hq hyG hd hAB
    refine ⟨J,halign,Or.inr hframe,hgap,hnon,hstrict,?_⟩
    intro i hiA hiB
    exact hfixed i hiA

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## The reflected positive AB2 reduction and full middle-frame alignment

Reflect the actual local A-up construction to move B
downward, without reflecting the hard cycle or E.  Combining the two
positive owner cases with the all-order negative cases produces a common
middle frame under the actual G/T order.  An exterior common frame and
the final transverse normalization remain separate geometric steps.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddleAAdvanceContraction

namespace MiddleBRetreatContraction

structure BRetreat (A B T : SignedPoint) (t e : ℝ) where
  point : SignedPoint
  sorted : point.Sorted
  avoids : point.AvoidsCore
  normal : point.y ≤ 0
  circle_lt : point.circle < B.circle
  BT_exact : quarterProjection point T (-t) 2=edgeWidth (-t)
  AB : zeroFeasible A point e 2

def reflectA {A B T : SignedPoint} {t e : ℝ}
    (O : AAdvance T.reflect B.reflect A.reflect t e) : BRetreat A B T t e where
  point := O.point.reflect
  sorted := by simpa using O.sorted
  avoids := by simpa using O.avoids
  normal := by simpa [SignedPoint.reflect] using neg_nonpos.mpr O.normal
  circle_lt := by simpa using O.circle_lt
  BT_exact := by
    have hp := quarterProjection_reflect O.point.reflect T (-t) 2
    have he : quarterProjection T.reflect O.point (-t) 0=
        quarterProjection O.point.reflect T (-t) 2 := by
      simpa [reflectedOwner] using hp
    exact he.symm.trans O.GA_exact
  AB := (zeroFeasible_reflect A O.point.reflect e 2).1
    (by simpa [reflectedOwner] using O.AB)

end MiddleBRetreatContraction

open MiddleBRetreatContraction
namespace SignedCycle

def replaceBAt (C : SignedCycle) (P : SignedPoint) (ρ : ℝ) : SignedCycle :=
  replacePoint C B P ρ

theorem replaceBAt_unchanged (C : SignedCycle) (P : SignedPoint) (ρ : ℝ)
    (i : Vertex) (hi : i ≠ B) :
    (replaceBAt C P ρ).point i=C.point i ∧ (replaceBAt C P ρ).theta i=C.theta i := by
  simp [replaceBAt,replacePoint,hi]

theorem replaceBAt_spread {C : SignedCycle} (h : C.Spread) (P : SignedPoint) {ρ : ℝ}
    (hρ : ρ=C.theta A ∨ ρ=C.theta T) : (replaceBAt C P ρ).Spread := by
  rcases hρ with rfl | rfl
  · exact replaceB_spread h P
  · intro i j
    by_cases hi : i=B <;> by_cases hj : j=B
    · subst i; subst j
      simpa [replaceBAt,replacePoint] using h T T
    · subst i
      simpa [replaceBAt,replacePoint,hj] using h T j
    · subst j
      simpa [replaceBAt,replacePoint,hi] using h i T
    · simpa [replaceBAt,replacePoint,hi,hj] using h i j

theorem replaceBAt_BT (C : SignedCycle) (P : SignedPoint) (ρ : ℝ) (j : Fin 4) :
    (replaceBAt C P ρ).Feasible B j ↔
      quarterFeasible P (C.point T) (C.theta T-ρ) j := by
  simp [replaceBAt,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,B,T,
    quarterFeasible,sub_nonneg]

theorem replaceBAt_AB (C : SignedCycle) (P : SignedPoint) (ρ : ℝ) (j : Fin 4) :
    (replaceBAt C P ρ).Feasible A j ↔
      zeroFeasible (C.point A) P (ρ-C.theta A) j := by
  simp [replaceBAt,replacePoint,Feasible,slack,edge,Candidate.word,delta,next,A,B,
    zeroFeasible,sub_nonneg]

def Witnesses.replaceBDown {C : SignedCycle} (w : C.Witnesses) {ρ : ℝ}
    (O : BRetreat (C.point A) (C.point B) (C.point T) (ρ-C.theta T) (ρ-C.theta A)) :
    (SignedCycle.replaceBAt C O.point ρ).Witnesses where
  owner i := if i=A ∨ i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · exact (replacePoint_other_feasible (v := B) (by decide : H ≠ B)
        (by decide : next H ≠ B)).2 (w.feasible H)
    · exact (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
        (by decide : next G ≠ B)).2 (w.feasible G)
    · exact (replaceBAt_AB C O.point ρ 2).2 O.AB
    · apply (replaceBAt_BT C O.point ρ 2).2
      unfold quarterFeasible
      simpa only [neg_sub] using O.BT_exact.symm.le
    · exact (replacePoint_other_feasible (v := B) (by decide : T ≠ B)
        (by decide : next T ≠ B)).2 (w.feasible T)
    · exact (replacePoint_other_feasible (v := B) (by decide : D ≠ B)
        (by decide : next D ≠ B)).2 (w.feasible D)
    · exact (replacePoint_other_feasible (v := B) (by decide : E ≠ B)
        (by decide : next E ≠ B)).2 (w.feasible E)
  allowed := by
    intro i
    by_cases hi : i=A ∨ i=B
    · rcases hi with rfl | rfl <;> norm_num [normalOwners,A,B]
    · simpa [hi] using w.allowed i

def HardInput.fromBRetreat {q : ℝ} (I : HardInput q) {ρ : ℝ}
    (hρ : ρ=I.cycle.theta A ∨ ρ=I.cycle.theta T)
    (O : BRetreat (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (ρ-I.cycle.theta T) (ρ-I.cycle.theta A)) : HardInput q where
  cycle := SignedCycle.replaceBAt I.cycle O.point ρ
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceBAt,replacePoint] using O.sorted
      · simpa [replaceBAt,replacePoint,hi] using I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=B
      · subst i
        have hh := O.circle_lt.le.trans (I.necessary.contained B)
        simpa [replaceBAt,replacePoint,SignedPoint.Contained] using hh
      · simpa [replaceBAt,replacePoint,hi] using I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=B
      · subst i; simpa [replaceBAt,replacePoint] using O.avoids
      · simpa [replaceBAt,replacePoint,hi] using I.necessary.core i
    spread := replaceBAt_spread I.necessary.spread O.point hρ }
  anchors_normal := by
    constructor
    · simpa [replaceBAt,replacePoint,H,B] using I.anchors_normal.H_nonneg
    · simpa [replaceBAt,replacePoint,A,B] using I.anchors_normal.A_nonneg
    · simpa [replaceBAt,replacePoint] using O.normal
    · simpa [replaceBAt,replacePoint,D,B] using I.anchors_normal.D_nonpos
  E_nonpos := by simpa [replaceBAt,replacePoint,E,B] using I.E_nonpos
  witnesses := I.witnesses.replaceBDown O
  GA_hard := (replacePoint_other_feasible (v := B) (by decide : G ≠ B)
    (by decide : next G ≠ B)).2 I.GA_hard
  BT_hard := by
    apply (replaceBAt_BT I.cycle O.point ρ 2).2
    unfold quarterFeasible
    simpa only [neg_sub] using O.BT_exact.symm.le
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.replaceBDown,H,A,B] using hh
      simpa [replaceBAt,replacePoint,G,B] using I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.replaceBDown,T,A,B] using hh
      simpa [replaceBAt,replacePoint,T,B] using I.zero_signs.TD_canceling hj }
  E_radial := by simpa [replaceBAt,replacePoint,H,D,E,B] using I.E_radial

theorem HardInput.retreat_B_to_frame {q ρ : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hρ : ρ=I.cycle.theta A ∨ ρ=I.cycle.theta T)
    (hm : ρ < I.cycle.theta B) (hTρ : I.cycle.theta T ≤ ρ)
    (hAρ : I.cycle.theta A ≤ ρ) (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta B=ρ ∧ J.cycle.Feasible A 2 ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have hr : I.cycle.theta B-I.cycle.theta T ∈ Icc 0 (7/10 : ℝ) := by
    constructor
    · linarith
    · have hh := I.necessary.spread B T
      have ha := le_abs_self (I.cycle.theta B-I.cycle.theta T)
      dsimp [frameCap] at hh
      linarith
  have hd : I.cycle.theta B-I.cycle.theta A ∈ Icc 0 (7/10 : ℝ) := by
    constructor
    · linarith
    · have hh := I.necessary.spread B A
      have ha := le_abs_self (I.cycle.theta B-I.cycle.theta A)
      dsimp [frameCap] at hh
      linarith
  have hBTsrc : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  have hABsrc : zeroFeasible (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta A) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,zeroFeasible,sub_nonneg]
      using hAB
  have hGAref : quarterFeasible (I.cycle.point T).reflect (I.cycle.point B).reflect
      (-(I.cycle.theta B-I.cycle.theta T)) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect _ _ _ 2).2 hBTsrc
  have hABref : zeroFeasible (I.cycle.point B).reflect (I.cycle.point A).reflect
      (I.cycle.theta B-I.cycle.theta A) 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect _ _ _ 2).2 hABsrc
  have hAa : (I.cycle.point A).reflect.a ≤ 283/200 :=
    (SignedPoint.coordinate_bounds (I.necessary.sorted A) (I.necessary.core A)
      (I.necessary.contained A) hq).2.1.le
  obtain ⟨O⟩ := actual_A_advance
    (by simpa using (I.necessary.contained B).trans hq)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    hAa
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr I.anchors_normal.A_nonneg)
    (show (I.cycle.point T).reflect.y ≤ (1/10 : ℝ) by dsimp [SignedPoint.reflect]; linarith)
    hr hd (sub_pos.mpr hm)
    (show I.cycle.theta B-ρ ≤ I.cycle.theta B-I.cycle.theta T by linarith)
    (show I.cycle.theta B-ρ ≤ I.cycle.theta B-I.cycle.theta A by linarith) hGAref hABref
  have ht : (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-ρ)=ρ-I.cycle.theta T := by ring
  have he : (I.cycle.theta B-I.cycle.theta A)-(I.cycle.theta B-ρ)=ρ-I.cycle.theta A := by ring
  rw [ht,he] at O
  let R := reflectA O
  refine ⟨I.fromBRetreat hρ R,?_,?_,?_,?_,?_,?_⟩
  · simp [HardInput.fromBRetreat,replaceBAt,replacePoint]
  · exact (replaceBAt_AB I.cycle R.point ρ 2).2 R.AB
  · simpa [HardInput.fromBRetreat,replaceBAt,replacePoint] using R.circle_lt
  · intro i hi
    by_cases hb : i=B
    · subst i
      simpa [HardInput.fromBRetreat,replaceBAt,replacePoint] using R.circle_lt.le
    · exact (congrArg SignedPoint.circle (replaceBAt_unchanged I.cycle R.point ρ i hb).1).le
  · refine ⟨B,by simp [anchorVertices],?_⟩
    simpa [HardInput.fromBRetreat,replaceBAt,replacePoint] using R.circle_lt
  · exact replaceBAt_unchanged I.cycle R.point ρ

theorem HardInput.align_positive_AB2_ordered {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hd : I.cycle.theta A < I.cycle.theta B) (hAB : I.cycle.Feasible A 2) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hBG : I.cycle.theta B ≤ I.cycle.theta G
  · obtain ⟨J,halign,hframe,hgap,hloss,hnon,hstrict,hfixed⟩ :=
      I.align_nonzero_AB2_B_below_G hq hyG hBG (ne_of_lt hd) hAB
    refine ⟨J,halign,hgap.symm.le,hnon,hstrict,?_⟩
    intro i hiA hiB
    exact hfixed i hiA
  · have hGB : I.cycle.theta G < I.cycle.theta B := lt_of_not_ge hBG
    by_cases hTA : I.cycle.theta T ≤ I.cycle.theta A
    · obtain ⟨J,hframe,hABJ,hloss,hnon,hstrict,hfixed⟩ :=
        I.retreat_B_to_frame hq hyT (Or.inl rfl) hd hTA le_rfl hAB
      have hA := (hfixed A (by decide : A≠B)).2
      have halign : J.cycle.theta A=J.cycle.theta B := hA.trans hframe.symm
      have hgap : 1 ≤ (J.cycle.point A).y-(J.cycle.point B).y := by
        have h0 : J.cycle.theta B-J.cycle.theta A=0 := by rw [halign]; ring
        simp only [A,B] at h0
        simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,h0,
          zeroProjection,sub_nonneg,edgeWidth_zero] using hABJ
      refine ⟨J,halign,hgap,hnon,hstrict,?_⟩
      intro i hiA hiB
      exact hfixed i hiB
    · have hAT : I.cycle.theta A < I.cycle.theta T := lt_of_not_ge hTA
      obtain ⟨J,hframe,hABJ,hlossB,hnonJ,hstrictJ,hfixedJ⟩ :=
        I.retreat_B_to_frame hq hyT (Or.inr rfl) (hGT.trans_lt hGB) le_rfl hAT.le hAB
      have hA := hfixedJ A (by decide : A≠B)
      have hG := hfixedJ G (by decide : G≠B)
      have hBGJ : J.cycle.theta B ≤ J.cycle.theta G := by rw [hframe,hG.2]; exact hGT
      have hdJ : J.cycle.theta A < J.cycle.theta B := by rw [hA.2,hframe]; exact hAT
      have hyGJ : (J.cycle.point G).y ≤ (1/10 : ℝ) := by rw [hG.1]; exact hyG
      obtain ⟨K,halign,hframeK,hgap,hlossA,hnonK,hstrictK,hfixedK⟩ :=
        J.align_nonzero_AB2_B_below_G hq hyGJ hBGJ (ne_of_lt hdJ) hABJ
      refine ⟨K,halign,hgap.symm.le,hnonJ.trans hnonK,hstrictJ.then_nonincrease hnonK,?_⟩
      intro i hiA hiB
      exact ⟨((hfixedK i hiA).1).trans ((hfixedJ i hiB).1),
        ((hfixedK i hiA).2).trans ((hfixedJ i hiB).2)⟩

/-- Exhaustive original-owner and middle-error-sign alignment.  Only the
actual intermediate order and the explicit one-tenth sign reserves are
assumed.  A nonzero source error produces strict loss at A or B. -/
theorem HardInput.align_middle_frames_ordered {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta A≠I.cycle.theta B → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  rcases lt_trichotomy (I.cycle.theta A) (I.cycle.theta B) with hpos | heq | hneg
  · have hex : ∃ J : HardInput q,
        J.cycle.theta A=J.cycle.theta B ∧
        1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
        AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
        (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
      rcases hj with hj | hj
      · exact I.align_positive_AB0_ordered hq hyG hyT hGT hpos
          (by simpa [hj] using I.witnesses.feasible A)
      · exact I.align_positive_AB2_ordered hq hyG hyT hGT hpos
          (by simpa [hj] using I.witnesses.feasible A)
    obtain ⟨J,halign,hgap,hnon,hstrict,hfixed⟩ := hex
    exact ⟨J,halign,hgap,hnon,fun _ => hstrict,hfixed⟩
  · have hgap : 1 ≤ (I.cycle.point A).y-(I.cycle.point B).y := by
      have hw := I.witnesses.feasible A
      have h0 : I.cycle.theta B-I.cycle.theta A=0 := by rw [heq]; ring
      simp only [A,B] at h0
      simp only [A] at hj
      rcases hj with hj | hj <;>
        simpa [hj,Feasible,slack,edge,Candidate.word,delta,next,A,B,h0,
          zeroProjection,sub_nonneg,edgeWidth_zero] using hw
    exact ⟨I,heq,hgap,anchorNonincrease_refl _,fun h => (h heq).elim,
      fun _ _ _ => ⟨rfl,rfl⟩⟩
  · obtain ⟨J,halign,hframe,hgap,hnon,hstrict,hfixed⟩ :=
      I.align_negative_AB_all_owners hq hyG hyT hneg
    exact ⟨J,halign,hgap,hnon,fun _ => hstrict,hfixed⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Returning a negative hard quarter to zero at the original circle

Rotate the shifted corner `(X-1,Y-1)` about `(1,1)`.
The exact norm drop follows from sorting.  The transverse drop is bounded
by the same `21/20` demand estimate used in the positive cap construction.
This proves the finite zero-cap comparison directly, without a piecewise
negative-cap derivative, diagonal transition, or common-radius lift.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleNegativeZeroCap
open HardSplitCap MiddleAAdvanceContraction

/-- Negative signed hard contacts also make the zero cap feasible at
the same source radius.  The two cases are the sign of `Y-1`. -/
theorem feasible_zero {q D θ X Y : ℝ}
    (hq : q ≤ qCap) (hD : 2/5 ≤ D) (hXY : Y ≤ X) (hY : 1/2 ≤ Y)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ))
    (hcontact : D ≤ (X-1)*Real.cos θ+(Y-1)*Real.sin θ)
    (hcircle : X^2+Y^2 ≤ q) : MiddleHardCap.Feasible q D := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 < Real.cos θ := by linarith only [hc]
  have hsortprod := mul_nonneg hs (sub_nonneg.mpr hXY)
  have hU : 0 < X-1 := by
    by_contra! hn
    have hp := mul_nonpos_of_nonpos_of_nonneg hn
      (show 0 ≤ Real.cos θ+Real.sin θ by linarith only [hc,hs])
    linarith only [hcontact,hp,hsortprod,hD]
  refine ⟨hq,hD,?_⟩
  by_cases hY1 : Y ≤ 1
  · have hyprod := mul_nonpos_of_nonpos_of_nonneg (show Y-1 ≤ 0 by linarith only [hY1]) hs
    have hxprod := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hU.le
    have hDX : D+1 ≤ X := by linarith only [hcontact,hyprod,hxprod]
    have hx2 := pow_le_pow_left₀ (show 0 ≤ D+1 by linarith only [hD]) hDX 2
    have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hY 2
    linarith only [hx2,hy2,hcircle]
  · have hV : 0 ≤ Y-1 := by linarith only [hY1]
    let P := (X-1)*Real.cos θ+(Y-1)*Real.sin θ
    have hD0 : 0 ≤ D := by linarith only [hD]
    have hDP : D ≤ P := hcontact
    have hDP2 := pow_le_pow_left₀ hD0 hDP 2
    have hnorm : P^2+((X-1)*Real.sin θ-(Y-1)*Real.cos θ)^2=
        (X-1)^2+(Y-1)^2 := by
      dsimp [P]
      calc
        _ = ((X-1)^2+(Y-1)^2)*((Real.sin θ)^2+(Real.cos θ)^2) := by ring
        _ = _ := by rw [Real.sin_sq_add_cos_sq,mul_one]
    have hDs : D^2 ≤ (X-1)^2+(Y-1)^2 := by
      linarith only [hDP2,hnorm,sq_nonneg ((X-1)*Real.sin θ-(Y-1)*Real.cos θ)]
    have hxprod := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hU.le
    have hyprod := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hV
    have hsum : D ≤ (X-1)+(Y-1) := by linarith only [hcontact,hxprod,hyprod]
    linarith only [hDs,hsum,hcircle]

def rotatedX (X Y θ : ℝ) : ℝ :=
  1+(X-1)*Real.cos θ+(Y-1)*Real.sin θ
def rotatedY (X Y θ : ℝ) : ℝ :=
  1-(X-1)*Real.sin θ+(Y-1)*Real.cos θ

theorem rotation_norm_strict {X Y θ : ℝ}
    (hXY : Y ≤ X) (hX : 1 < X)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hθ0 : 0 < θ) :
    (rotatedX X Y θ)^2+(rotatedY X Y θ)^2 < X^2+Y^2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hθ
  have hc0 : 0 < Real.cos θ := by linarith
  have hspos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0
    (by linarith [hθ.2,Real.pi_gt_three])
  let c := Real.cos θ
  let s := Real.sin θ
  let v := 1-c
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hclt : c < 1 := by
    by_contra! hn
    have hp := mul_pos hspos hspos
    have hcs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hn 2
    nlinarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hsum : 1 < c+s := by
    by_contra! hn
    have hcs := pow_le_pow_left₀ (by dsimp [c,s]; positivity : 0 ≤ c+s) hn 2
    have hp := mul_pos hc0 hspos
    nlinarith
  have hvs : 0 < s-v := by dsimp [v]; linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hXY) hvs.le
  have hstrict := mul_pos (sub_pos.mpr hX) hv
  have hid : (rotatedX X Y θ)^2+(rotatedY X Y θ)^2-X^2-Y^2=
      -2*(X-Y)*(s-v)-4*(X-1)*v := by
    dsimp [rotatedX,rotatedY,v,c,s]
    linear_combination ((X-1)^2+(Y-1)^2)*(Real.sin_sq_add_cos_sq θ)
  linarith

/-- Finite loss bound on the original circle.  Its coefficient is
strictly dominated by the positive cap gain on the opposite anchor. -/
theorem negative_zero_loss {q D θ X Y : ℝ}
    (hq : q ≤ qCap) (hD : 2/5 ≤ D) (hXY : Y ≤ X) (hY : 1/2 ≤ Y)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hθ0 : 0 < θ)
    (hcontact : D ≤ (X-1)*Real.cos θ+(Y-1)*Real.sin θ)
    (hcircle : X^2+Y^2 ≤ q) :
    MiddleHardCap.Feasible q D ∧ Y < cap q D 0+(21/20)*θ := by
  have hf := feasible_zero hq hD hXY hY hθ hcontact hcircle
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hsortprod := mul_nonneg hs (sub_nonneg.mpr hXY)
  have hX1 : 1 < X := by
    by_contra! hn
    have hp := mul_nonpos_of_nonpos_of_nonneg (show X-1 ≤ 0 by linarith only [hn])
      (show 0 ≤ Real.cos θ+Real.sin θ by linarith only [hc,hs])
    linarith only [hcontact,hp,hsortprod,hD]
  have hXu : X ≤ 383/200 := by
    by_contra! hn
    have hx2 := pow_lt_pow_left₀ hn (by norm_num : (0:ℝ) ≤ 383/200)
      (by decide : (2:ℕ)≠0)
    have hy2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hY 2
    have hQ := hq
    dsimp [qCap] at hQ
    linarith only [hx2,hy2,hQ,hcircle]
  have hYu : Y ≤ 3/2 := by
    by_contra! hn
    have hy2 := pow_lt_pow_left₀ hn (by norm_num : (0:ℝ) ≤ 3/2)
      (by decide : (2:ℕ)≠0)
    have hx2 := pow_le_pow_left₀ (show 0 ≤ Y by linarith only [hY]) hXY 2
    have hQ := hq
    dsimp [qCap] at hQ
    linarith only [hx2,hy2,hQ,hcircle]
  let proxy : SignedPoint := ⟨X-1/2,Y-3/2⟩
  have hproxyA : proxy.a ≤ 283/200 := by dsimp [proxy]; linarith only [hXu]
  have hproxyY : proxy.y ≤ 0 := by dsimp [proxy]; linarith only [hYu]
  have hg := demand_gain hproxyA hproxyY hθ (by norm_num : (0:ℝ) ≤ 0) hθ0
  have hd0 : demand proxy 0=Y := by simp [demand,proxy]; ring
  have hdθ : demand proxy θ=rotatedY X Y θ := by dsimp [demand,proxy,rotatedY]; ring
  rw [hd0,hdθ,sub_zero] at hg
  have hnorm := rotation_norm_strict hXY hX1 hθ hθ0
  have hXrot : D+1 ≤ rotatedX X Y θ := by dsimp [rotatedX]; linarith only [hcontact]
  have hXrot2 := pow_le_pow_left₀ (show 0 ≤ D+1 by linarith only [hD]) hXrot 2
  have hzero : (0:ℝ) ∈ Icc 0 (7/10 : ℝ) := by norm_num
  have hw := MiddleHardCap.root_pos hf hzero
  have hw2 := MiddleHardCap.root_sq hf hzero
  have hcap0 : cap q D 0=root q D 0 := by simp [cap]
  have hYrot : rotatedY X Y θ < cap q D 0 := by
    rw [hcap0]
    simp only [contact,Real.cos_zero] at hw2
    have hlt : (rotatedY X Y θ)^2<(root q D 0)^2 := by
      linarith only [hw2,hnorm,hcircle,hXrot2]
    exact lt_of_pow_lt_pow_left₀ 2 hw.le hlt
  exact ⟨hf,by linarith only [hg,hYrot]⟩

end SquaresInCircles.Eight.MiddleNegativeZeroCap
end
end
end

section
/-!
## Actual-circle construction for an exterior common middle frame

The negative-quarter zero comparison and the opposite
positive-cap gain make the two endpoint caps sum to more than two.  Each
cap uses its own original anchor radius.  Two explicit transverse corners
strictly below those caps sum to two; their exact hard-contact primaries
give strict circle loss at both original middle anchors.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleClampConstruction
open HardSplitCap MiddlePositiveContraction

theorem cap_upper {q D θ : ℝ} (h : MiddleHardCap.Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 ≤ cap q D θ) : cap q D θ < 7/5 := by
  have hX := MiddleHardCap.primary_lower h.transverse hθ
    (show 0 ≤ cap q D θ by linarith) (HardSplitCap.corner_contact q D θ).ge
  have hprimary : 7/5 ≤ cornerX q D θ := by linarith [h.transverse]
  have hXs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hprimary 2
  have hnorm := MiddleHardCap.corner_norm h hθ
  have hq := h.ceiling
  dsimp [qCap] at hq
  by_contra! hn
  have hYs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hn 2
  nlinarith

def contactPoint (D Y θ : ℝ) : SignedPoint :=
  ⟨primaryCorner D Y θ-1/2,Y-1/2⟩

theorem contactPoint_properties {q D θ Y : ℝ} (h : MiddleHardCap.Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 < Y) (hcap : Y < cap q D θ) :
    (contactPoint D Y θ).Sorted ∧ (contactPoint D Y θ).AvoidsCore ∧
      0 < (contactPoint D Y θ).y ∧ (contactPoint D Y θ).circle < q ∧
      (contactPoint D Y θ).a*Real.cos θ-(contactPoint D Y θ).y*Real.sin θ=
        edgeWidth θ+D-1/2 := by
  obtain ⟨hprimary,hnorm,hsorted⟩ := MiddleHardCap.strict_contact_norm h hθ hY.le hcap
  have hnormal : 0 < (contactPoint D Y θ).y := by dsimp [contactPoint]; linarith
  have hcircle : (contactPoint D Y θ).circle=(primaryCorner D Y θ)^2+Y^2 := by
    dsimp [SignedPoint.circle]
    rw [abs_of_pos hnormal]
    dsimp [contactPoint]
    ring
  refine ⟨⟨by dsimp [contactPoint]; linarith,?_⟩,?_,hnormal,?_,?_⟩
  · rw [abs_of_pos hnormal]
    dsimp [contactPoint]
    linarith
  · have ha : (9/10 : ℝ) ≤ (contactPoint D Y θ).a := by dsimp [contactPoint]; linarith
    dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ (contactPoint D Y θ).a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ (contactPoint D Y θ).a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|(contactPoint D Y θ).y|-1/2) 0)]
  · rw [hcircle]
    exact hnorm
  · have hc0 : Real.cos θ ≠ 0 := ne_of_gt (by
      linarith [(transport_trig_coarse hθ).1] : 0 < Real.cos θ)
    have hh := primaryCorner_contact (D := D) (Y := Y) hc0
    rw [edgeWidth_positive_formula hθ]
    dsimp [contactPoint]
    nlinarith

private theorem r8_quarterProjection_two (p r : SignedPoint) (d : ℝ) :
    quarterProjection p r d 2=p.a*Real.cos d-p.y*Real.sin d-r.y := rfl

structure PairClamp (G A B T : SignedPoint) (t u : ℝ) where
  pointA : SignedPoint
  pointB : SignedPoint
  sorted_A : pointA.Sorted
  sorted_B : pointB.Sorted
  avoids_A : pointA.AvoidsCore
  avoids_B : pointB.AvoidsCore
  normal_A : 0 < pointA.y
  normal_B : pointB.y < 0
  circle_A : pointA.circle < A.circle
  circle_B : pointB.circle < B.circle
  AB_exact : pointA.y-pointB.y=1
  AB_zero : zeroFeasible pointA pointB 0 0
  AB_two : zeroFeasible pointA pointB 0 2
  GA_exact : quarterProjection G pointA (-t) 0=edgeWidth (-t)
  BT_exact : quarterProjection pointB T (-u) 2=edgeWidth (-u)

theorem actual_above_pair {G A B T : SignedPoint} {r η : ℝ}
    (hsA : A.Sorted) (hqA : A.circle ≤ qCap) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ (1/10 : ℝ)) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hr : 0 < r) (hη : 0 ≤ η) (hspan : r+η ≤ 7/10)
    (hgap : 1 ≤ A.y-B.y)
    (hGA : quarterFeasible G A r 0)
    (hBT : quarterFeasible B T (-(r+η)) 2) : Nonempty (PairClamp G A B T 0 η) := by
  let DA := 1/2-G.y
  let DB := 1/2+T.y
  let XA := A.a+1/2
  let YA := A.y+1/2
  let XB := B.a+1/2
  let YB := -B.y+1/2
  let LA := cap A.circle DA 0
  let LB := cap B.circle DB η
  have hrm : r ∈ Icc 0 (7/10 : ℝ) := ⟨hr.le,by linarith⟩
  have hηm : η ∈ Icc 0 (7/10 : ℝ) := ⟨hη,by linarith⟩
  have hum : r+η ∈ Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  have hzero : (0:ℝ) ∈ Icc 0 (7/10 : ℝ) := by norm_num
  have hDA : 2/5 ≤ DA := by dsimp [DA]; linarith
  have hDB : 2/5 ≤ DB := by dsimp [DB]; linarith
  have hYA : 1/2 ≤ YA := by dsimp [YA]; linarith
  have hYB : 1/2 ≤ YB := by dsimp [YB]; linarith
  have hXYA : YA ≤ XA := by
    have hh := hsA.2
    rw [abs_of_nonneg hyA] at hh
    dsimp [XA,YA]
    linarith
  have hcircleA : XA^2+YA^2=A.circle := by
    simp [XA,YA,SignedPoint.circle,abs_of_nonneg hyA]
  have hcircleB : XB^2+YB^2=B.circle := by
    simp [XB,YB,SignedPoint.circle,abs_of_nonpos hyB]
  have hcontactA : DA ≤ (XA-1)*Real.cos r+(YA-1)*Real.sin r := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula hrm] at hh
    dsimp [DA,XA,YA]
    nlinarith
  have hcontactB : DB ≤ (XB-1)*Real.cos (r+η)-YB*Real.sin (r+η) := by
    have hh : edgeWidth (-(r+η)) ≤ quarterProjection B T (-(r+η)) 2 := hBT
    rw [r8_quarterProjection_two,edgeWidth_negative_formula hum,Real.cos_neg,
      Real.sin_neg] at hh
    dsimp [DB,XB,YB]
    linarith
  obtain ⟨hfA,hgainA⟩ := MiddleNegativeZeroCap.negative_zero_loss
    hqA hDA hXYA hYA hrm hr hcontactA hcircleA.le
  have hfB := MiddleHardCap.feasible_of_contact hqB hDB hum hYB hcontactB hcircleB.le
  have hcapB := MiddleHardCap.cap_majorizes hfB hum
    (show 0 ≤ YB by linarith) hcontactB hcircleB.le
  have hgainB := MiddleHardCap.cap_gain hfB hum hη
    (show η < r+η by linarith) (hYB.trans hcapB)
  have hsum : 2 < LA+LB := by
    dsimp [LA,LB] at *
    dsimp [YA,YB] at hgainA hcapB hYA hYB
    linarith
  have hLBfloor : 1/2 ≤ LB := by dsimp [LB]; linarith
  have hLBupper : LB < 7/5 := cap_upper hfB hηm hLBfloor
  have hLAfloor : 1/2 ≤ LA := by linarith
  have hLAupper : LA < 7/5 := cap_upper hfA hzero hLAfloor
  let YA' := (2+LA-LB)/2
  let YB' := (2+LB-LA)/2
  have hYA' : 1/2 < YA' := by dsimp [YA']; linarith
  have hYB' : 1/2 < YB' := by dsimp [YB']; linarith
  have hYAcap : YA' < LA := by dsimp [YA']; linarith
  have hYBcap : YB' < LB := by dsimp [YB']; linarith
  obtain ⟨hsP,hcP,hnP,hqP,hhP⟩ := contactPoint_properties hfA hzero hYA' hYAcap
  obtain ⟨hsR,hcR,hnR,hqR,hhR⟩ := contactPoint_properties hfB hηm hYB' hYBcap
  let P := contactPoint DA YA' 0
  let R := (contactPoint DB YB' η).reflect
  have hABexact : P.y-R.y=1 := by
    dsimp [P,R,contactPoint,SignedPoint.reflect,YA',YB']
    ring
  refine ⟨{
    pointA := P
    pointB := R
    sorted_A := hsP
    sorted_B := by simpa [R] using hsR
    avoids_A := hcP
    avoids_B := by simpa [R] using hcR
    normal_A := hnP
    normal_B := by simpa [R,SignedPoint.reflect] using neg_neg_of_pos hnR
    circle_A := hqP
    circle_B := by simpa [R] using hqR
    AB_exact := hABexact
    AB_zero := by simp [zeroFeasible,zeroProjection,hABexact]
    AB_two := by simp [zeroFeasible,zeroProjection,hABexact]
    GA_exact := ?_
    BT_exact := ?_
  }⟩
  · change G.y+P.a*Real.cos (-(0:ℝ))+P.y*Real.sin (-(0:ℝ))=edgeWidth (-(0:ℝ))
    change P.a*Real.cos 0-P.y*Real.sin 0=edgeWidth 0+DA-1/2 at hhP
    simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,edgeWidth_zero] at hhP
    simp only [neg_zero,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,edgeWidth_zero]
    dsimp [DA] at hhP
    linarith
  · change R.a*Real.cos (-η)-R.y*Real.sin (-η)-T.y=edgeWidth (-η)
    rw [Real.cos_neg,Real.sin_neg,edgeWidth_neg]
    have hRa : R.a=(contactPoint DB YB' η).a := rfl
    have hRy : R.y= -(contactPoint DB YB' η).y := rfl
    have hDB : DB=1/2+T.y := rfl
    rw [hRa,hRy]
    rw [hDB] at hhR
    linarith

def PairClamp.reflected {G A B T : SignedPoint} {t u : ℝ}
    (O : PairClamp T.reflect B.reflect A.reflect G.reflect t u) : PairClamp G A B T u t where
  pointA := O.pointB.reflect
  pointB := O.pointA.reflect
  sorted_A := by simpa using O.sorted_B
  sorted_B := by simpa using O.sorted_A
  avoids_A := by simpa using O.avoids_B
  avoids_B := by simpa using O.avoids_A
  normal_A := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal_B
  normal_B := by simpa [SignedPoint.reflect] using neg_neg_of_pos O.normal_A
  circle_A := by simpa using O.circle_B
  circle_B := by simpa using O.circle_A
  AB_exact := by
    have hh := O.AB_exact
    dsimp [SignedPoint.reflect]
    linarith
  AB_zero := (zeroFeasible_reflect O.pointB.reflect O.pointA.reflect 0 0).1
    (by simpa [reflectedOwner] using O.AB_two)
  AB_two := (zeroFeasible_reflect O.pointB.reflect O.pointA.reflect 0 2).1
    (by simpa [reflectedOwner] using O.AB_zero)
  GA_exact := by
    have hp := quarterProjection_reflect G O.pointB.reflect (-u) 0
    have he : quarterProjection O.pointB G.reflect (-u) 2=
        quarterProjection G O.pointB.reflect (-u) 0 := by simpa [reflectedOwner] using hp
    exact he.symm.trans O.BT_exact
  BT_exact := by
    have hp := quarterProjection_reflect O.pointA.reflect T (-t) 2
    have he : quarterProjection T.reflect O.pointA (-t) 0=
        quarterProjection O.pointA.reflect T (-t) 2 := by simpa [reflectedOwner] using hp
    exact he.symm.trans O.GA_exact

theorem actual_below_pair {G A B T : SignedPoint} {r η : ℝ}
    (hsB : B.Sorted) (hqA : A.circle ≤ qCap) (hqB : B.circle ≤ qCap)
    (hyA : 0 ≤ A.y) (hyB : B.y ≤ 0)
    (hyG : G.y ≤ (1/10 : ℝ)) (hyT : -(1/10 : ℝ) ≤ T.y)
    (hr : 0 < r) (hη : 0 ≤ η) (hspan : r+η ≤ 7/10)
    (hgap : 1 ≤ A.y-B.y)
    (hGA : quarterFeasible G A (-(r+η)) 0)
    (hBT : quarterFeasible B T r 2) : Nonempty (PairClamp G A B T η 0) := by
  have hGAref : quarterFeasible T.reflect B.reflect r 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T r 2).2 hBT
  have hBTref : quarterFeasible A.reflect G.reflect (-(r+η)) 2 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect G A (-(r+η)) 0).2 hGA
  obtain ⟨O⟩ := actual_above_pair (by simpa using hsB)
    (by simpa using hqB) (by simpa using hqA)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hyB)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr hyA)
    (show T.reflect.y ≤ (1/10 : ℝ) by dsimp [SignedPoint.reflect]; linarith)
    (show -(1/10 : ℝ) ≤ G.reflect.y by dsimp [SignedPoint.reflect]; linarith)
    hr hη hspan
    (show 1 ≤ B.reflect.y-A.reflect.y by dsimp [SignedPoint.reflect]; linarith)
    hGAref hBTref
  exact ⟨O.reflected⟩

end SquaresInCircles.Eight.MiddleClampConstruction
end
end
end

section
/-!
## Clamping a common middle frame to the G/T interval

Both exterior cases use the separate-circle pair construction (`HardInput.above_common_pair`,
`HardInput.below_common_pair`). The new hard cycle (`HardInput.fromClamp`) keeps the original H,
G, T, D and E data and the nonincident physical witnesses. A common frame of the source outside
the interval produces strict losses on both A and B (`HardInput.clamp_common_middle`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddleClampConstruction
namespace SignedCycle

theorem HardInput.aligned_AB_gap {q : ℝ} (I : HardInput q)
    (hcommon : I.cycle.theta A=I.cycle.theta B) :
    1 ≤ (I.cycle.point A).y-(I.cycle.point B).y := by
  have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
    simpa [normalOwners,A] using I.witnesses.allowed A
  have hw := I.witnesses.feasible A
  have h0 : I.cycle.theta B-I.cycle.theta A=0 := by rw [hcommon]; ring
  simp only [A,B] at h0
  simp only [A] at hj
  rcases hj with hj | hj <;>
    simpa [hj,Feasible,slack,edge,Candidate.word,delta,next,A,B,h0,
      zeroProjection,sub_nonneg,edgeWidth_zero] using hw

def HardInput.fromClamp {q β : ℝ} (I : HardInput q)
    (hβ : β=I.cycle.theta G ∨ β=I.cycle.theta T)
    (O : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-β) (β-I.cycle.theta T)) : HardInput q :=
  I.replaceMiddle O.pointA O.pointB β hβ O.sorted_A O.sorted_B O.avoids_A O.avoids_B
    O.normal_A.le O.normal_B.le O.circle_A.le O.circle_B.le
    (by unfold quarterFeasible; simpa only [neg_sub] using O.GA_exact.symm.le)
    (by unfold quarterFeasible; simpa only [neg_sub] using O.BT_exact.symm.le)
    O.AB_zero O.AB_two

theorem HardInput.fromClamp_properties {q β : ℝ} (I : HardInput q)
    (hβ : β=I.cycle.theta G ∨ β=I.cycle.theta T)
    (O : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-β) (β-I.cycle.theta T)) :
    let J := I.fromClamp hβ O
    J.cycle.theta A=β ∧ J.cycle.theta B=β ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      (J.cycle.point A).circle < (I.cycle.point A).circle ∧
      (J.cycle.point B).circle < (I.cycle.point B).circle ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  dsimp only
  refine ⟨rfl,rfl,O.AB_exact,O.circle_A,O.circle_B,?_,?_⟩
  · intro i hi
    by_cases ha : i=A
    · subst i; exact O.circle_A.le
    by_cases hb : i=B
    · subst i; exact O.circle_B.le
    · exact (congrArg SignedPoint.circle (replaceMiddle_unchanged I.cycle O.pointA O.pointB β i ha hb).1).le
  · exact replaceMiddle_unchanged I.cycle O.pointA O.pointB β

theorem HardInput.above_common_pair {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hG : I.cycle.theta G < I.cycle.theta A) :
    Nonempty (PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      0 (I.cycle.theta G-I.cycle.theta T)) := by
  have hspan : (I.cycle.theta A-I.cycle.theta G)+
      (I.cycle.theta G-I.cycle.theta T) ≤ 7/10 := by
    have hh := I.necessary.spread A T
    have ha := le_abs_self (I.cycle.theta A-I.cycle.theta T)
    dsimp [frameCap] at hh
    linarith
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hBTraw : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta B) 2 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta A-I.cycle.theta G)+(I.cycle.theta G-I.cycle.theta T))) 2 := by
    rw [show -((I.cycle.theta A-I.cycle.theta G)+(I.cycle.theta G-I.cycle.theta T))=
      I.cycle.theta T-I.cycle.theta A by ring,hcommon]
    exact hBTraw
  exact actual_above_pair (I.necessary.sorted A) ((I.necessary.contained A).trans hq)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyG hyT (sub_pos.mpr hG) (sub_nonneg.mpr hGT)
    hspan (I.aligned_AB_gap hcommon) hGA hBT

theorem HardInput.below_common_pair {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hT : I.cycle.theta A < I.cycle.theta T) :
    Nonempty (PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta G-I.cycle.theta T) 0) := by
  have hspan : (I.cycle.theta T-I.cycle.theta A)+
      (I.cycle.theta G-I.cycle.theta T) ≤ 7/10 := by
    have hh := I.necessary.spread G A
    have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
    dsimp [frameCap] at hh
    linarith
  have hGAraw : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta A-I.cycle.theta G) 0 := by
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-((I.cycle.theta T-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta T))) 0 := by
    rw [show -((I.cycle.theta T-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta T))=
      I.cycle.theta A-I.cycle.theta G by ring]
    exact hGAraw
  have hBT : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (I.cycle.theta T-I.cycle.theta A) 2 := by
    rw [hcommon]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact actual_below_pair (I.necessary.sorted B) ((I.necessary.contained A).trans hq)
    ((I.necessary.contained B).trans hq) I.anchors_normal.A_nonneg
    I.anchors_normal.B_nonpos hyG hyT (sub_pos.mpr hT) (sub_nonneg.mpr hGT)
    hspan (I.aligned_AB_gap hcommon) hGA hBT

/-- The common middle frame is brought into the original intermediate interval `[θT, θG]`; if
it lies outside, both anchor circles of the source strictly decrease. -/
theorem HardInput.clamp_common_middle {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      1 ≤ (J.cycle.point A).y-(J.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A<I.cycle.theta T ∨ I.cycle.theta G<I.cycle.theta A) →
        (J.cycle.point A).circle<(I.cycle.point A).circle ∧
        (J.cycle.point B).circle<(I.cycle.point B).circle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hupper : I.cycle.theta A ≤ I.cycle.theta G
  · by_cases hlower : I.cycle.theta T ≤ I.cycle.theta A
    · refine ⟨I,hcommon,⟨hlower,hupper⟩,I.aligned_AB_gap hcommon,
        anchorNonincrease_refl _,?_,fun _ _ _ => ⟨rfl,rfl⟩⟩
      rintro (h | h) <;> linarith
    · have hlow : I.cycle.theta A < I.cycle.theta T := lt_of_not_ge hlower
      obtain ⟨O⟩ := I.below_common_pair hq hyG hyT hGT hcommon hlow
      have O' : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
          (I.cycle.theta G-I.cycle.theta T) (I.cycle.theta T-I.cycle.theta T) := by
        simpa only [sub_self] using O
      let J := I.fromClamp (Or.inr rfl) O'
      obtain ⟨hA,hB,hgap,hCA,hCB,hnon,hfixed⟩ := I.fromClamp_properties (Or.inr rfl) O'
      refine ⟨J,hA.trans hB.symm,?_,hgap.symm.le,hnon,fun _ => ⟨hCA,hCB⟩,hfixed⟩
      rw [hA]
      exact ⟨le_rfl,hGT⟩
  · have hupp : I.cycle.theta G < I.cycle.theta A := lt_of_not_ge hupper
    obtain ⟨O⟩ := I.above_common_pair hq hyG hyT hGT hcommon hupp
    have O' : PairClamp (I.cycle.point G) (I.cycle.point A) (I.cycle.point B) (I.cycle.point T)
        (I.cycle.theta G-I.cycle.theta G) (I.cycle.theta G-I.cycle.theta T) := by
      simpa only [sub_self] using O
    let J := I.fromClamp (Or.inl rfl) O'
    obtain ⟨hA,hB,hgap,hCA,hCB,hnon,hfixed⟩ := I.fromClamp_properties (Or.inl rfl) O'
    refine ⟨J,hA.trans hB.symm,?_,hgap.symm.le,hnon,fun _ => ⟨hCA,hCB⟩,hfixed⟩
    rw [hA]
    exact ⟨hGT,le_rfl⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate MiddleAboveContraction
namespace SignedCycle

theorem HardInput.gap_normalization_point {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A ≤ I.cycle.theta G)
    (hgap : 1 < (I.cycle.point A).y-(I.cycle.point B).y) :
    ∃ O : AWeakContraction (I.cycle.point G) (I.cycle.point A) (I.cycle.point B)
      (I.cycle.theta B-I.cycle.theta G), O.point.y-(I.cycle.point B).y=1 := by
  let t := I.cycle.theta G-I.cycle.theta A
  let P : SignedPoint := ⟨(I.cycle.point A).a,1+(I.cycle.point B).y⟩
  have htm : t ∈ Icc 0 (7/10 : ℝ) := by
    constructor
    · exact sub_nonneg.mpr hAG
    · have hh := I.necessary.spread G A
      have ha := le_abs_self (I.cycle.theta G-I.cycle.theta A)
      dsimp [frameCap] at hh
      dsimp [t]
      linarith
  have hBbound := (SignedPoint.coordinate_bounds (I.necessary.sorted B)
    (I.necessary.core B) (I.necessary.contained B) hq).2.2
  have hnormal : 0 < P.y := by
    dsimp [P]
    linarith [neg_le_abs (I.cycle.point B).y]
  have hPY : P.y < (I.cycle.point A).y := by dsimp [P]; linarith
  have hGA : quarterFeasible (I.cycle.point G) (I.cycle.point A) (-t) 0 := by
    dsimp [t]
    rw [neg_sub]
    simpa [Feasible,slack,edge,Candidate.word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  have hcontact : 1/2-(I.cycle.point G).y ≤
      ((I.cycle.point A).a+1/2-1)*Real.cos t-
        ((I.cycle.point A).y+1/2)*Real.sin t := by
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh
    rw [edgeWidth_positive_formula htm] at hh
    nlinarith
  have hprimary : (9/10 : ℝ) ≤ P.a := by
    have hh := MiddleHardCap.primary_lower
      (show 2/5 ≤ 1/2-(I.cycle.point G).y by linarith) htm
      (show 0 ≤ (I.cycle.point A).y+1/2 by linarith [I.anchors_normal.A_nonneg]) hcontact
    dsimp [P]
    linarith
  have hcircle : P.circle < (I.cycle.point A).circle := by
    have hs := pow_lt_pow_left₀ (show P.y+1/2 < (I.cycle.point A).y+1/2 by linarith)
      (show 0 ≤ P.y+1/2 by linarith) (by decide : (2:ℕ)≠0)
    dsimp [SignedPoint.circle]
    rw [abs_of_pos hnormal,abs_of_nonneg I.anchors_normal.A_nonneg]
    dsimp [P] at *
    linarith
  have hABexact : P.y-(I.cycle.point B).y=1 := by dsimp [P]; ring
  refine ⟨{
    point := P
    sorted := ⟨by dsimp [P]; exact (I.necessary.sorted A).1,?_⟩
    avoids := ?_
    normal := hnormal
    circle_lt := hcircle
    AB_gap := hABexact.symm.le
    AB_zero := by simp [zeroFeasible,zeroProjection,hABexact]
    AB_two := by simp [zeroFeasible,zeroProjection,hABexact]
    GA := ?_
  },hABexact⟩
  · have hh := (I.necessary.sorted A).2
    rw [abs_of_nonneg I.anchors_normal.A_nonneg] at hh
    rw [abs_of_pos hnormal]
    dsimp [P]
    linarith
  · dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0 ≤ P.a-1/2)]
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/5)
      (show 2/5 ≤ P.a-1/2 by linarith) 2
    nlinarith [sq_nonneg (max (|P.y|-1/2) 0)]
  · rw [← hcommon,show I.cycle.theta A-I.cycle.theta G= -t by dsimp [t]; ring]
    have hs0 := (transport_trig_coarse htm).2.1
    have hp := mul_nonneg (sub_nonneg.mpr hPY.le) hs0
    have hh := hGA
    simp [quarterFeasible,quarterProjection] at hh ⊢
    dsimp [P] at *
    nlinarith

theorem HardInput.normalize_common_gap {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hcommon : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A ≤ I.cycle.theta G) :
    ∃ J : HardInput q,
      (∀ i, J.cycle.theta i=I.cycle.theta i) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (1 < (I.cycle.point A).y-(I.cycle.point B).y → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → J.cycle.point i=I.cycle.point i) := by
  have hgap := I.aligned_AB_gap hcommon
  by_cases heq : (I.cycle.point A).y-(I.cycle.point B).y=1
  · refine ⟨I,fun _ => rfl,heq,anchorNonincrease_refl _,?_,fun _ _ => rfl⟩
    intro h
    linarith
  · have hstrict : 1 < (I.cycle.point A).y-(I.cycle.point B).y := by
      rcases lt_or_eq_of_le hgap with h | h
      · exact h
      · exact (heq h.symm).elim
    obtain ⟨O,hO⟩ := I.gap_normalization_point hq hyG hcommon hAG hstrict
    let J := I.fromAboveMiddle O
    refine ⟨J,?_,?_,?_,?_,?_⟩
    · intro i
      by_cases hi : i=A
      · subst i
        simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint] using hcommon.symm
      · exact (replaceA_unchanged I.cycle O.point i hi).2
    · simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint,A,B] using hO
    · intro i hi
      by_cases ha : i=A
      · subst i
        simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt.le
      · exact (congrArg SignedPoint.circle (replaceA_unchanged I.cycle O.point i ha).1).le
    · intro _
      refine ⟨A,by simp [anchorVertices],?_⟩
      simpa [J,HardInput.fromAboveMiddle,replaceA,replacePoint] using O.circle_lt
    · intro i hi
      exact (replaceA_unchanged I.cycle O.point i hi).1

theorem HardInput.canonicalize_common_middle {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G)
    (hcommon : I.cycle.theta A=I.cycle.theta B) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A<I.cycle.theta T ∨ I.cycle.theta G<I.cycle.theta A ∨
        1<(I.cycle.point A).y-(I.cycle.point B).y) → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hinside : I.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G)
  · obtain ⟨J,hframes,hgap,hnon,hstrict,hfixed⟩ :=
      I.normalize_common_gap hq hyG hcommon hinside.2
    refine ⟨J,(hframes A).trans (hcommon.trans (hframes B).symm),?_,hgap,hnon,?_,?_⟩
    · rw [hframes A]
      exact hinside
    · rintro (h | h | h)
      · exact (not_lt_of_ge hinside.1 h).elim
      · exact (not_lt_of_ge hinside.2 h).elim
      · exact hstrict h
    · intro i hiA hiB
      exact ⟨hfixed i hiA,hframes i⟩
  · have hout : I.cycle.theta A<I.cycle.theta T ∨ I.cycle.theta G<I.cycle.theta A := by
      by_cases hlo : I.cycle.theta T ≤ I.cycle.theta A
      · right
        exact lt_of_not_ge (fun hhi => hinside ⟨hlo,hhi⟩)
      · exact Or.inl (lt_of_not_ge hlo)
    obtain ⟨K,hcommonK,hintervalK,hgapK,hnonK,hstrictK,hfixedK⟩ :=
      I.clamp_common_middle hq hyG hyT hGT hcommon
    have hGK := hfixedK G (by decide : G≠A) (by decide : G≠B)
    have hyGK : (K.cycle.point G).y ≤ (1/10 : ℝ) := by rw [hGK.1]; exact hyG
    have hAGK : K.cycle.theta A ≤ K.cycle.theta G := by rw [hGK.2]; exact hintervalK.2
    obtain ⟨J,hframes,hgap,hnonJ,hstrictJ,hfixedJ⟩ :=
      K.normalize_common_gap hq hyGK hcommonK hAGK
    have hsourceStrict : StrictAnchorLoss I.cycle K.cycle :=
      ⟨A,by simp [anchorVertices],(hstrictK hout).1⟩
    refine ⟨J,(hframes A).trans (hcommonK.trans (hframes B).symm),?_,hgap,
      hnonK.trans hnonJ,fun _ => hsourceStrict.then_nonincrease hnonJ,?_⟩
    · rw [hframes A]
      exact hintervalK
    · intro i hiA hiB
      exact ⟨(hfixedJ i hiA).trans ((hfixedK i hiA hiB).1),
        (hframes i).trans ((hfixedK i hiA hiB).2)⟩

/-- Complete actual middle reduction under the ordered intermediate
front-end hypotheses.  The source strictness predicate records all
departures from the canonical middle conditions. -/
theorem HardInput.canonicalize_middle_ordered {q : ℝ} (I : HardInput q)
    (hq : q ≤ qCap) (hyG : (I.cycle.point G).y ≤ (1/10 : ℝ))
    (hyT : -(1/10 : ℝ) ≤ (I.cycle.point T).y)
    (hGT : I.cycle.theta T ≤ I.cycle.theta G) :
    ∃ J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta A ∈ Icc (I.cycle.theta T) (I.cycle.theta G) ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta A≠I.cycle.theta B ∨ I.cycle.theta A<I.cycle.theta T ∨
        I.cycle.theta G<I.cycle.theta A ∨ 1<(I.cycle.point A).y-(I.cycle.point B).y) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i, i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  by_cases hcommon : I.cycle.theta A=I.cycle.theta B
  · obtain ⟨J,hAB,hinterval,hgap,hnon,hstrict,hfixed⟩ :=
      I.canonicalize_common_middle hq hyG hyT hGT hcommon
    refine ⟨J,hAB,hinterval,hgap,hnon,?_,hfixed⟩
    rintro (h | h)
    · exact (h hcommon).elim
    · exact hstrict h
  · obtain ⟨K,hcommonK,hgapK,hnonK,hstrictK,hfixedK⟩ :=
      I.align_middle_frames_ordered hq hyG hyT hGT
    have hGK := hfixedK G (by decide : G≠A) (by decide : G≠B)
    have hTK := hfixedK T (by decide : T≠A) (by decide : T≠B)
    have hyGK : (K.cycle.point G).y ≤ (1/10 : ℝ) := by rw [hGK.1]; exact hyG
    have hyTK : -(1/10 : ℝ) ≤ (K.cycle.point T).y := by rw [hTK.1]; exact hyT
    have hGTK : K.cycle.theta T ≤ K.cycle.theta G := by rw [hTK.2,hGK.2]; exact hGT
    obtain ⟨J,hAB,hinterval,hgap,hnonJ,hstrictJ,hfixedJ⟩ :=
      K.canonicalize_common_middle hq hyGK hyTK hGTK hcommonK
    refine ⟨J,hAB,?_,hgap,hnonK.trans hnonJ,
      fun _ => (hstrictK hcommon).then_nonincrease hnonJ,?_⟩
    · simpa only [hTK.2,hGK.2] using hinterval
    · intro i hiA hiB
      exact ⟨((hfixedJ i hiA hiB).1).trans ((hfixedK i hiA hiB).1),
        ((hfixedJ i hiA hiB).2).trans ((hfixedK i hiA hiB).2)⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end
