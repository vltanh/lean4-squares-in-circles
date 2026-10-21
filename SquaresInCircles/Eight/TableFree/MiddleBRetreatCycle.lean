module

public import SquaresInCircles.Eight.TableFree.MiddleAAdvanceCycle

/-!
# The reflected positive AB2 reduction and full middle-frame alignment

Uncompiled draft.  Reflect the actual local A-up construction to move B
downward, without reflecting the hard cycle or E.  Combining the two
positive owner cases with the all-order negative cases produces a common
middle frame under the actual G/T order.  An exterior common frame and
the final transverse normalization remain separate geometric steps.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
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
        simpa [Feasible,slack,edge,Candidate.word,delta,next,A,B,halign,
          zeroProjection,sub_nonneg] using hABJ
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
      rcases hj with hj | hj <;>
        simpa [hj,Feasible,slack,edge,Candidate.word,delta,next,A,B,heq,
          zeroProjection,sub_nonneg] using hw
    exact ⟨I,heq,hgap,anchorNonincrease_refl _,fun h => (h heq).elim,
      fun _ _ _ => ⟨rfl,rfl⟩⟩
  · obtain ⟨J,halign,hframe,hgap,hnon,hstrict,hfixed⟩ :=
      I.align_negative_AB_all_owners hq hyG hyT hneg
    exact ⟨J,halign,hgap,hnon,fun _ => hstrict,hfixed⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
