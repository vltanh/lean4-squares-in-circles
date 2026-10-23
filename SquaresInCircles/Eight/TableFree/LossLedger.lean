module

public import SquaresInCircles.Eight.TableFree.CircleGeometry

/-!
# Composition of actual anchor-circle losses

Uncompiled draft. This module is only bookkeeping: it does not assert that
any geometric transport exists. Each transport must provide the displayed
inequalities for the centers it actually constructs. Strictness is retained
at the five anchors H,A,B,D,E, never at either free intermediate G,T.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree
open Candidate

/-- The five vertices carrying positive disk masses in the stationary dual. -/
def anchorVertices : Finset Vertex := {H,A,B,D,E}

def AnchorNonincrease (C D : SignedCycle) : Prop :=
  ∀ i ∈ anchorVertices, (D.point i).circle ≤ (C.point i).circle

def StrictAnchorLoss (C D : SignedCycle) : Prop :=
  ∃ i ∈ anchorVertices, (D.point i).circle < (C.point i).circle

def AnchorsUnchanged (C D : SignedCycle) : Prop :=
  ∀ i ∈ anchorVertices, D.point i=C.point i ∧ D.theta i=C.theta i

def AllAnchorsOn (q : ℝ) (C : SignedCycle) : Prop :=
  ∀ i ∈ anchorVertices, (C.point i).circle=q

theorem anchorNonincrease_refl (C : SignedCycle) : AnchorNonincrease C C :=
  fun _ _ => le_rfl

theorem AnchorNonincrease.trans {C D E : SignedCycle}
    (hCD : AnchorNonincrease C D) (hDE : AnchorNonincrease D E) :
    AnchorNonincrease C E := fun i hi => (hDE i hi).trans (hCD i hi)

theorem AnchorsUnchanged.nonincrease {C D : SignedCycle}
    (h : AnchorsUnchanged C D) : AnchorNonincrease C D := by
  intro i hi
  rw [(h i hi).1]

theorem AnchorsUnchanged.symm {C D : SignedCycle}
    (h : AnchorsUnchanged C D) : AnchorsUnchanged D C := by
  intro i hi
  exact ⟨(h i hi).1.symm,(h i hi).2.symm⟩

theorem AnchorsUnchanged.trans {C D E : SignedCycle}
    (hCD : AnchorsUnchanged C D) (hDE : AnchorsUnchanged D E) :
    AnchorsUnchanged C E := by
  intro i hi
  exact ⟨(hDE i hi).1.trans (hCD i hi).1,(hDE i hi).2.trans (hCD i hi).2⟩

theorem StrictAnchorLoss.then_nonincrease {C D E : SignedCycle}
    (hCD : StrictAnchorLoss C D) (hDE : AnchorNonincrease D E) :
    StrictAnchorLoss C E := by
  obtain ⟨i,hi,h⟩ := hCD
  exact ⟨i,hi,(hDE i hi).trans_lt h⟩

theorem AnchorNonincrease.then_strict {C D E : SignedCycle}
    (hCD : AnchorNonincrease C D) (hDE : StrictAnchorLoss D E) :
    StrictAnchorLoss C E := by
  obtain ⟨i,hi,h⟩ := hDE
  exact ⟨i,hi,h.trans_le (hCD i hi)⟩

theorem no_strict_loss_to_on_circle {q : ℝ} {C D : SignedCycle}
    (hc : ∀ i ∈ anchorVertices, (C.point i).Contained q)
    (hd : AllAnchorsOn q D) : ¬ StrictAnchorLoss C D := by
  rintro ⟨i,hi,hl⟩
  exact circle_loss_impossible (hc i hi) hl (hd i hi)

/-- Every intermediate state on an anchor-nonincreasing route to a sharp
circle is itself tight. This is the only direction used in equality pullback. -/
theorem anchors_tight_before {q : ℝ} {C D : SignedCycle}
    (hc : ∀ i ∈ anchorVertices, (C.point i).Contained q)
    (hCD : AnchorNonincrease C D) (hd : AllAnchorsOn q D) :
    AllAnchorsOn q C := by
  intro i hi
  exact le_antisymm (hc i hi) ((hd i hi).symm.le.trans (hCD i hi))

/-- Explicit finite transport trace. The record stores the actual states;
it cannot certify a transition without its corresponding circle inequalities. -/
structure AnchorTrace (C D : SignedCycle) where
  length : ℕ
  state : Fin (length+1) → SignedCycle
  first : state 0=C
  last : state (Fin.last length)=D
  step : ∀ i : Fin length,
    AnchorNonincrease (state i.castSucc) (state i.succ)

namespace AnchorTrace

theorem nonincrease {C D : SignedCycle} (T : AnchorTrace C D) :
    AnchorNonincrease C D := by
  have h (k : Fin (T.length+1)) : AnchorNonincrease (T.state 0) (T.state k) := by
    refine Fin.induction ?_ ?_ k
    · exact anchorNonincrease_refl _
    · intro i hi
      exact hi.trans (T.step i)
  simpa [T.first,T.last] using h (Fin.last T.length)

theorem strict_of_step {C D : SignedCycle} (T : AnchorTrace C D)
    (k : Fin T.length)
    (hk : StrictAnchorLoss (T.state k.castSucc) (T.state k.succ)) :
    StrictAnchorLoss C D := by
  obtain ⟨i,hi,hstrict⟩ := hk
  have hmono : Antitone (fun n : Fin (T.length+1) => (T.state n).point i |>.circle) := by
    apply antitone_iff_forall_lt.mpr
    intro a b hab
    have hstep (j : Fin T.length) := T.step j i hi
    exact (Fin.antitone_iff_le_succ.mpr hstep) hab.le
  refine ⟨i,hi,?_⟩
  rw [← T.first,← T.last]
  exact (hmono (Fin.le_last _)).trans_lt
    (hstrict.trans_le (hmono (Fin.zero_le _)))

end AnchorTrace

/-- A local move's predicate must be tested on its source, not on the final
comparison system. The strictness test is supplied by the actual local proof. -/
theorem source_predicate_excluded {P : SignedCycle → Prop} {q : ℝ}
    {C D : SignedCycle} (hc : ∀ i ∈ anchorVertices,(C.point i).Contained q)
    (hd : AllAnchorsOn q D) (hstrict : P C → StrictAnchorLoss C D) : ¬P C := by
  intro hp
  exact no_strict_loss_to_on_circle hc hd (hstrict hp)

/-- G-only and T-only replacements have disjoint changed vertices. -/
def replacePoint (C : SignedCycle) (i : Vertex) (p : SignedPoint) (t : ℝ) : SignedCycle :=
  ⟨Function.update C.point i p,Function.update C.theta i t⟩

theorem replacement_anchors_unchanged (C : SignedCycle) {i : Vertex}
    (hi : i=G ∨ i=T) (p : SignedPoint) (t : ℝ) :
    AnchorsUnchanged C (replacePoint C i p t) := by
  intro j hj
  have hji : j≠i := by
    rcases hi with rfl | rfl <;>
      simp [anchorVertices,H,A,B,D,E,G,T] at hj ⊢ <;> omega
  simp [replacePoint,Function.update_of_ne hji]

theorem intermediate_replacements_commute (C : SignedCycle)
    (pG pT : SignedPoint) (tG tT : ℝ) :
    replacePoint (replacePoint C G pG tG) T pT tT =
      replacePoint (replacePoint C T pT tT) G pG tG := by
  have hGT : G≠T := by decide
  cases C
  simp only [replacePoint]
  congr 1 <;> exact Function.update_comm hGT

end SquaresInCircles.Eight.TableFree