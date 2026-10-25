module

public import SquaresInCircles.Eight.Owners.CircleGeometry

/-!
# Eight squares: composing the losses on the anchor circles

Along a move the circles of the five anchors H, A, B, D, E (`anchorVertices`) do not increase
(`AnchorNonincrease`), or one of them decreases strictly (`StrictAnchorLoss`); strictness is
recorded at the anchors only, never at the free intermediates G and T. These relations compose
(`AnchorNonincrease.trans`, `StrictAnchorLoss.then_nonincrease`, `AnchorNonincrease.then_strict`),
and a strict loss cannot end with every anchor on the circle (`no_strict_loss_to_on_circle`). Each
transport proves them for the points it builds.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
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

/-- If no anchor circle increases from `C` to `D` and every anchor of `D` lies on the circle, then
so does every anchor of `C`. This is the direction used to pull equality back. -/
theorem anchors_tight_before {q : ℝ} {C D : SignedCycle}
    (hc : ∀ i ∈ anchorVertices, (C.point i).Contained q)
    (hCD : AnchorNonincrease C D) (hd : AllAnchorsOn q D) :
    AllAnchorsOn q C := by
  intro i hi
  exact le_antisymm (hc i hi) ((hd i hi).symm.le.trans (hCD i hi))

/-- A finite trace of cycles from `C` to `D` in which no anchor circle increases at any step. -/
structure AnchorTrace (C D : SignedCycle) where
  length : ℕ
  state : Fin (length+1) → SignedCycle
  first : state 0=C
  last : state (Fin.last length)=D
  step : ∀ i : Fin length,
    AnchorNonincrease (state i.castSucc) (state i.succ)

namespace AnchorTrace

end AnchorTrace

/-- The cycle with the point and frame of the vertex `i` replaced by `p` and `t`. Replacing G or T
leaves the anchors unchanged (`replacement_anchors_unchanged`). -/
def replacePoint (C : SignedCycle) (i : Vertex) (p : SignedPoint) (t : ℝ) : SignedCycle :=
  ⟨Function.update C.point i p,Function.update C.theta i t⟩

theorem replacement_anchors_unchanged (C : SignedCycle) {i : Vertex}
    (hi : i=G ∨ i=T) (p : SignedPoint) (t : ℝ) :
    AnchorsUnchanged C (replacePoint C i p t) := by
  intro j hj
  have hji : j≠i := by
    simp only [anchorVertices,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hi with rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨Function.update_of_ne hji _ _,Function.update_of_ne hji _ _⟩

end SquaresInCircles.Eight