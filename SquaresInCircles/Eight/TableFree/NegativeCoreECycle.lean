module

public import SquaresInCircles.Eight.TableFree.NegativeCoreEGap
public import SquaresInCircles.Eight.TableFree.OutsideECycle

/-!
# Original seven-cycle insertion of the negative core-E reductions

Uncompiled source. Both local endpoints change only E. The actual D/H
frames and all other points, owners, and errors are retained. The exact
positive-variation loss is computed before building a new normalized
boundary input at the same q; equality of the two variations supplies
the negative budget as well.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace NegativeCoreE

structure CycleMove (q : ℝ) (C : SignedCycle) where
  point : SignedPoint
  theta : ℝ
  sorted : point.Sorted
  contained : point.Contained q
  core : point.Core
  nonpos : point.y≤0
  frame_range : theta∈Icc (min (C.theta E) (C.theta D)) (max (C.theta E) (C.theta D))
  de : Fin 4
  eh : Fin 4
  de_allowed : de=2 ∨ de=3
  eh_allowed : eh=0 ∨ eh=1
  DE : quarterFeasible (C.point D) point (theta-C.theta D) de
  EH : quarterFeasible point (C.point H) (C.theta H-theta) eh
  positive_nonincrease : positiveVariation (Function.update C.theta E theta)≤positiveVariation C.theta

namespace CycleMove
variable {q : ℝ} {C : SignedCycle}

def cycle (O : CycleMove q C) : SignedCycle := replacePoint C E O.point O.theta

theorem unchanged (O : CycleMove q C) (i : Vertex) (hi : i≠E) :
    O.cycle.point i=C.point i ∧ O.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem other_delta (O : CycleMove q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    delta O.cycle.theta i=delta C.theta i := by
  have hn : next i≠E := (by decide : ∀ j : Vertex,j≠D → next j≠E) i hiD
  simp [delta,(O.unchanged i hiE).2,(O.unchanged (next i) hn).2]

theorem DE_actual (O : CycleMove q C) : O.cycle.Feasible D O.de := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using O.DE

theorem EH_actual (O : CycleMove q C) : O.cycle.Feasible E O.eh := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,
    SignedCycle.edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using O.EH

theorem other_feasible (O : CycleMove q C) (i : Vertex) (hiD : i≠D) (hiE : i≠E)
    (j : Fin 4) : O.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := (by decide : ∀ j : Vertex,j≠D → next j≠E) i hiD
  exact SignedCycle.replacePoint_other_feasible hiE hn

theorem necessary (O : CycleMove q C) (hn : C.Necessary q) : O.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (v := E) (a := E) (b := D)
    hn O.sorted O.contained O.core.ge (Or.inr O.frame_range)

theorem normal (O : CycleMove q C) (hn : C.NormalAnchors) : O.cycle.NormalAnchors := by
  constructor
  · rw [(O.unchanged H (by decide)).1]; exact hn.H_nonneg
  · rw [(O.unchanged A (by decide)).1]; exact hn.A_nonneg
  · rw [(O.unchanged B (by decide)).1]; exact hn.B_nonpos
  · rw [(O.unchanged D (by decide)).1]; exact hn.D_nonpos

def witnesses (O : CycleMove q C) (w : C.Witnesses) : O.cycle.Witnesses where
  owner := Function.update (Function.update w.owner D O.de) E O.eh
  feasible i := by
    by_cases hiE : i=E
    · subst i; simpa using O.EH_actual
    · by_cases hiD : i=D
      · subst i; simpa [D,E] using O.DE_actual
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using
          (O.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i
      simpa [SignedCycle.normalOwners,E] using O.eh_allowed
    · by_cases hiD : i=D
      · subst i
        simpa [SignedCycle.normalOwners,D,E] using O.de_allowed
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using w.allowed i

theorem other_owner (O : CycleMove q C) (w : C.Witnesses) (i : Vertex)
    (hiD : i≠D) (hiE : i≠E) : (O.witnesses w).owner i=w.owner i := by
  simp [witnesses,hiD,hiE]

theorem zero_signs (O : CycleMove q C) (w : C.Witnesses)
    (hz : C.ZeroSignImplications w) : O.cycle.ZeroSignImplications (O.witnesses w) := by
  constructor
  · intro hj
    rw [(O.unchanged G (by decide)).1]
    apply hz.HG_canceling
    simpa [witnesses,H,D,E] using hj
  · intro hj
    rw [(O.unchanged T (by decide)).1]
    apply hz.TD_canceling
    simpa [witnesses,T,D,E] using hj

theorem negative_nonincrease (O : CycleMove q C) :
    negativeVariation O.cycle.theta≤negativeVariation C.theta := by
  rw [← variations_equal O.cycle.theta,← variations_equal C.theta]
  exact O.positive_nonincrease

def boundaryInput (I : SignedCycle.NormalizedBoundaryInput q) (hq : q≤qCap)
    (O : CycleMove q I.cycle) : SignedCycle.NormalizedBoundaryInput q where
  cycle := O.cycle
  necessary := O.necessary I.necessary
  ordered := SignedCycle.normal_necessary_ordered (O.necessary I.necessary) hq
    (O.normal I.anchors_normal) (O.witnesses I.witnesses) (O.zero_signs I.witnesses I.zero_signs)
  strict_spread := SignedCycle.strictSpread_replace_clamped (v := E) (a := E) (b := D)
    (p := O.point) I.strict_spread (Or.inr O.frame_range)
  positive_variation := lt_of_le_of_lt O.positive_nonincrease I.positive_variation
  negative_variation := lt_of_le_of_lt O.negative_nonincrease I.negative_variation
  radial := by
    intro i
    by_cases hi : i=E
    · subst i; exact Or.inr O.core
    · rw [(O.unchanged i hi).1]; exact I.radial i
  anchors_outer := by
    intro i hi
    have hiE : i≠E := (by decide : ∀ j∈({H,A,B,D} : Finset Vertex),j≠E) i hi
    rw [(O.unchanged i hiE).1]
    exact I.anchors_outer i hi
  anchors_normal := O.normal I.anchors_normal
  witnesses := O.witnesses I.witnesses
  zero_signs := O.zero_signs I.witnesses I.zero_signs
  E_nonpos := O.nonpos

end CycleMove

def NegativeDEEndpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : NegativeDEEndpoint q (C.point D) (C.point E) (C.point H)
      (C.theta D-C.theta E) (C.theta H-C.theta E)) : CycleMove q C where
  point := O.point
  theta := C.theta E+O.movement
  sorted := O.sorted
  contained := O.contained
  core := O.core
  nonpos := O.nonpos
  frame_range := by
    have hED : C.theta E≤C.theta D := by linarith [O.negative_remaining,O.movement_nonneg]
    rw [min_eq_left hED,max_eq_right hED]
    constructor <;> linarith [O.negative_remaining,O.movement_nonneg]
  de := 3
  eh := 0
  de_allowed := Or.inr rfl
  eh_allowed := Or.inl rfl
  DE := by convert O.DE3 using 1 <;> ring
  EH := by convert O.EH0 using 1 <;> ring
  positive_nonincrease := by
    have hDEold : positivePart (C.theta E-C.theta D)=0 :=
      max_eq_right (by linarith [O.movement_nonneg,O.negative_remaining])
    have hDEnew : positivePart (C.theta E+O.movement-C.theta D)=0 :=
      max_eq_right (by linarith [O.negative_remaining])
    have hEHold : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E :=
      max_eq_left (by linarith [O.movement_nonneg,O.movement_le_p])
    have hEHnew : positivePart (C.theta H-(C.theta E+O.movement))=
        C.theta H-(C.theta E+O.movement) := max_eq_left (by linarith [O.movement_le_p])
    have heq : positiveVariation C.theta-
        positiveVariation (Function.update C.theta E (C.theta E+O.movement))=O.movement := by
      have hV : ∀ θ : Vertex → ℝ, positiveVariation θ=
          positivePart (θ G-θ H)+positivePart (θ A-θ G)+positivePart (θ B-θ A)+
          positivePart (θ T-θ B)+positivePart (θ D-θ T)+positivePart (θ E-θ D)+
          positivePart (θ H-θ E) := fun θ => by
        simp only [positiveVariation,Fin.sum_univ_seven,delta,next]; rfl
      rw [hV,hV]
      simp only [Function.update_self,Function.update_of_ne (show H≠E by decide),
        Function.update_of_ne (show G≠E by decide),Function.update_of_ne (show A≠E by decide),
        Function.update_of_ne (show B≠E by decide),Function.update_of_ne (show T≠E by decide),
        Function.update_of_ne (show D≠E by decide)]
      rw [hDEold,hDEnew,hEHold,hEHnew]
      ring
    linarith [O.movement_nonneg]

def NegativeEHEndpoint.toCycle {q : ℝ} {C : SignedCycle}
    (O : NegativeEHEndpoint q (C.point D) (C.point E) (C.point H)
      (C.theta E-C.theta D) (C.theta E-C.theta H))
    (hDEpos : C.theta D<C.theta E) : CycleMove q C where
  point := O.point
  theta := C.theta D
  sorted := O.sorted
  contained := O.contained
  core := O.core
  nonpos := O.nonpos
  frame_range := ⟨min_le_right _ _,le_max_right _ _⟩
  de := 2
  eh := 1
  de_allowed := Or.inl rfl
  eh_allowed := Or.inr rfl
  DE := by simpa using O.DE2
  EH := by convert O.EH1 using 1 <;> ring
  positive_nonincrease := by
    have hDEold : positivePart (C.theta E-C.theta D)=C.theta E-C.theta D :=
      max_eq_left (sub_nonneg.mpr hDEpos.le)
    have hDEnew : positivePart (C.theta D-C.theta D)=0 := by simp
    have hEHold : positivePart (C.theta H-C.theta E)=0 :=
      max_eq_right (by linarith [O.negative_remaining])
    have hEHnew : positivePart (C.theta H-C.theta D)=0 :=
      max_eq_right (by linarith [O.negative_remaining])
    have heq : positiveVariation C.theta-
        positiveVariation (Function.update C.theta E (C.theta D))=C.theta E-C.theta D := by
      have hV : ∀ θ : Vertex → ℝ, positiveVariation θ=
          positivePart (θ G-θ H)+positivePart (θ A-θ G)+positivePart (θ B-θ A)+
          positivePart (θ T-θ B)+positivePart (θ D-θ T)+positivePart (θ E-θ D)+
          positivePart (θ H-θ E) := fun θ => by
        simp only [positiveVariation,Fin.sum_univ_seven,delta,next]; rfl
      rw [hV,hV]
      simp only [Function.update_self,Function.update_of_ne (show H≠E by decide),
        Function.update_of_ne (show G≠E by decide),Function.update_of_ne (show A≠E by decide),
        Function.update_of_ne (show B≠E by decide),Function.update_of_ne (show T≠E by decide),
        Function.update_of_ne (show D≠E by decide)]
      rw [hDEold,hDEnew,hEHold,hEHnew]
      ring
    linarith

/-- Same-state secondary selection is also an original-radius move. -/
def identityMove {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hc : (I.cycle.point E).Core) (de eh : Fin 4)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hDE : I.cycle.Feasible D de) (hEH : I.cycle.Feasible E eh) : CycleMove q I.cycle where
  point := I.cycle.point E
  theta := I.cycle.theta E
  sorted := I.necessary.sorted E
  contained := I.necessary.contained E
  core := hc
  nonpos := I.E_nonpos
  frame_range := ⟨min_le_left _ _,le_max_left _ _⟩
  de := de
  eh := eh
  de_allowed := hde
  eh_allowed := heh
  DE := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  EH := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  positive_nonincrease := by simp

end NegativeCoreE
end SquaresInCircles.Eight.TableFree
