module

public import SquaresInCircles.Eight.TableFree.PositiveECandidate
public import SquaresInCircles.Eight.TableFree.PairOrder

/-!
# Insertion of a positive E-pair candidate into the original seven-cycle

Uncompiled source. Exactly E is replaced, at the same common radius.
The other six coordinates and frames, and all five nonincident weak
owners, remain literal. Both signed variations are unchanged because
the two original and two new E errors are nonnegative with equal sum.
Physical winding is derived from the actual normal-owner geometry.
The output is deliberately a sign-free BoundaryInput.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.PositiveEPair
open Candidate

namespace Endpoint
variable {q : ℝ} {C : SignedCycle}

def cycle (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) : SignedCycle :=
  replacePoint C E F.point (C.theta D+F.deError)

def deOwner (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) : Fin 4 :=
  if F.deError=0 then 2 else 3

def ehOwner (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) : Fin 4 :=
  if F.deError=C.theta H-C.theta D then 0 else 1

theorem unchanged (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (i : Vertex) (hi : i≠E) : F.cycle.point i=C.point i ∧ F.cycle.theta i=C.theta i := by
  simp [cycle,replacePoint,hi]

theorem delta_DE (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    delta F.cycle.theta D=F.deError := by simp [cycle,replacePoint,delta,next,D,E]

theorem delta_EH (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    delta F.cycle.theta E=C.theta H-C.theta D-F.deError := by
  simp [cycle,replacePoint,delta,next,H,D,E]
  ring

theorem other_delta (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (i : Vertex) (hiD : i≠D) (hiE : i≠E) : delta F.cycle.theta i=delta C.theta i := by
  have hn : next i≠E := by fin_cases i <;> norm_num [next,D,E] at hiD ⊢
  simp [delta,(F.unchanged i hiE).2,(F.unchanged (next i) hn).2]

theorem other_feasible (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (i : Vertex) (hiD : i≠D) (hiE : i≠E) (j : Fin 4) :
    F.cycle.Feasible i j ↔ C.Feasible i j := by
  have hn : next i≠E := by fin_cases i <;> norm_num [next,D,E] at hiD ⊢
  exact SignedCycle.replacePoint_other_feasible hiE hn

theorem DE_primary (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible D 3 := by
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
    word,delta,next,D,E,quarterFeasible,sub_nonneg] using F.DE

theorem EH_primary (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible E 1 := by
  have herr : C.theta H-(C.theta D+F.deError)=C.theta H-C.theta D-F.deError := by ring
  simpa [cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
    word,delta,next,H,D,E,herr,quarterFeasible,sub_nonneg] using F.EH

theorem DE_actual (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible D F.deOwner := by
  by_cases hz : F.deError=0
  · have hh := F.DE_aligned hz
    simpa [deOwner,hz,cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,D,E,quarterFeasible,sub_nonneg] using hh
  · simpa [deOwner,hz] using F.DE_primary

theorem EH_actual (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    F.cycle.Feasible E F.ehOwner := by
  by_cases hz : F.deError=C.theta H-C.theta D
  · have hh := F.EH_aligned hz
    have herr : C.theta H-(C.theta D+F.deError)=0 := by linarith
    simpa [ehOwner,hz,cycle,replacePoint,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,
      word,delta,next,H,D,E,herr,quarterFeasible,sub_nonneg] using hh
  · simpa [ehOwner,hz] using F.EH_primary

theorem frame_range (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D)) :
    C.theta D+F.deError∈Icc (min (C.theta D) (C.theta H)) (max (C.theta D) (C.theta H)) := by
  have hDH : C.theta D≤C.theta H := by linarith [F.de_mem.1,F.de_mem.2]
  rw [min_eq_left hDH,max_eq_right hDH]
  constructor <;> linarith [F.de_mem.1,F.de_mem.2]

theorem necessary (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hn : C.Necessary q) : F.cycle.Necessary q :=
  SignedCycle.necessary_replace_clamped (v := E) (a := D) (b := H)
    hn F.sorted F.outer.le F.core (Or.inr F.frame_range)

theorem normal (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hn : C.NormalAnchors) : F.cycle.NormalAnchors := by
  constructor
  · rw [(F.unchanged H (by decide)).1]; exact hn.H_nonneg
  · rw [(F.unchanged A (by decide)).1]; exact hn.A_nonneg
  · rw [(F.unchanged B (by decide)).1]; exact hn.B_nonpos
  · rw [(F.unchanged D (by decide)).1]; exact hn.D_nonpos

def witnesses (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (w : C.Witnesses) : F.cycle.Witnesses where
  owner := Function.update (Function.update w.owner D F.deOwner) E F.ehOwner
  feasible i := by
    by_cases hiE : i=E
    · subst i; simpa using F.EH_actual
    · by_cases hiD : i=D
      · subst i; simpa [D,E] using F.DE_actual
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using
          (F.other_feasible i hiD hiE (w.owner i)).2 (w.feasible i)
  allowed i := by
    by_cases hiE : i=E
    · subst i
      simp [SignedCycle.normalOwners,E,ehOwner]
    · by_cases hiD : i=D
      · subst i
        simp [SignedCycle.normalOwners,D,E,deOwner]
      · simpa [Function.update_of_ne hiE,Function.update_of_ne hiD] using w.allowed i

theorem other_owner (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (w : C.Witnesses) (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
    (F.witnesses w).owner i=w.owner i := by simp [witnesses,hiD,hiE]

theorem zero_signs (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) :
    F.cycle.ZeroSignImplications (F.witnesses w) := by
  constructor
  · intro hj
    rw [(F.unchanged G (by decide)).1]
    apply hz.HG_canceling
    simpa [witnesses,H,D,E] using hj
  · intro hj
    rw [(F.unchanged T (by decide)).1]
    apply hz.TD_canceling
    simpa [witnesses,T,D,E] using hj

theorem positive_variation_eq (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hDE : 0≤delta C.theta D) (hEH : 0≤delta C.theta E) :
    positiveVariation F.cycle.theta=positiveVariation C.theta := by
  have hDEold : positivePart (C.theta E-C.theta D)=C.theta E-C.theta D := max_eq_left hDE
  have hEHold : positivePart (C.theta H-C.theta E)=C.theta H-C.theta E := max_eq_left hEH
  have hDEnew : positivePart F.deError=F.deError := max_eq_left F.de_mem.1
  have hEHnew : positivePart (C.theta H-C.theta D-F.deError)=
      C.theta H-C.theta D-F.deError := max_eq_left (by linarith [F.de_mem.2])
  have herr : C.theta H-(C.theta D+F.deError)=C.theta H-C.theta D-F.deError := by ring
  simp [positiveVariation,Fin.sum_univ_succ,delta,next,cycle,replacePoint,
    H,G,A,B,T,D,E,Function.update_apply,herr,hDEold,hEHold,hDEnew,hEHnew]
  ring

theorem negative_variation_eq (F : Endpoint q (C.point D) (C.point H) (C.theta H-C.theta D))
    (hDE : 0≤delta C.theta D) (hEH : 0≤delta C.theta E) :
    negativeVariation F.cycle.theta=negativeVariation C.theta := by
  rw [← variations_equal F.cycle.theta,← variations_equal C.theta]
  exact F.positive_variation_eq hDE hEH

def boundaryInput (I : SignedCycle.BoundaryInput q) (hq : q≤qCap)
    (F : Endpoint q (I.cycle.point D) (I.cycle.point H) (I.cycle.theta H-I.cycle.theta D))
    (hDE : 0≤delta I.cycle.theta D) (hEH : 0≤delta I.cycle.theta E) :
    SignedCycle.BoundaryInput q where
  cycle := F.cycle
  necessary := F.necessary I.necessary
  ordered := SignedCycle.normal_necessary_ordered (F.necessary I.necessary) hq
    (F.normal I.anchors_normal) (F.witnesses I.witnesses) (F.zero_signs I.witnesses I.zero_signs)
  strict_spread := SignedCycle.strictSpread_replace_clamped (v := E) (a := D) (b := H)
    (p := F.point) I.strict_spread (Or.inr F.frame_range)
  positive_variation := by rw [F.positive_variation_eq hDE hEH]; exact I.positive_variation
  negative_variation := by rw [F.negative_variation_eq hDE hEH]; exact I.negative_variation
  radial := by
    intro i
    by_cases hi : i=E
    · subst i; exact Or.inl F.outer
    · rw [(F.unchanged i hi).1]; exact I.radial i
  anchors_outer := by
    intro i hi
    have hiE : i≠E := by fin_cases i <;> norm_num [H,A,B,D,E] at hi ⊢
    rw [(F.unchanged i hiE).1]
    exact I.anchors_outer i hi
  anchors_normal := F.normal I.anchors_normal
  witnesses := F.witnesses I.witnesses
  zero_signs := F.zero_signs I.witnesses I.zero_signs

end Endpoint

theorem original_candidate {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1)
    (hd : 0≤delta I.cycle.theta D) (he : 0≤delta I.cycle.theta E)
    (ht0 : 0<I.cycle.theta H-I.cycle.theta D) :
    Nonempty (Endpoint q (I.cycle.point D) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta D)) := by
  have hsum : delta I.cycle.theta D+delta I.cycle.theta E=I.cycle.theta H-I.cycle.theta D := by
    simp [delta,next,D,E,H]
    ring
  have ht : I.cycle.theta H-I.cycle.theta D≤7/10 :=
    (le_abs_self _).trans (I.necessary.spread H D)
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E) (delta I.cycle.theta D) 3 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,D,next,
      quarterFeasible,sub_nonneg] using hDE
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H) (delta I.cycle.theta E) 1 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,E,next,
      quarterFeasible,sub_nonneg] using hEH
  have hh := candidate hQL hQU (I.necessary.sorted D) (I.anchors_outer D (by simp))
    (I.necessary.sorted H) (I.anchors_outer H (by simp))
    (I.necessary.sorted E) (I.necessary.contained E) hd he
    (by rwa [hsum]) (by rwa [hsum]) hDE' hEH'
  simpa only [hsum] using hh

end SquaresInCircles.Eight.TableFree.PositiveEPair
