module

public import SquaresInCircles.Eight.TableFree.NegativeCoreECycle
public import SquaresInCircles.Eight.TableFree.ActualCoreEBlocks

/-!
# Every negative E-primary total has an actual geometric reduction

Uncompiled source. The endpoint is constructed from the original
normalized boundary cycle. It either has nonnegative retained E total,
or has flat E with both retained primary errors nonpositive. Every
nonincident witness and every G/A/B/T datum is literally unchanged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate ActualCoreEBlocks
namespace NegativeCoreE

theorem CycleMove.primary_DE {q : ℝ} {C : SignedCycle} (O : CycleMove q C) :
    primaryDE O.cycle O.de=if O.de=3 then O.theta-C.theta D else 0 := by
  simp [primaryDE,CycleMove.cycle,replacePoint,delta,next,D,E]

theorem CycleMove.primary_EH {q : ℝ} {C : SignedCycle} (O : CycleMove q C) :
    primaryEH O.cycle O.eh=if O.eh=1 then C.theta H-O.theta else 0 := by
  simp [primaryEH,CycleMove.cycle,replacePoint,delta,next,H,E]

theorem CycleMove.total {q : ℝ} {C : SignedCycle} (O : CycleMove q C) :
    eTotal O.cycle O.de O.eh=
      (if O.de=3 then O.theta-C.theta D else 0)+
      (if O.eh=1 then C.theta H-O.theta else 0) := by
  rw [eTotal,O.primary_DE,O.primary_EH]

structure Reduction (q : ℝ) (I : SignedCycle.NormalizedBoundaryInput q) where
  move : CycleMove q I.cycle
  normal_form : 0≤eTotal move.cycle move.de move.eh ∨
    (move.point.a=7/12 ∧ primaryDE move.cycle move.de≤0 ∧ primaryEH move.cycle move.eh≤0)

/-- A same-state EH0 selection is made only after its original weak
projection is known. The sole retained DE error then decides which
proved stress family applies; it is never silently discarded. -/
theorem reduce_with_secondary {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hq : q≤qCap) (hc : (I.cycle.point E).Core)
    (hEH : I.cycle.Feasible E 0) : Nonempty (Reduction q I) := by
  let de := I.witnesses.owner D
  have hde : de=2 ∨ de=3 := by
    simpa [de,SignedCycle.normalOwners,D] using I.witnesses.allowed D
  let O := identityMove I hc de 0 hde (Or.inl rfl) (I.witnesses.feasible D) hEH
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  have hf := (secondary_flat (I.necessary.sorted E) I.E_nonpos hc
    (I.necessary.sorted H) (I.necessary.contained H) hq hEH').1
  refine ⟨⟨O,?_⟩⟩
  by_cases hpos : 0≤primaryDE O.cycle O.de
  · left
    rw [eTotal,O.primary_EH]
    simpa [O,identityMove] using hpos
  · right
    refine ⟨hf,le_of_lt (lt_of_not_ge hpos),?_⟩
    rw [O.primary_EH]
    norm_num [O,identityMove]

/-- Complete owner and sign split at the original q. The two mixed cases
invoke the actual compact core-arc endpoint and explicit flat-gap endpoint;
no feasibility or terminal-event premise is supplied by the caller. -/
theorem reduce_negative_total {q : ℝ} (I : SignedCycle.NormalizedBoundaryInput q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (I.cycle.point E).Core)
    (hneg : eTotal I.cycle (I.witnesses.owner D) (I.witnesses.owner E)<0) :
    Nonempty (Reduction q I) := by
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact reduce_with_secondary I hqU hc hEH0
  let C := I.cycle
  have heh : I.witnesses.owner E=1 := by
    have hh : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [SignedCycle.normalOwners,E] using I.witnesses.allowed E
    rcases hh with hh | hh
    · exact False.elim (hEH0 (by simpa [hh] using I.witnesses.feasible E))
    · exact hh
  have hde : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [SignedCycle.normalOwners,D] using I.witnesses.allowed D
  have hEH : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    have hh : C.Feasible E 1 := by simpa [C,heh] using I.witnesses.feasible E
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hnot : ¬quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
    intro hh
    apply hEH0
    simpa [C,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := I.necessary.spread (next i) i
  have hflat {n : ℝ} (hn : n∈Ioc 0 frameCap)
      (heq : C.theta H-C.theta E= -n) : (C.point E).a=7/12 :=
    (genuine_negative_flat (I.necessary.sorted E) I.E_nonpos hc
      (I.necessary.sorted H) I.anchors_normal.H_nonneg (I.necessary.contained H)
      hqU hn (by simpa only [heq] using hEH)
      (by simpa only [heq] using hnot)).1
  rcases hde with hde | hde
  · have hr : C.theta H-C.theta E<0 := by
      simpa [eTotal,primaryDE,primaryEH,hde,heh,C,delta,next,H,D,E] using hneg
    have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
      ⟨by linarith,(le_abs_self _).trans (I.necessary.spread E H)⟩
    have hf := hflat hn (by ring)
    let O := identityMove I hc 2 1 (Or.inl rfl) (Or.inr rfl)
      (by simpa [hde] using I.witnesses.feasible D)
      (by simpa [heh] using I.witnesses.feasible E)
    refine ⟨⟨O,Or.inr ⟨hf,?_,?_⟩⟩⟩
    · rw [O.primary_DE]; norm_num [O,identityMove]
    · rw [O.primary_EH]; simpa [O,identityMove,C] using hr.le
  · have hsum : C.theta H-C.theta D<0 := by
      have hh := hneg
      simp [eTotal,primaryDE,primaryEH,hde,heh,C,delta,next,H,D,E] at hh
      linarith
    have hDE : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
      have hh : C.Feasible D 3 := by simpa [C,hde] using I.witnesses.feasible D
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
        delta,next,D,E,quarterFeasible,sub_nonneg] using hh
    by_cases hEHneg : C.theta H<C.theta E
    · have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
        ⟨sub_pos.mpr hEHneg,(le_abs_self _).trans (I.necessary.spread E H)⟩
      have hf := hflat hn (by ring)
      by_cases hDEpos : C.theta D<C.theta E
      · obtain ⟨P⟩ := negative_EH_endpoint hqL hqU
          (I.necessary.sorted D) (I.necessary.core D) (I.anchors_outer D (by simp))
          (I.necessary.sorted H) (I.necessary.core H) I.anchors_normal.H_nonneg
          (I.necessary.contained H) (I.necessary.sorted E) I.E_nonpos hc hn
          ⟨sub_pos.mpr hDEpos,by linarith⟩ hDE
          (by simpa only [neg_sub] using hEH) (by simpa only [neg_sub] using hnot)
        let O := P.toCycle hDEpos
        refine ⟨⟨O,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
        · rw [O.primary_DE]; norm_num [O,NegativeEHEndpoint.toCycle]
        · rw [O.primary_EH]
          simpa [O,NegativeEHEndpoint.toCycle] using hsum.le
      · let O := identityMove I hc 3 1 (Or.inr rfl) (Or.inr rfl)
          (by simpa [hde] using I.witnesses.feasible D)
          (by simpa [heh] using I.witnesses.feasible E)
        refine ⟨⟨O,Or.inr ⟨hf,?_,?_⟩⟩⟩
        · rw [O.primary_DE]
          simpa [O,identityMove,C] using sub_nonpos.mpr (le_of_not_gt hDEpos)
        · rw [O.primary_EH]
          simpa [O,identityMove,C] using (sub_neg.mpr hEHneg).le
    · have hp : 0<C.theta H-C.theta E := by
        have hr0 : 0≤C.theta H-C.theta E := sub_nonneg.mpr (le_of_not_gt hEHneg)
        apply lt_of_le_of_ne hr0
        intro heq
        apply hnot
        simpa [heq.symm,quarterFeasible,quarterProjection] using hEH
      have hn : C.theta D-C.theta E∈Ioc 0 frameCap :=
        ⟨by linarith,(le_abs_self _).trans (I.necessary.spread D E)⟩
      obtain ⟨P⟩ := negative_DE_endpoint hqL hqU (I.necessary.sorted H)
        I.anchors_normal.H_nonneg (I.anchors_outer H (by simp))
        (I.necessary.sorted E) I.E_nonpos hc hn ⟨hp,by linarith⟩
        (by simpa only [neg_sub] using hDE) hEH
      let O := P.toCycle
      refine ⟨⟨O,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
      · rw [O.primary_DE]
        simp only [O,NegativeDEEndpoint.toCycle,ite_true]
        linarith [P.negative_remaining]
      · rw [O.primary_EH]; norm_num [O,NegativeDEEndpoint.toCycle]

end NegativeCoreE
end SquaresInCircles.Eight.TableFree
