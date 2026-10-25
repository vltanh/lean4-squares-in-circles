module

public import SquaresInCircles.Eight.Owners.GA.Paired.NegativeEEndpoint
public import SquaresInCircles.Eight.Owners.GA.ETransport
public import SquaresInCircles.Eight.Owners.GA.EZero

/-!
# Eight squares: two negative E primaries reduce to one in a high-GA source domain

`reduce` turns two negative E primaries DE3 and EH1 of a core E into one. If EH0 or DE2 is
feasible, E is reselected at the same state. Otherwise the intrinsic concavity endpoint takes the
place of E in the seven-cycle (`Endpoint.toMove`): its frame stays between the frames of H and D,
both variations are unchanged, and the moved cycle is again a source domain (`Result.source`). The
zero-tangent endpoint is excluded by the reflected BT theorem, and at each of the two other
endpoints an aligned secondary is selected.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PairedNegativeE
open Candidate SignedCycle ETransport

def Endpoint.toMove {q : ℝ} {C : SignedCycle}
    (O : Endpoint q (C.point D) (C.point H) (C.theta D-C.theta H))
    (hDE : delta C.theta D<0) (hEH : delta C.theta E<0) : Move q C where
  point := O.point
  theta := C.theta H+O.x
  sorted := O.sorted
  contained := O.contained
  core := O.core
  flat := O.flat
  nonpos := O.nonpos
  frame_range := by
    have hHD : C.theta H≤C.theta D := by linarith [O.range.1,O.range.2]
    refine ⟨H,D,?_⟩
    rw [min_eq_left hHD,max_eq_right hHD]
    constructor <;> linarith [O.range.1,O.range.2]
  de := 3
  eh := 1
  de_allowed := Or.inr rfl
  eh_allowed := Or.inr rfl
  DE := by convert O.DE3 using 1 <;> ring
  EH := by convert O.EH1 using 1 <;> ring
  positive_nonincrease := by
    have hd : C.theta E<C.theta D := by simpa [delta,next,D,E] using hDE
    have he : C.theta H<C.theta E := by simpa [delta,next,E,H] using hEH
    have hDEold : positivePart (C.theta E-C.theta D)=0 :=
      max_eq_right (sub_nonpos.mpr hd.le)
    have hEHold : positivePart (C.theta H-C.theta E)=0 :=
      max_eq_right (sub_nonpos.mpr he.le)
    have hDEnew : positivePart (C.theta H+O.x-C.theta D)=0 :=
      max_eq_right (by linarith [O.range.2])
    have hEHnew : positivePart (C.theta H-(C.theta H+O.x))=0 :=
      max_eq_right (by linarith [O.range.1])
    have heq : positiveVariation (Function.update C.theta E (C.theta H+O.x))=
        positiveVariation C.theta := by
      have h1 : positivePart (C.theta 0+O.x-C.theta 5)=0 := hDEnew
      have h2 : positivePart (-O.x)=0 := by
        rw [show -O.x=C.theta H-(C.theta H+O.x) by ring]
        exact hEHnew
      have h3 : positivePart (C.theta 6-C.theta 5)=0 := hDEold
      have h4 : positivePart (C.theta 0-C.theta 6)=0 := hEHold
      simp [positiveVariation,Fin.sum_univ_succ,delta,next,H,D,E,Function.update_apply]
      rw [h1,h2,h3,h4]
    exact heq.le

structure Result (q : ℝ) (C : SignedCycle) where
  move : Move q C
  single :
    (move.de=3 ∧ move.eh=0 ∧ delta move.cycle.theta D<0) ∨
    (move.de=2 ∧ move.eh=1 ∧ delta move.cycle.theta E<0)

def Result.source {q : ℝ} {C : SignedCycle} (R : Result q C)
    (I : SourceDomain q C) (hq : q≤qCap) : SourceDomain q R.move.cycle :=
  R.move.source I hq

/-- No new point, endpoint event or feasible descendant is assumed: the intrinsic local theorem
gives them, realized with the neighboring data of the cycle. -/
theorem reduce {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hEc : (C.point E).Core)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 1)
    (hDEneg : delta C.theta D<0) (hEHneg : delta C.theta E<0) :
    Nonempty (Result q C) := by
  have hDE' : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  have hEH' : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  by_cases hEH0 : C.Feasible E 0
  · have hEH0' : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hEH0
    have hf := (NegativeCoreE.secondary_flat (I.necessary.sorted E) I.E_nonpos hEc
      (I.necessary.sorted H) (I.necessary.contained H) hqU hEH0').1
    let O := ETransport.identity I hEc hf 3 0 (Or.inr rfl) (Or.inl rfl) hDE hEH0
    refine ⟨⟨O,Or.inl ⟨rfl,rfl,?_⟩⟩⟩
    simpa [O,ETransport.identity,Move.cycle,replacePoint] using hDEneg
  have hnot : ¬quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
    intro hh
    apply hEH0
    simpa [Feasible,slack,edge,word,delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hD : C.theta E<C.theta D := by simpa [delta,next,D,E] using hDEneg
  have hH : C.theta H<C.theta E := by simpa [delta,next,E,H] using hEHneg
  have ht : C.theta E-C.theta H∈Ioc 0 frameCap :=
    ⟨sub_pos.mpr hH,(le_abs_self _).trans (I.necessary.spread E H)⟩
  obtain ⟨hflat,hP⟩ := actual_parameters (I.necessary.sorted E) hEc I.E_nonpos
    (I.necessary.sorted H) (I.necessary.core H) (I.necessary.contained H)
    I.H_positive.le hqU ht (by simpa only [neg_sub] using hEH')
    (by simpa only [neg_sub] using hnot)
  by_cases hDE2 : C.Feasible D 2
  · let O := ETransport.identity I hEc hflat 2 1 (Or.inl rfl) (Or.inr rfl) hDE2 hEH
    refine ⟨⟨O,Or.inr ⟨rfl,rfl,?_⟩⟩⟩
    simpa [O,ETransport.identity,Move.cycle,replacePoint] using hEHneg
  have hv : C.theta D-C.theta H∈Ioc 0 (7/10:ℝ) :=
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread D H)⟩
  obtain ⟨P⟩ := endpoint hqL hP hflat I.E_nonpos hv
    (show C.theta E-C.theta H∈Ioo 0 (C.theta D-C.theta H) by
      constructor <;> linarith)
    (by convert hDE' using 1; ring)
    (by simpa only [neg_sub] using hEH')
  let O := P.toMove hDEneg hEHneg
  have hzero : P.point.y≠0 := by
    intro hz
    have hq : q∈Icc (5/2:ℝ) Q0 :=
      ⟨(show (5/2:ℝ)≤qLow by norm_num [qLow]).trans hqL,by simpa only [qCap,Q0] using hqU⟩
    have hh := (O.source I hqU).E_negative hq
    change P.point.y<0 at hh
    linarith
  rcases P.terminal with hx | hx | hy
  · have hsecondary : quarterFeasible O.point (C.point H) (C.theta H-O.theta) 0 := by
      have hp : quarterFeasible P.point (C.point H) 0 1 := by simpa [hx] using P.EH1
      have hs := (quarter_low_tie P.point (C.point H)).2 hp
      simpa [O,Endpoint.toMove,hx] using hs
    let O' : Move q C := { O with eh:=0,eh_allowed:=Or.inl rfl,EH:=hsecondary }
    refine ⟨⟨O',Or.inl ⟨rfl,rfl,?_⟩⟩⟩
    change C.theta H+P.x-C.theta D<0
    rw [hx]
    linarith [hv.1]
  · have hsecondary : quarterFeasible (C.point D) O.point (O.theta-C.theta D) 2 := by
      have hp : quarterFeasible (C.point D) P.point 0 3 := by simpa [hx] using P.DE3
      have hs := (quarter_high_tie (C.point D) P.point).2 hp
      have heq : O.theta-C.theta D=0 := by
        dsimp [O,Endpoint.toMove]
        rw [hx]
        ring
      rw [heq]
      exact hs
    let O' : Move q C := { O with de:=2,de_allowed:=Or.inl rfl,DE:=hsecondary }
    refine ⟨⟨O',Or.inr ⟨rfl,rfl,?_⟩⟩⟩
    change C.theta H-(C.theta H+P.x)<0
    rw [hx]
    linarith [hv.1]
  · exact (hzero hy).elim

end SquaresInCircles.Eight.GlobalGA.PairedNegativeE
