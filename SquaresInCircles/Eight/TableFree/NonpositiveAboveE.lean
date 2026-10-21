module

public import SquaresInCircles.Eight.TableFree.NonpositiveEH1Transport
public import SquaresInCircles.Eight.TableFree.NonpositiveEOutsideCycle

/-!
# No original nonpositive E frame lies above H

Uncompiled reconstruction.  The primary EH1 source moves on E's own
original circle.  The actual source radial inequality supplies the
primary reserve used in that construction.  Every non-E point, frame,
and unaffected owner is literal at the resulting E=H cycle.  Combining
this with the rotated EH0 gate exhausts the original allowed EH owners.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate

/-- A primary source above H reaches an actual same-q E=H cycle on
exactly its original E circle.  The endpoint has strict actual DE slack,
and no loss is charged to a circle which was only lifted to a cap. -/
theorem HardInput.nonpositive_above_EH1_endpoint {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta H<I.cycle.theta E)
    (hEH1 : I.cycle.Feasible E 1) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      (∀i, (J.cycle.point i).circle=(I.cycle.point i).circle) ∧
      (∀i, i≠D → i≠E → J.witnesses.owner i=I.witnesses.owner i) ∧
      J.cycle.theta E=I.cycle.theta H ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 ∧ 0<J.cycle.slack D 3 := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonneg I.anchors_normal.H_nonneg] using hh
  have hEa : (353/500:ℝ)<(I.cycle.point E).a := hb.H_tangent.1.trans_le hHrad
  have hEu := (SignedPoint.coordinate_bounds (I.necessary.sorted E)
    (I.necessary.core E) (I.necessary.contained E) hq).2.1
  have hDEorder : I.cycle.theta D≤I.cycle.theta E :=
    (sub_nonneg.mp hb.span_nonneg).trans hEHorder.le
  have hDE := I.nonpositive_DE_primary_of_nonneg hq hAB hAG hGH hDT hTB hHG hTD hDEorder
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta E-I.cycle.theta H
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hx : x∈Ioc 0 (7/10:ℝ) :=
    ⟨sub_pos.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread E H)⟩
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread E D)
    dsimp [α,x,frameCap] at *
    linarith
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E) (α+x) 3 := by
    have heq : α+x=I.cycle.theta E-I.cycle.theta D := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H) (-x) 1 := by
    have heq : -x=I.cycle.theta H-I.cycle.theta E := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH1
  obtain ⟨P,hP,hPangle,hPcircle,hPDE,hPEH⟩ :=
    NonpositiveEH1Transport.endpoint_state hb.H_primary.2 (I.necessary.sorted E)
      hEa hEu I.E_nonpos (I.necessary.contained E) hα hx hsum hDE' hEH'
  let J := I.fromNonpositiveEInterior hq hb hP
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  have hcircle (i : Vertex) : (J.cycle.point i).circle=(I.cycle.point i).circle := by
    by_cases hi : i=E
    · subst i
      exact (eInteriorCycle_circle hP.b_nonneg).trans hPcircle
    · rw [(hfixed i hi).1]
  have howner (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
      J.witnesses.owner i=I.witnesses.owner i := by
    simp [J,HardInput.fromNonpositiveEInterior,Witnesses.eInterior,hiD,hiE]
  have hJEHframe : J.cycle.theta E=I.cycle.theta H := by
    change I.cycle.theta D+P.2.2=I.cycle.theta H
    rw [hPangle]
    dsimp [α]
    ring
  have hJDE : J.cycle.Feasible D 3 := eInteriorCycle_DE (by linarith [hb.span_lt]) hP
  have hJEH : J.cycle.Feasible E 1 := eInteriorCycle_EH (by linarith [hb.span_lt]) hP
  have hstrict : 0<J.cycle.slack D 3 := by
    have hu : P.2.2∈Icc 0 (7/10:ℝ) :=
      ⟨hP.angle.1,by linarith [hP.angle.2,hb.span_lt]⟩
    have hw : EInteriorGeometry.W P.2.2=edgeWidth P.2.2 := by
      rw [edgeWidth_positive_formula hu]
      rfl
    rw [hw] at hPDE
    change 0<(eInteriorCycle I.cycle P).slack D 3
    simpa [eInteriorCycle,slack,edge,word,delta,next,D,E,
      EInteriorGeometry.deValue,quarterProjection,sub_pos] using hPDE
  exact ⟨J,hfixed,hcircle,howner,hJEHframe,hJDE,hJEH,hstrict⟩

theorem HardInput.nonpositive_above_EH1_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta H<I.cycle.theta E)
    (hEH1 : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  obtain ⟨J,hfixed,hcircle,howner,hJEHframe,hJDE,hJEH,hstrict⟩ :=
    I.nonpositive_above_EH1_endpoint hcap hAB hAG hGH hDT hTB hHG hTD hEHorder hEH1
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  apply J.nonpositive_EH_impossible hqL hq
  · rw [hA.2,hB.2]; exact hAB
  · rw [hA.1,hB.1]; exact hnorm
  · rw [hA.2,hG.2]; exact hAG
  · rw [hG.2,hH.2]; exact hGH
  · rw [hD.2,hT.2]; exact hDT
  · rw [hT.2,hB.2]; exact hTB
  · simpa [Feasible,slack,edge,word,delta,next,H,G,hH.1,hH.2,hG.1,hG.2] using hHG
  · simpa [Feasible,slack,edge,word,delta,next,T,D,hT.1,hT.2,hD.1,hD.2] using hTD
  · exact hJEHframe.trans hH.2.symm
  · exact hJDE
  · exact hJEH

/-- Exhaustion is over the actual selected original EH owner.  There
is no frame-placement hypothesis on the original E. -/
theorem HardInput.nonpositive_E_le_H {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    I.cycle.theta E≤I.cycle.theta H := by
  by_contra! habove
  have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [normalOwners,E] using I.witnesses.allowed E
  rcases hj with hj | hj
  · have hEH0 : I.cycle.Feasible E 0 := by simpa [hj] using I.witnesses.feasible E
    exact I.nonpositive_above_EH0_impossible hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
      habove hEH0
  · have hEH1 : I.cycle.Feasible E 1 := by simpa [hj] using I.witnesses.feasible E
    exact I.nonpositive_above_EH1_impossible hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
      habove hEH1

end SquaresInCircles.Eight.TableFree.SignedCycle
