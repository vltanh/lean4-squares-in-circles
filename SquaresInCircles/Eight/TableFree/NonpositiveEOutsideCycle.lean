module

public import SquaresInCircles.Eight.TableFree.NonpositiveEH0Transport
public import SquaresInCircles.Eight.TableFree.NegativeLargeBEEndpoint
public import SquaresInCircles.Eight.TableFree.NonpositiveOuterReduction
public import SquaresInCircles.Eight.TableFree.EpsilonGeometry

/-!
# Actual mixed-owner gates outside the nonpositive H--D interval

Uncompiled reconstruction.  Each nonnegative mixed error supplies its
actual primary axis independently of the sign of the other error.  The
E=H barrier is proved after the concrete small-side transports, rather
than assumed as a terminal hypothesis.  The rotated EH0 construction
above H is then inserted into the actual same-q necessary cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate AlignedMixedE

theorem HardInput.nonpositive_DE_primary_of_nonneg {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E) : I.cycle.Feasible D 3 := by
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hDrad : -(I.cycle.point D).y≤(I.cycle.point E).a := by
    have hh := (le_max_right |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using hh
  have hu : I.cycle.theta E-I.cycle.theta D∈Icc 0 (7/10:ℝ) :=
    ⟨sub_nonneg.mpr hDEorder,(le_abs_self _).trans (I.necessary.spread E D)⟩
  have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
    simpa [normalOwners,D] using I.witnesses.allowed D
  rcases hj with hj | hj
  · have hsource : quarterFeasible (I.cycle.point D) (I.cycle.point E)
        (I.cycle.theta E-I.cycle.theta D) 2 := by
      simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,hj]
        using I.witnesses.feasible D
    have hh := DE_primary_of_nonneg (I.necessary.sorted D) (I.necessary.sorted E)
      I.anchors_normal.D_nonpos I.E_nonpos hDrad hu hsource
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg] using hh
  · simpa [hj] using I.witnesses.feasible D

theorem HardInput.nonpositive_EH_primary_of_nonneg {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) : I.cycle.Feasible E 1 := by
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonneg I.anchors_normal.H_nonneg] using hh
  have hv : I.cycle.theta H-I.cycle.theta E∈Icc 0 (7/10:ℝ) :=
    ⟨sub_nonneg.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread H E)⟩
  have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [normalOwners,E] using I.witnesses.allowed E
  rcases hj with hj | hj
  · have hsource : quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,hj]
        using I.witnesses.feasible E
    have hh := EH_primary_of_nonneg (I.necessary.sorted H).1.le
      I.E_nonpos hHrad hv hsource
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg] using hh
  · simpa [hj] using I.witnesses.feasible E

/-- The original nonpositive cycle cannot have E=H.  The three outer
alternatives are produced by the actual small-side construction here. -/
theorem HardInput.nonpositive_EH_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  obtain ⟨J,hJAB,hJnorm,hJAG,hJGH,hJDT,hJTB,hJHG,hJTD,hcases,hnon,hstrict,
    hJAy,hJBy,hθ,hfixed⟩ :=
    I.reduce_nonpositive_small_sides hqL hcap hAB hnorm hAG hGH hDT hTB hHG hTD
  have hH := hfixed H (by simp)
  have hD := hfixed D (by simp)
  have hE := hfixed E (by simp)
  have hJframe : J.cycle.theta E=J.cycle.theta H := by rw [hE.2,hH.2]; exact hEHframe
  have hJDE : J.cycle.Feasible D 3 := by
    simpa [Feasible,slack,edge,word,delta,next,D,E,hD.1,hD.2,hE.1,hE.2] using hDE
  have hJEH : J.cycle.Feasible E 1 := by
    simpa [Feasible,slack,edge,word,delta,next,E,H,hE.1,hE.2,hH.1,hH.2] using hEH
  rcases hcases with ⟨hHGframe,hTDframe⟩ | ⟨hAy,hTDframe⟩ | ⟨hBy,hHGframe⟩
  · exact J.aligned_epsilon_zero_impossible hcap hHGframe hJAB hTDframe
      (hJAG.trans hJGH) (by rw [hJAB]; exact hJDT.trans hJTB) hJframe hJDE hJEH
  · exact J.nonpositive_large_A_EH_impossible hcap hJAG hJGH hJHG hAy.le hJframe hJEH
  · exact J.nonpositive_large_B_EH_impossible hq hJAB (hJAG.trans hJGH) hHGframe
      hJDT hJTB hJTD hBy.le hJframe hJDE hJEH

/-- Every rotated EH0 source strictly above H constructs the excluded
E=H endpoint on the same q-circle.  The original DE witness is first
upgraded at that same source point; every non-E point is retained. -/
theorem HardInput.nonpositive_above_EH0_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta H<I.cycle.theta E)
    (hEH0 : I.cycle.Feasible E 0) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hDEorder : I.cycle.theta D≤I.cycle.theta E := by
    have hDH : I.cycle.theta D≤I.cycle.theta H := sub_nonneg.mp hb.span_nonneg
    exact hDH.trans hEHorder.le
  have hDE := I.nonpositive_DE_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hDEorder
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
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H) (-x) 0 := by
    have heq : -x=I.cycle.theta H-I.cycle.theta E := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH0
  obtain ⟨P,hP,hPangle,hPDE,hPEH⟩ := NonpositiveEH0Transport.endpoint_state hqL hcap
    hb.H_primary.1 hb.H_primary.2 hb.H_tangent.1 (I.necessary.sorted E) I.E_nonpos
    (I.necessary.contained E) hα hx hsum hDE' hEH'
  let J := I.fromNonpositiveEInterior hcap hb hP
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  have hJEHframe : J.cycle.theta E=J.cycle.theta H := by
    rw [hH.2]
    change I.cycle.theta D+P.2.2=I.cycle.theta H
    rw [hPangle]
    dsimp [α]
    ring
  have hJDE : J.cycle.Feasible D 3 := eInteriorCycle_DE (by linarith [hb.span_lt]) hP
  have hJEH : J.cycle.Feasible E 1 := eInteriorCycle_EH (by linarith [hb.span_lt]) hP
  apply J.nonpositive_EH_impossible hqL hq
  · rw [hA.2,hB.2]; exact hAB
  · rw [hA.1,hB.1]; exact hnorm
  · rw [hA.2,hG.2]; exact hAG
  · rw [hG.2,hH.2]; exact hGH
  · rw [hD.2,hT.2]; exact hDT
  · rw [hT.2,hB.2]; exact hTB
  · simpa [Feasible,slack,edge,word,delta,next,H,G,hH.1,hH.2,hG.1,hG.2] using hHG
  · simpa [Feasible,slack,edge,word,delta,next,T,D,hT.1,hT.2,hD.1,hD.2] using hTD
  · exact hJEHframe
  · exact hJDE
  · exact hJEH

end SquaresInCircles.Eight.TableFree.SignedCycle
