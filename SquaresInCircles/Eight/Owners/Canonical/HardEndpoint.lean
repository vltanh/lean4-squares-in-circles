module

public import SquaresInCircles.Eight.Boundary.SourceRecovery
public import SquaresInCircles.Eight.Words.Aligned.GAEndpointStress
public import SquaresInCircles.Eight.Owners.Ordered.CancelingSplit

/-!
# Eight squares: the actual delta-zero hard branch reaches the geometric endpoint

The common frame shift below preserves every signed
point and every original SAT slack.  It is used only to express an actual
two-frame endpoint in the convention of the five-corner theorem.

For an aligned hard chain with E in D's frame, the same-radius hard split
has two possible endpoints.  The actual GA--DE endpoint is impossible;
the surviving endpoint is the geometric five-corner chain.  Strict losses
on the original A/B circles exclude an interior source split at equality.
No circle equality is assumed of either free intermediate.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Candidate GeometricModel Stationary
namespace SignedCycle

/-- A common physical rotation, leaving all own-frame coordinates literal. -/
def shiftFrame (C : SignedCycle) (r : ℝ) : SignedCycle where
  point := C.point
  theta i := C.theta i-r

@[simp] theorem shiftFrame_point (C : SignedCycle) (r : ℝ) (i : Vertex) :
    (C.shiftFrame r).point i=C.point i := rfl

theorem shiftFrame_delta (C : SignedCycle) (r : ℝ) (i : Vertex) :
    delta (C.shiftFrame r).theta i=delta C.theta i := by
  dsimp [shiftFrame,delta]
  ring

@[simp] theorem shiftFrame_slack (C : SignedCycle) (r : ℝ)
    (i : Vertex) (j : Fin 4) : (C.shiftFrame r).slack i j=C.slack i j := by
  simp only [slack,shiftFrame_delta,edge,shiftFrame_point]

@[simp] theorem shiftFrame_feasible (C : SignedCycle) (r : ℝ)
    (i : Vertex) (j : Fin 4) :
    (C.shiftFrame r).Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,shiftFrame_slack]

theorem canonical_shift_theta {C : SignedCycle}
    (hHG : C.theta G=C.theta H) (hAB : C.theta A=C.theta B)
    (hTD : C.theta T=C.theta D) (hAD : C.theta A=C.theta D)
    (hED : C.theta E=C.theta D) :
    (C.shiftFrame (C.theta D)).theta=
      SourceRecovery.endpointTheta (C.theta H-C.theta D) := by
  have hBD : C.theta B=C.theta D := hAB.symm.trans hAD
  simp only [H,G,A,B,T,D,E] at hHG hAB hTD hAD hED hBD
  funext i
  fin_cases i <;>
    simp [shiftFrame,SourceRecovery.endpointTheta,H,D,hHG,hBD,hTD,hAD,hED]

/-- Select the actual hard axes and retain the original weak zero owners.
The only additional mixed axis needed here is the original EH1 witness. -/
def canonicalOwner {C : SignedCycle} (w : C.Witnesses) : Vertex → Fin 4 :=
  ![w.owner H,0,w.owner A,2,w.owner T,w.owner D,1]

theorem canonicalOwner_allowed {C : SignedCycle} (w : C.Witnesses) :
    ∀ i,canonicalOwner w i∈terminalOwners i := by
  intro i
  have hH := w.allowed H
  have hA := w.allowed A
  have hT := w.allowed T
  have hD := w.allowed D
  fin_cases i
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hH
  · simp [canonicalOwner,terminalOwners,H,A,T,D]
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hA
  · simp [canonicalOwner,terminalOwners,H,A,T,D]
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hT
  · simpa [canonicalOwner,normalOwners,terminalOwners,H,G,A,B,T,D,E] using hD
  · simp [canonicalOwner,terminalOwners,H,A,T,D]

theorem HardInput.canonicalOwner_feasible {q : ℝ} (I : HardInput q)
    (hEH : I.cycle.Feasible E 1) :
    ∀ i,I.cycle.Feasible i (canonicalOwner I.witnesses i) := by
  intro i
  fin_cases i
  · exact I.witnesses.feasible H
  · exact I.GA_hard
  · exact I.witnesses.feasible A
  · exact I.BT_hard
  · exact I.witnesses.feasible T
  · exact I.witnesses.feasible D
  · exact hEH

theorem HardInput.canonical_tilt {q : ℝ} (I : HardInput q)
    (horder : I.cycle.theta D≤I.cycle.theta H) :
    0≤I.cycle.theta H-I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D≤Real.pi/4 := by
  have hs := (abs_le.mp (I.necessary.spread H D)).2
  refine ⟨sub_nonneg.mpr horder,?_⟩
  dsimp [frameCap] at hs
  linarith [Real.pi_gt_three]

theorem HardInput.canonical_lower_bound {q : ℝ} (I : HardInput q)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hAD : I.cycle.theta A=I.cycle.theta D)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (horder : I.cycle.theta D≤I.cycle.theta H)
    (hEH : I.cycle.Feasible E 1) : qStar≤q := by
  exact SourceRecovery.endpoint_lower_bound (I.canonical_tilt horder)
    (canonical_shift_theta hHG hAB hTD hAD hED)
    I.necessary.sorted I.necessary.contained (canonicalOwner I.witnesses)
    (canonicalOwner_allowed I.witnesses)
    (fun i => (shiftFrame_feasible _ _ _ _).2 (I.canonicalOwner_feasible hEH i))

/-- The endpoint conclusions concern the source's own five anchor circles
and its own signed slacks, because the common shift changes neither. -/
theorem HardInput.canonical_sharp {q : ℝ} (I : HardInput q)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hAD : I.cycle.theta A=I.cycle.theta D)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (horder : I.cycle.theta D≤I.cycle.theta H)
    (hEH : I.cycle.Feasible E 1) (hq : q≤qStar) :
    q=qStar ∧ I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have htheta := canonical_shift_theta hHG hAB hTD hAD hED
  have ht := I.canonical_tilt horder
  have hp := canonicalOwner_allowed I.witnesses
  have hf : ∀ i,(I.cycle.shiftFrame (I.cycle.theta D)).Feasible i
      (canonicalOwner I.witnesses i) :=
    fun i => (shiftFrame_feasible _ _ _ _).2 (I.canonicalOwner_feasible hEH i)
  have hslack := SourceRecovery.endpoint_all_slacks_zero ht htheta
    I.necessary.sorted I.necessary.contained (canonicalOwner I.witnesses) hp hf hq
  have hcircle := SourceRecovery.endpoint_all_anchors_on ht htheta
    I.necessary.sorted I.necessary.contained (canonicalOwner I.witnesses) hp hf hq
  refine ⟨le_antisymm hq (I.canonical_lower_bound hHG hAB hTD hAD hED horder hEH),
    hslack.1,hcircle,?_⟩
  intro i j hj
  simpa only [shiftFrame_slack] using hslack.2 i j hj

/-- Split the actual A/B pair while retaining H, D, E and their two mixed
contacts.  The other split endpoint is excluded at the original qCap. -/
theorem HardInput.delta_zero_canonical_split {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta D ∧
      J.cycle.theta E=J.cycle.theta D ∧
      J.cycle.theta D≤J.cycle.theta H ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta A<I.cycle.theta H ∧ I.cycle.theta D<I.cycle.theta A →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨J,hend,hJAB,hnon,hstrict,hfixed⟩ :=
    I.split_with_source_loss hq hHG hAB.symm hTD
      (by simpa [hHG] using hleft) (by simpa [hTD] using hright)
  have hH := hfixed H (by decide) (by decide)
  have hG := hfixed G (by decide) (by decide)
  have hT := hfixed T (by decide) (by decide)
  have hD := hfixed D (by decide) (by decide)
  have hE := hfixed E (by decide) (by decide)
  have hJHG : J.cycle.theta G=J.cycle.theta H := by rw [hG.2,hH.2,hHG]
  have hJTD : J.cycle.theta T=J.cycle.theta D := by rw [hT.2,hD.2,hTD]
  have hJED : J.cycle.theta E=J.cycle.theta D := by rw [hE.2,hD.2,hED]
  have hJorder : J.cycle.theta D≤J.cycle.theta H := by
    rw [hD.2,hH.2]
    exact hright.trans hleft
  have hJDE : J.cycle.Feasible D 3 := by
    have e : J.cycle.slack D 3=I.cycle.slack D 3 := by
      simp only [slack,edge,delta,show next D=E from rfl,hD.1,hD.2,hE.1,hE.2]
    rw [Feasible,e]
    exact hDE
  have hJEH : J.cycle.Feasible E 1 := by
    have e : J.cycle.slack E 1=I.cycle.slack E 1 := by
      simp only [slack,edge,delta,show next E=H from rfl,hE.1,hE.2,hH.1,hH.2]
    rw [Feasible,e]
    exact hEH
  have hJAD : J.cycle.theta A=J.cycle.theta D := by
    rcases hend with h | h
    · have hAH := h.trans hJHG
      exact (J.aligned_GA_DE_impossible hq hJHG hJAB hJTD hAH hJED
        (by simpa [hAH] using hJorder) hJDE hJEH).elim
    · exact h.trans hJTD
  refine ⟨J,hJHG,hJAB,hJTD,hJAD,hJED,hJorder,hJDE,hJEH,hnon,?_,hfixed⟩
  intro hi
  apply hstrict
  simpa [hHG,hTD] using hi

/-- Equality is pulled back to the unchanged source frame data.  An
interior source split would strictly reduce an original A/B circle, whereas
the actual endpoint's five circles are all qStar. -/
theorem HardInput.delta_zero_sharp {q : ℝ} (I : HardInput q) (hq : q≤qStar)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta H)
    (hright : I.cycle.theta D≤I.cycle.theta A)
    (hED : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    I.cycle.theta A=I.cycle.theta D ∧ q=qStar ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have hQ : q≤qCap := hq.trans qStar_limits.2.2.le
  obtain ⟨J,hG,hAB',hT,hAD,hED',ho,hD,hE,hnon,hstrict,hfixed⟩ :=
    I.delta_zero_canonical_split hQ hHG hAB hTD hleft hright hED hDE hEH
  have hsharp := J.canonical_sharp hG hAB' hT hAD hED' ho hE hq
  have hnoloss : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle
      (fun i _ => (I.necessary.contained i).trans hq) hsharp.2.2.1
  have hADsource : I.cycle.theta A=I.cycle.theta D := by
    by_contra hne
    have hDA : I.cycle.theta D<I.cycle.theta A := lt_of_le_of_ne hright (Ne.symm hne)
    have hAH : I.cycle.theta A<I.cycle.theta H := by
      rcases lt_or_eq_of_le hleft with h | h
      · exact h
      · exact (I.aligned_GA_DE_impossible hQ hHG hAB hTD h hED hright hDE hEH).elim
    exact hnoloss (hstrict ⟨hAH,hDA⟩)
  exact ⟨hADsource,I.canonical_sharp hHG hAB hTD hADsource hED
    (hright.trans hleft) hEH hq⟩

end SignedCycle
end SquaresInCircles.Eight
