module

public import SquaresInCircles.Eight.TableFree.NonpositiveEOrder
public import SquaresInCircles.Eight.TableFree.CanonicalNegativeCycle
public import SquaresInCircles.Eight.TableFree.OrderedHardEndpoint

/-!
# The full nonpositive hard terminal on its original source

Uncompiled source draft.  Both outer errors may be nonzero and E may
start anywhere in the original frame interval, with either weak mixed
owner.  The actual E ordering and small-side transports reduce the finite
terminal alternatives to the aligned or the large-B canonical theorem.

Every loss is compared with the original anchor circle.  The proof first
recovers the original E frame and HG alignment, and then applies the
canonical negative theorem to the untouched source.  No equality of a
transported intermediate with its ancestor is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate GeometricModel ExactFamily

/-- Complete ordered nonpositive terminal, including both possible
large-side alternatives.  Only actual anchor circles are pulled back. -/
theorem HardInput.nonpositive_ordered_anchor_rigidity {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    q=qStar ∧ AllAnchorsOn qStar I.cycle ∧ (I.cycle.point A).y<1/2 := by
  have htrial : q≤qTrial :=
    hqq.trans (GeometricExistence.stationary_radius_ceiling sharpData_stationary).le
  have hcap : q≤qCap := htrial.trans (by norm_num [qTrial,qCap])
  obtain ⟨J,hJAB,hJnorm,hJAG,hJGH,hJDT,hJTB,hJHG,hJTD,hcases,hnon,hstrict,
    hJAy,hJBy,hθ,hfixed⟩ :=
    I.reduce_nonpositive_small_sides hqL hcap hAB hnorm hAG hGH hDT hTB hHG hTD
  have hH := hfixed H (by simp)
  have hD := hfixed D (by simp)
  have hE := hfixed E (by simp)
  have hJDEorder : J.cycle.theta D≤J.cycle.theta E := by
    rw [hD.2,hE.2]; exact hDEorder
  have hJEHorder : J.cycle.theta E≤J.cycle.theta H := by
    rw [hE.2,hH.2]; exact hEHorder
  have hJDE : J.cycle.Feasible D 3 := by
    simpa [Feasible,slack,edge,word,delta,next,D,E,hD.1,hD.2,hE.1,hE.2] using hDE
  have hJEH : J.cycle.Feasible E 1 := by
    simpa [Feasible,slack,edge,word,delta,next,E,H,hE.1,hE.2,hH.1,hH.2] using hEH
  have hsmall : (J.cycle.point A).y<1/2 := by
    by_contra! hlarge
    rcases hcases with ⟨hG,hT⟩ | ⟨hA,hT⟩ | ⟨hB,hG⟩
    · exact J.nonpositive_large_A_ordered_impossible htrial hJAB hJAG hJGH
        (hJDT.trans hJTB) hT hJHG hlarge hJDEorder hJEHorder hJDE hJEH
    · exact J.nonpositive_large_A_ordered_impossible htrial hJAB hJAG hJGH
        (hJDT.trans hJTB) hT hJHG hlarge hJDEorder hJEHorder hJDE hJEH
    · linarith
  have hsharp : q=qStar ∧ AllAnchorsOn qStar J.cycle := by
    rcases hcases with ⟨hG,hT⟩ | ⟨hA,hT⟩ | ⟨hB,hG⟩
    · have hs := J.aligned_ordered_sharp hqq hG hJAB hT
        (hJAG.trans hJGH) (by rw [hJAB]; exact hJDT.trans hJTB)
        hJDEorder hJEHorder
      exact ⟨hs.2.2.1,hs.2.2.2.2.1⟩
    · exact False.elim (lt_asymm hA hsmall)
    · obtain ⟨K,hfixedK,hKED,hnonK,hstrictK,hKDE,hKEH⟩ :=
        J.reduce_nonpositive_large_B_DE htrial hJAB (hJAG.trans hJGH) hG
          hJDT hJTB hJTD hB.le hJDEorder hJEHorder hJDE hJEH
      have hKH := hfixedK H (by decide)
      have hKG := hfixedK G (by decide)
      have hKA := hfixedK A (by decide)
      have hKB := hfixedK B (by decide)
      have hKT := hfixedK T (by decide)
      have hKD := hfixedK D (by decide)
      have hKAB : K.cycle.theta A=K.cycle.theta B := by
        rw [hKA.2,hKB.2]; exact hJAB
      have hKAH : K.cycle.theta A≤K.cycle.theta H := by
        rw [hKA.2,hKH.2]; exact hJAG.trans hJGH
      have hKGH : K.cycle.theta G=K.cycle.theta H := by
        rw [hKG.2,hKH.2]; exact hG
      have hKDT : K.cycle.theta D≤K.cycle.theta T := by
        rw [hKD.2,hKT.2]; exact hJDT
      have hKTB : K.cycle.theta T≤K.cycle.theta B := by
        rw [hKT.2,hKB.2]; exact hJTB
      have hKTD : K.cycle.Feasible T 2 := by
        simpa [Feasible,slack,edge,word,delta,next,T,D,hKT.1,hKT.2,hKD.1,hKD.2]
          using hJTD
      have hKBy : 1/2≤ -(K.cycle.point B).y := by rw [hKB.1]; exact hB.le
      have hs := K.nonpositive_canonical_rigidity sharpData_stationary hqq
        hKAB hKAH hKGH hKDT hKTB hKTD hKBy hKED hKDE hKEH
      exact ⟨hs.1,anchors_tight_before
        (fun i _ => (J.necessary.contained i).trans hqq) hnonK hs.2.2.2.2.1⟩
  refine ⟨hsharp.1,anchors_tight_before
    (fun i _ => (I.necessary.contained i).trans hqq) hnon hsharp.2,?_⟩
  rwa [hJAy] at hsmall

/-- All E frames and both original mixed-owner choices are covered.
The two negative outer errors are resolved on the original source,
including any strict loss already present at its five anchors. -/
theorem HardInput.nonpositive_sharp {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    q=qStar ∧ I.cycle.theta G=I.cycle.theta H ∧
      I.cycle.theta B=I.cycle.theta T ∧ I.cycle.theta T=I.cycle.theta D ∧
      I.cycle.theta E=I.cycle.theta D ∧
      I.cycle.theta H-I.cycle.theta D=FiveCorner.selected.angle ∧
      AllAnchorsOn qStar I.cycle ∧
      ∀ i j,j∈terminalOwners i → I.cycle.slack i j=0 := by
  have htrial : q≤qTrial :=
    hqq.trans (GeometricExistence.stationary_radius_ceiling sharpData_stationary).le
  have hcap : q≤qCap := htrial.trans (by norm_num [qTrial,qCap])
  have source_contained : ∀i∈anchorVertices,(I.cycle.point i).Contained qStar :=
    fun i _ => (I.necessary.contained i).trans hqq
  have ordered_sharp (J : HardInput q)
      (hfixed : ∀i,i≠E → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i)
      (ho : J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H))
      (hDE : J.cycle.Feasible D 3) (hEH : J.cycle.Feasible E 1) :
      q=qStar ∧ AllAnchorsOn qStar J.cycle ∧ (J.cycle.point A).y<1/2 := by
    have hH := hfixed H (by decide)
    have hG := hfixed G (by decide)
    have hA := hfixed A (by decide)
    have hB := hfixed B (by decide)
    have hT := hfixed T (by decide)
    have hD := hfixed D (by decide)
    apply J.nonpositive_ordered_anchor_rigidity hqL hqq
    · rw [hA.2,hB.2]; exact hAB
    · rw [hA.1,hB.1]; exact hnorm
    · rw [hA.2,hG.2]; exact hAG
    · rw [hG.2,hH.2]; exact hGH
    · rw [hD.2,hT.2]; exact hDT
    · rw [hT.2,hB.2]; exact hTB
    · simpa [Feasible,slack,edge,word,delta,next,H,G,hH.1,hH.2,hG.1,hG.2] using hHG
    · simpa [Feasible,slack,edge,word,delta,next,T,D,hT.1,hT.2,hD.1,hD.2] using hTD
    · rw [hD.2]; exact ho.1
    · rw [hH.2]; exact ho.2
    · exact hDE
    · exact hEH
  obtain ⟨J,hfixed,horder,hnon,hstrict,hJDE,hJEH⟩ :=
    I.order_nonpositive_E hqL htrial hAB hnorm hAG hGH hDT hTB hHG hTD
  have hJsharp := ordered_sharp J hfixed horder hJDE hJEH
  have hnolossJ : ¬StrictAnchorLoss I.cycle J.cycle :=
    no_strict_loss_to_on_circle source_contained hJsharp.2.1
  have hDEorder : I.cycle.theta D≤I.cycle.theta E := by
    by_contra! hbelow
    exact hnolossJ (hstrict hbelow)
  have hEHorder := I.nonpositive_E_le_H hqL htrial hAB hnorm hAG hGH hDT hTB hHG hTD
  have hDE := I.nonpositive_DE_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hDEorder
  have hEH := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
  have hAy : (I.cycle.point A).y<1/2 := by
    have hA := (hfixed A (by decide)).1
    rw [hA] at hJsharp
    exact hJsharp.2.2
  have hEy : (I.cycle.point E).y<0 := by
    have hne : (I.cycle.point E).y≠0 := fun hzero =>
      I.nonpositive_zero_E_impossible hcap hAB hAG hGH hDT hTB hHG hTD hzero
        hDEorder hEHorder hDE hEH
    exact lt_of_le_of_ne I.E_nonpos hne
  have hEHlt : I.cycle.theta E<I.cycle.theta H := by
    have hne : I.cycle.theta E≠I.cycle.theta H := fun halign =>
      I.nonpositive_EH_impossible hqL htrial hAB hnorm hAG hGH hDT hTB hHG hTD
        halign hDE hEH
    exact lt_of_le_of_ne hEHorder hne
  have hED : I.cycle.theta E=I.cycle.theta D := by
    by_contra hne
    have hDElt := lt_of_le_of_ne hDEorder (Ne.symm hne)
    obtain ⟨K,hfixedK,horderK,hboundaryK,hnonK,hstrictK,hKDE,hKEH⟩ :=
      I.reduce_nonpositive_E hcap hAB hAG hGH hDT hTB hHG hTD hDEorder hEHorder hDE hEH
    have hKsharp := ordered_sharp K hfixedK horderK hKDE hKEH
    exact no_strict_loss_to_on_circle source_contained hKsharp.2.1
      (hstrictK ⟨hEy,hDElt,hEHlt⟩)
  have hGHframe : I.cycle.theta G=I.cycle.theta H := by
    by_contra hne
    have hGHlt := lt_of_le_of_ne hGH hne
    obtain ⟨K,hKAB,hKnorm,hKAG,hKGH,hKDT,hKTB,hKHG,hKTD,hcases,hnonK,hstrictK,
      hKAy,hKBy,hKθ,hfixedK⟩ :=
      I.reduce_nonpositive_small_sides hqL hcap hAB hnorm hAG hGH hDT hTB hHG hTD
    have hH := hfixedK H (by simp)
    have hD := hfixedK D (by simp)
    have hE := hfixedK E (by simp)
    have hKDEorder : K.cycle.theta D≤K.cycle.theta E := by
      rw [hD.2,hE.2]; exact hDEorder
    have hKEHorder : K.cycle.theta E≤K.cycle.theta H := by
      rw [hE.2,hH.2]; exact hEHorder
    have hKDE : K.cycle.Feasible D 3 := by
      simpa [Feasible,slack,edge,word,delta,next,D,E,hD.1,hD.2,hE.1,hE.2] using hDE
    have hKEH : K.cycle.Feasible E 1 := by
      simpa [Feasible,slack,edge,word,delta,next,E,H,hE.1,hE.2,hH.1,hH.2] using hEH
    have hKsharp := K.nonpositive_ordered_anchor_rigidity hqL hqq hKAB hKnorm
      hKAG hKGH hKDT hKTB hKHG hKTD hKDEorder hKEHorder hKDE hKEH
    exact no_strict_loss_to_on_circle source_contained hKsharp.2.1
      (hstrictK (Or.inl ⟨hGHlt,hAy.le⟩))
  have hBy : 1/2≤ -(I.cycle.point B).y := by linarith
  have hs := I.nonpositive_canonical_rigidity sharpData_stationary hqq hAB
    (hAG.trans hGH) hGHframe hDT hTB hTD hBy hED hDE hEH
  have hBTframe : I.cycle.theta B=I.cycle.theta T := hs.2.1
  have hTDframe : I.cycle.theta T=I.cycle.theta D := hs.2.2.1
  have hADframe : I.cycle.theta A=I.cycle.theta D := hAB.trans (hBTframe.trans hTDframe)
  have hcanonical := I.canonical_sharp hGHframe hAB hTDframe hADframe hED
    (hDT.trans (hTB.trans (by rw [←hAB]; exact hAG.trans hGH))) hEH hqq
  exact ⟨hcanonical.1,hGHframe,hBTframe,hTDframe,hED,hcanonical.2⟩

theorem HardInput.nonpositive_lower_bound {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) : qStar≤q := by
  by_cases h : qStar≤q
  · exact h
  · have hqq := (lt_of_not_ge h).le
    have heq := (I.nonpositive_sharp hqL hqq hAB hnorm hAG hGH hDT hTB hHG hTD).1
    exact heq.symm.le

/-- An inherited strict loss at any rigid anchor cannot reach the
nonpositive terminal, regardless of the original E frame or mixed owner. -/
theorem HardInput.nonpositive_no_source_loss {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hqq : q≤qStar)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    {source : SignedCycle}
    (hc : ∀i∈anchorVertices,(source.point i).Contained q) :
    ¬StrictAnchorLoss source I.cycle := by
  have hs := I.nonpositive_sharp hqL hqq hAB hnorm hAG hGH hDT hTB hHG hTD
  exact no_strict_loss_to_on_circle (fun i hi => (hc i hi).trans hqq)
    hs.2.2.2.2.2.2.1

end SquaresInCircles.Eight.TableFree.SignedCycle
