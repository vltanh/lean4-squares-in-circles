module

public import SquaresInCircles.Eight.Owners.Canonical.NegativeCycle
public import SquaresInCircles.Eight.Owners.Nonpositive.BelowRotated
public import SquaresInCircles.Eight.Owners.Ordered.HardEndpoint

/-!
# Eight squares: the full nonpositive hard terminal on its original source

Both outer errors may be nonzero and E may
start anywhere in the original frame interval, with either weak mixed
owner.  The actual E ordering and small-side transports reduce the finite
terminal alternatives to the aligned or the large-B canonical theorem.

Every loss is compared with the original anchor circle.  The proof first
recovers the original E frame and HG alignment, and then applies the
canonical negative theorem to the untouched source.  No equality of a
transported intermediate with its ancestor is assumed.
-/

section
/-!
## Exhaustive original mixed-owner E ordering for nonpositive outer composites

The original E may begin at any frame in
the actual spread interval and may retain either allowed mixed owner.
Above H is excluded.  Each below-D owner has its concrete original-circle
descent with strict E loss.  An E already between D and H retains its
literal point and frame, and its actual radial alternative supplies
both primary axes there.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

theorem HardInput.order_nonpositive_E {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta E<I.cycle.theta D → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  have hEHorder := I.nonpositive_E_le_H hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
  by_cases hbelow : I.cycle.theta E<I.cycle.theta D
  · have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    have hendpoint : ∃J : HardInput q,
        (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
        J.cycle.theta E=I.cycle.theta D ∧
        AnchorNonincrease I.cycle J.cycle ∧ StrictAnchorLoss I.cycle J.cycle ∧
        (J.cycle.point E).circle<(I.cycle.point E).circle ∧
        J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
      rcases hj with hj | hj
      · have hDE : I.cycle.Feasible D 2 := by simpa [hj] using I.witnesses.feasible D
        exact I.reduce_nonpositive_below_rotated hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
          hbelow hDE
      · have hDE : I.cycle.Feasible D 3 := by simpa [hj] using I.witnesses.feasible D
        exact I.reduce_nonpositive_below_primary hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
          hbelow hDE
    obtain ⟨J,hfixed,hframe,hnon,hstrict,hcircle,hDE,hEH⟩ := hendpoint
    refine ⟨J,hfixed,?_,hnon,fun _ => hstrict,hDE,hEH⟩
    rw [hframe]
    exact ⟨le_rfl,sub_nonneg.mp hb.span_nonneg⟩
  · have hDEorder : I.cycle.theta D≤I.cycle.theta E := le_of_not_gt hbelow
    have hDE := I.nonpositive_DE_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hDEorder
    have hEH := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
    exact ⟨I,fun _ _ => ⟨rfl,rfl⟩,⟨hDEorder,hEHorder⟩,
      anchorNonincrease_refl I.cycle,fun h => (hbelow h).elim,hDE,hEH⟩

end SquaresInCircles.Eight.SignedCycle
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate GeometricModel Stationary

private theorem feasible_congr {C C' : SignedCycle} {i k : Vertex} (hk : next i=k) {j : Fin 4}
    (h1 : C'.point i=C.point i) (h2 : C'.theta i=C.theta i)
    (h3 : C'.point k=C.point k) (h4 : C'.theta k=C.theta k) :
    C'.Feasible i j ↔ C.Feasible i j := by
  subst hk
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

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
    exact (feasible_congr (k := E) (by decide) hD.1 hD.2 hE.1 hE.2).2 hDE
  have hJEH : J.cycle.Feasible E 1 := by
    exact (feasible_congr (k := H) (by decide) hE.1 hE.2 hH.1 hH.2).2 hEH
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
        exact (feasible_congr (k := D) (by decide) hKT.1 hKT.2 hKD.1 hKD.2).2 hJTD
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
    · exact (feasible_congr (k := G) (by decide) hH.1 hH.2 hG.1 hG.2).2 hHG
    · exact (feasible_congr (k := D) (by decide) hT.1 hT.2 hD.1 hD.2).2 hTD
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
      exact (feasible_congr (k := E) (by decide) hD.1 hD.2 hE.1 hE.2).2 hDE
    have hKEH : K.cycle.Feasible E 1 := by
      exact (feasible_congr (k := H) (by decide) hE.1 hE.2 hH.1 hH.2).2 hEH
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

end SquaresInCircles.Eight.SignedCycle
end
end
end
