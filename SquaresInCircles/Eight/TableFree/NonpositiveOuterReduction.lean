module

public import SquaresInCircles.Eight.TableFree.NonpositiveMixedE

/-!
# Removing every small-tangent negative outer error in the actual cycle

Uncompiled draft.  The two local transports are composed at their
literal output cycles.  Both middle tangents and their common frame are
retained; a removed nonzero error is charged to its original middle
circle.  H,D,E remain the original points and frames.  The exact AB
normalization then leaves either two aligned sides or one large-tangent
negative side, with no loss of the original strictness predicate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

private theorem HardInput.reduce_small_HG {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H) (hHG : I.cycle.Feasible H 0) :
    ∃J : HardInput q,
      ((I.cycle.point A).y≤1/2 → J.cycle.theta G=J.cycle.theta H) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta G<I.cycle.theta H ∧ (I.cycle.point A).y≤1/2) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) ∧
      J.cycle.theta A≤J.cycle.theta G ∧ J.cycle.theta G≤J.cycle.theta H ∧
      J.cycle.Feasible H 0 := by
  by_cases hsmall : (I.cycle.point A).y≤1/2
  · obtain ⟨J,hGH',hAB',hy,hnon,hstrict,hθ,hpoint⟩ :=
      I.align_nonpositive_HG0_small hqL hq hAB hAG hGH hsmall hHG
    refine ⟨J,fun _ => hGH',hAB',hy,hnon,fun h => hstrict h.1,hθ,hpoint,?_,
      hGH'.le,J.aligned_HG_zero hGH'⟩
    rw [hGH',hθ A (by decide),hθ H (by decide)]
    exact hAG.trans hGH
  · refine ⟨I,?_,hAB,rfl,anchorNonincrease_refl _,?_,?_,?_,hAG,hGH,hHG⟩
    · intro hs
      exact False.elim (hsmall hs)
    · intro hs
      exact False.elim (hsmall hs.2)
    · exact fun _ _ => rfl
    · exact fun _ _ _ => rfl

private theorem HardInput.reduce_small_TD {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B) (hTD : I.cycle.Feasible T 2) :
    ∃J : HardInput q,
      (-(I.cycle.point B).y≤1/2 → J.cycle.theta T=J.cycle.theta D) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta D<I.cycle.theta T ∧ -(I.cycle.point B).y≤1/2) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) ∧
      J.cycle.theta D≤J.cycle.theta T ∧ J.cycle.theta T≤J.cycle.theta B ∧
      J.cycle.Feasible T 2 := by
  by_cases hsmall : -(I.cycle.point B).y≤1/2
  · obtain ⟨J,hTD',hAB',hy,hnon,hstrict,hθ,hpoint⟩ :=
      I.align_nonpositive_TD2_small hqL hq hAB hDT hTB hsmall hTD
    refine ⟨J,fun _ => hTD',hAB',hy,hnon,fun h => hstrict h.1,hθ,hpoint,
      hTD'.symm.le,?_,J.aligned_TD_two hTD'⟩
    rw [hTD',hθ D (by decide),hθ B (by decide)]
    exact hDT.trans hTB
  · refine ⟨I,?_,hAB,rfl,anchorNonincrease_refl _,?_,?_,?_,hDT,hTB,hTD⟩
    · intro hs
      exact False.elim (hsmall hs)
    · intro hs
      exact False.elim (hsmall hs.2)
    · exact fun _ _ => rfl
    · exact fun _ _ _ => rfl

private theorem r60_feasible_congr {C C' : SignedCycle} {i : Vertex}
    (h1 : C'.point i=C.point i) (h2 : C'.point (next i)=C.point (next i))
    (h3 : C'.theta i=C.theta i) (h4 : C'.theta (next i)=C.theta (next i)) (j : Fin 4) :
    C'.Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

/-- Exhaustive reduction after actual AB normalization.  Every remaining
nonzero negative error belongs to a side whose original middle tangent
is strictly greater than one half.  The other side is literally aligned.
At the threshold both sides align. -/
theorem HardInput.reduce_nonpositive_small_sides {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    ∃J : HardInput q,
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y-(J.cycle.point B).y=1 ∧
      J.cycle.theta A≤J.cycle.theta G ∧ J.cycle.theta G≤J.cycle.theta H ∧
      J.cycle.theta D≤J.cycle.theta T ∧ J.cycle.theta T≤J.cycle.theta B ∧
      J.cycle.Feasible H 0 ∧ J.cycle.Feasible T 2 ∧
      ((J.cycle.theta G=J.cycle.theta H ∧ J.cycle.theta T=J.cycle.theta D) ∨
        (1/2<(J.cycle.point A).y ∧ J.cycle.theta T=J.cycle.theta D) ∨
        (1/2< -(J.cycle.point B).y ∧ J.cycle.theta G=J.cycle.theta H)) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.theta G<I.cycle.theta H ∧ (I.cycle.point A).y≤1/2) ∨
        (I.cycle.theta D<I.cycle.theta T ∧ -(I.cycle.point B).y≤1/2)) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      (∀i,i≠G → i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀i,i∈({H,D,E} : Finset Vertex) →
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) := by
  obtain ⟨K,hKsmall,hKAB,hKAy,hIK,hIKstrict,hKθ,hKpoint,hKAG,hKGH,hKHG⟩ :=
    I.reduce_small_HG hqL hq hAB hAG hGH hHG
  have hKB : K.cycle.point B=I.cycle.point B := hKpoint B (by decide) (by decide)
  have hKT : K.cycle.point T=I.cycle.point T := hKpoint T (by decide) (by decide)
  have hKD : K.cycle.point D=I.cycle.point D := hKpoint D (by decide) (by decide)
  have hKDT : K.cycle.theta D≤K.cycle.theta T := by
    rw [hKθ D (by decide),hKθ T (by decide)]
    exact hDT
  have hKTB : K.cycle.theta T≤K.cycle.theta B := by
    rw [hKθ T (by decide),hKθ B (by decide)]
    exact hTB
  have hKTD : K.cycle.Feasible T 2 := by
    have hn : next T=D := by decide
    exact (r60_feasible_congr hKT (by rw [hn]; exact hKD) (hKθ T (by decide))
      (by rw [hn]; exact hKθ D (by decide)) 2).2 hTD
  obtain ⟨J,hJsmall,hJAB,hJBy,hKJ,hKJstrict,hJθ,hJpoint,hJDT,hJTB,hJTD⟩ :=
    K.reduce_small_TD hqL hq hKAB hKDT hKTB hKTD
  have hJA : J.cycle.point A=K.cycle.point A := hJpoint A (by decide) (by decide)
  have hJG : J.cycle.point G=K.cycle.point G := hJpoint G (by decide) (by decide)
  have hJH : J.cycle.point H=K.cycle.point H := hJpoint H (by decide) (by decide)
  have hJAy : (J.cycle.point A).y=(I.cycle.point A).y := by rw [hJA,hKAy]
  have hJBy' : (J.cycle.point B).y=(I.cycle.point B).y := by rw [hJBy,hKB]
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    rw [hJAy,hJBy']
    exact hnorm
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by
    rw [hJθ A (by decide),hJθ G (by decide)]
    exact hKAG
  have hJGH : J.cycle.theta G≤J.cycle.theta H := by
    rw [hJθ G (by decide),hJθ H (by decide)]
    exact hKGH
  have hJHG : J.cycle.Feasible H 0 := by
    have hn : next H=G := by decide
    exact (r60_feasible_congr hJH (by rw [hn]; exact hJG) (hJθ H (by decide))
      (by rw [hn]; exact hJθ G (by decide)) 0).2 hKHG
  have hsmallH : (I.cycle.point A).y≤1/2 → J.cycle.theta G=J.cycle.theta H := by
    intro hs
    rw [hJθ G (by decide),hJθ H (by decide)]
    exact hKsmall hs
  have hsmallD : -(I.cycle.point B).y≤1/2 → J.cycle.theta T=J.cycle.theta D := by
    intro hs
    apply hJsmall
    rw [hKB]
    exact hs
  have hcases :
      (J.cycle.theta G=J.cycle.theta H ∧ J.cycle.theta T=J.cycle.theta D) ∨
        (1/2<(J.cycle.point A).y ∧ J.cycle.theta T=J.cycle.theta D) ∨
        (1/2< -(J.cycle.point B).y ∧ J.cycle.theta G=J.cycle.theta H) := by
    by_cases hsA : (I.cycle.point A).y≤1/2
    · by_cases hsB : -(I.cycle.point B).y≤1/2
      · exact Or.inl ⟨hsmallH hsA,hsmallD hsB⟩
      · exact Or.inr (Or.inr ⟨by rw [hJBy']; linarith,hsmallH hsA⟩)
    · exact Or.inr (Or.inl ⟨by rw [hJAy]; linarith,hsmallD (by linarith)⟩)
  refine ⟨J,hJAB,hJnorm,hJAG,hJGH,hJDT,hJTB,hJHG,hJTD,hcases,hIK.trans hKJ,
    ?_,hJAy,hJBy',?_,?_⟩
  · intro hs
    rcases hs with hH | hD
    · exact (hIKstrict hH).then_nonincrease hKJ
    · apply hIK.then_strict
      apply hKJstrict
      refine ⟨?_,?_⟩
      · rw [hKθ D (by decide),hKθ T (by decide)]
        exact hD.1
      · rw [hKB]
        exact hD.2
  · intro i hiG hiT
    rw [hJθ i hiT,hKθ i hiG]
  · intro i hi
    have hiG : i≠G := (by decide : ∀ j∈({H,D,E} : Finset Vertex),j≠G) i hi
    have hiA : i≠A := (by decide : ∀ j∈({H,D,E} : Finset Vertex),j≠A) i hi
    have hiT : i≠T := (by decide : ∀ j∈({H,D,E} : Finset Vertex),j≠T) i hi
    have hiB : i≠B := (by decide : ∀ j∈({H,D,E} : Finset Vertex),j≠B) i hi
    exact ⟨(hJpoint i hiT hiB).trans (hKpoint i hiG hiA),
      (hJθ i hiT).trans (hKθ i hiG)⟩

end SignedCycle
end SquaresInCircles.Eight.TableFree
