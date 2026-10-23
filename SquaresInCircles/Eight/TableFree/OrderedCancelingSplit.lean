module

public import SquaresInCircles.Eight.TableFree.OrderedCancelingCycle
public import SquaresInCircles.Eight.TableFree.HardSplitCycle

/-!
# The concrete canceling outer reduction followed by the hard split

Uncompiled draft.  The same-q outer construction is immediately fed to
the actual hard-cap split.  Strict losses remain relative to the original
separate anchor circles, including when a second reduction follows them.
H, D and E, their frames, and both original mixed-axis slacks are retained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate
namespace SignedCycle

/-- Choose the improved split exactly when its source is interior.  This
single output records nonincrease in both cases and retains the strict
source loss rather than merely the common containing radius. -/
theorem HardInput.split_with_source_loss {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hHG : I.cycle.theta G=I.cycle.theta H)
    (hAB : I.cycle.theta B=I.cycle.theta A)
    (hTD : I.cycle.theta T=I.cycle.theta D)
    (hleft : I.cycle.theta A≤I.cycle.theta G)
    (hright : I.cycle.theta T≤I.cycle.theta A) :
    ∃ J : HardInput q,
      (J.cycle.theta A=J.cycle.theta G ∨ J.cycle.theta A=J.cycle.theta T) ∧
      J.cycle.theta A=J.cycle.theta B ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta A<I.cycle.theta G ∧ I.cycle.theta T<I.cycle.theta A →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠A → i≠B → J.cycle.point i=I.cycle.point i ∧
        J.cycle.theta i=I.cycle.theta i) := by
  by_cases hi : I.cycle.theta A<I.cycle.theta G ∧ I.cycle.theta T<I.cycle.theta A
  · obtain ⟨J,hend,hAB',hnon,hstrict,hA,hB,hfixed⟩ :=
      I.exists_split_strict_loss hq hHG hAB hTD hi.1 hi.2
    exact ⟨J,hend,hAB',hnon,(fun _ => hstrict),hfixed⟩
  · obtain ⟨J,hend,hAB',hcircle,hfixed⟩ :=
      I.exists_split_aligned hq hHG hAB hTD hleft hright
    refine ⟨J,hend,hAB',?_,(fun h => (hi h).elim),hfixed⟩
    intro i _
    exact (hcircle i).le

/-- A full actual split endpoint in the ordered canceling sector.  Any
nonzero original outer error or interior original common frame is charged
to a strict loss on an original anchor circle. -/
theorem HardInput.ordered_canceling_split {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hsum : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 2) (hTD : I.cycle.Feasible T 0) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.theta A=J.cycle.theta H ∨ J.cycle.theta A=J.cycle.theta D) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      ((I.cycle.theta G≠I.cycle.theta H ∨ I.cycle.theta T≠I.cycle.theta D ∨
        (I.cycle.theta A<I.cycle.theta H ∧ I.cycle.theta D<I.cycle.theta A)) →
        StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i∈({H,D,E} : Finset Vertex) →
        J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i=D ∨ i=E → ∀j,J.cycle.slack i j=I.cycle.slack i j) := by
  obtain ⟨K,hKG,hKT,hKAB,hKsum,hKynG,hKynT,hKA,hKB,hnonK,hstrictK,hframeK,hpointK⟩ :=
    I.align_ordered_canceling_outer hqL hq hAB hsum hAH hAG hDB hTB hHG hTD
  have hKAframe := hframeK A (by decide) (by decide)
  have hKHframe := hframeK H (by decide) (by decide)
  have hKDframe := hframeK D (by decide) (by decide)
  have hleft : K.cycle.theta A≤K.cycle.theta G := by rw [hKG,hKAframe,hKHframe]; exact hAH
  have hright : K.cycle.theta T≤K.cycle.theta A := by
    rw [hKT,hKDframe,hKAframe,hAB]
    exact hDB
  obtain ⟨J,hend,hJAB,hnonJ,hstrictJ,hfixedJ⟩ :=
    K.split_with_source_loss hq hKG hKAB.symm hKT hleft hright
  have hJG := (hfixedJ G (by decide) (by decide)).2
  have hJH := (hfixedJ H (by decide) (by decide)).2
  have hJT := (hfixedJ T (by decide) (by decide)).2
  have hJD := (hfixedJ D (by decide) (by decide)).2
  have hGH : J.cycle.theta G=J.cycle.theta H := by rw [hJG,hJH,hKG]
  have hTD' : J.cycle.theta T=J.cycle.theta D := by rw [hJT,hJD,hKT]
  have hfixed (i : Vertex) (hi : i∈({H,D,E} : Finset Vertex)) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i := by
    have hiA : i≠A := by fin_cases i <;> simp [H,D,E,A] at hi ⊢
    have hiB : i≠B := by fin_cases i <;> simp [H,D,E,B] at hi ⊢
    have hiG : i≠G := by fin_cases i <;> simp [H,D,E,G] at hi ⊢
    have hiT : i≠T := by fin_cases i <;> simp [H,D,E,T] at hi ⊢
    exact ⟨(hfixedJ i hiA hiB).1.trans (hpointK i hi),
      (hfixedJ i hiA hiB).2.trans (hframeK i hiG hiT)⟩
  refine ⟨J,hGH,hTD',hJAB,?_,?_,?_,hfixed,?_⟩
  · simpa [hGH,hTD'] using hend
  · intro i hi
    exact (hnonJ i hi).trans (hnonK i hi)
  · rintro (hg | ht | hi)
    · obtain ⟨i,hia,hiloss⟩ := hstrictK (Or.inl hg)
      exact ⟨i,hia,(hnonJ i hia).trans_lt hiloss⟩
    · obtain ⟨i,hia,hiloss⟩ := hstrictK (Or.inr ht)
      exact ⟨i,hia,(hnonJ i hia).trans_lt hiloss⟩
    · have hKi : K.cycle.theta A<K.cycle.theta G ∧ K.cycle.theta T<K.cycle.theta A := by
        rw [hKG,hKT,hKAframe,hKHframe,hKDframe]
        exact hi
      obtain ⟨i,hia,hiloss⟩ := hstrictJ hKi
      exact ⟨i,hia,hiloss.trans_le (hnonK i hia)⟩
  · intro i hi j
    have hH := hfixed H (by simp)
    have hD := hfixed D (by simp)
    have hE := hfixed E (by simp)
    rcases hi with rfl | rfl <;>
      simp [slack,edge,delta,next,D,E,H,hH.1,hH.2,hD.1,hD.2,hE.1,hE.2]

end SignedCycle
end SquaresInCircles.Eight.TableFree
