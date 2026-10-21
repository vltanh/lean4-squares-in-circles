module

public import SquaresInCircles.Eight.TableFree.SecondCoreCore
public import SquaresInCircles.Eight.TableFree.SecondOuterQuarter
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroCycle
public import SquaresInCircles.Eight.TableFree.SecondMixedQuarter
public import SquaresInCircles.Eight.TableFree.SecondMixedZero

/-!
# The complete second wrong-word exclusion on the original cycle

Uncompiled transcription of Sections 4--5 of
`HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md`.
Every radial assignment, allowed sign, original weak separating owner,
closed core join and reflected role is included. The zero-primary
exclusion is already retained by the original-owner zero-edge wrappers.
The same literal vertex label is used on the two incident edges and
cancels in the final sum. No generated word conclusion is imported.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecondWord
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

lemma binary_edge (i : Vertex) :
    WordProblems.wrongWord .second i=0 ∨ WordProblems.wrongWord .second i=1 := by
  fin_cases i <;> norm_num [WordProblems.wrongWord]

/-- Full radial and quarter dispatch on the unchanged boundary cycle. -/
theorem actual_edge (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  by_cases hs : C.kind i=.outer
  · by_cases ht : C.kind (next i)=.outer
    · rcases binary_edge i with hz | hq
      · exact OuterZero.actual C F hgap hw i (by rw [hw]; exact hz) hs ht
      · exact OuterQuarter.actual C F hgap hw i hq hs ht
    · rcases binary_edge i with hz | hq
      · exact MixedZero.actual C F hgap hw i (by rw [hw]; exact hz)
          (Or.inl ⟨hs,ht⟩)
      · exact MixedQuarter.actual C F hgap hw i hq (Or.inl ⟨hs,ht⟩)
  · by_cases ht : C.kind (next i)=.outer
    · rcases binary_edge i with hz | hq
      · exact MixedZero.actual C F hgap hw i (by rw [hw]; exact hz)
          (Or.inr ⟨hs,ht⟩)
      · exact MixedQuarter.actual C F hgap hw i hq (Or.inr ⟨hs,ht⟩)
    · exact CoreCore.actual C F hgap hw i hs ht

lemma threshold_total : (∑i : Vertex,threshold i)=(125671/20000:ℝ) := by
  simp_rw [threshold_value]
  norm_num

lemma threshold_total_gt_circle : 2*Real.pi<∑i : Vertex,threshold i := by
  rw [threshold_total]
  linarith [Real.pi_lt_d4]

/-- The unrestricted second-word contradiction for a genuine physical lift. -/
theorem excluded (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second) : False := by
  have hsum : (∑i : Vertex,threshold i)<
      ∑i : Vertex,phaseValue F hgap i+wrongMarker C .second i-
        wrongMarker C .second (next i) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (actual_edge C F hgap hw i).le
    · exact ⟨0,Finset.mem_univ _,actual_edge C F hgap hw 0⟩
  rw [marker_budget C F hgap (wrongMarker C .second)] at hsum
  exact (not_lt_of_ge threshold_total_gt_circle.le) hsum

theorem not_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    F.word hgap pi_lt_22_over_7≠WordProblems.wrongWord .second :=
  excluded C F hgap

/-- The same obstruction after physical reflection/reversal and relabeling. -/
theorem not_dihedral (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    ¬(F.word hgap pi_lt_22_over_7).DihedralEquivalent (WordProblems.wrongWord .second) := by
  intro he
  obtain ⟨G,hG⟩ := normalize_word C F hgap (WordProblems.wrongWord .second) he
  exact excluded (G.boundary C) (F.act G) (boundary_gap_lower (G.boundary C) le_rfl) hG

end SquaresInCircles.Eight.TableFree.SecondWord
