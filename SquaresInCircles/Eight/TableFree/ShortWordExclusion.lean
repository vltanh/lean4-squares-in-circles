module

public import SquaresInCircles.Eight.TableFree.ShortOuterQuarter
public import SquaresInCircles.Eight.TableFree.ShortMixedQuarter

/-!
# Complete short wrong-word exclusion on the original boundary cycle

Uncompiled transcription of `HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md`.
Every radial state, allowed literal sign and original weak separator is
included. The single vertex representation is unchanged between adjacent
edges; its marker therefore cancels in the exact cyclic sum. The zero
primary exclusions are already proved on the same physical cycle.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ShortWord
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry WordProblems

theorem binary_edge (i : Vertex) : wrongWord .short i=0∨wrongWord .short i=1 := by
  fin_cases i <;> norm_num [wrongWord]

theorem actual_edge (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex) :
    (wrongGamma .short i:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  rcases binary_edge i with hz|hq
  · exact Zero.actual C F hgap hw i (by rw [hw]; exact hz)
  · by_cases hs : C.kind i=.outer
    · by_cases ht : C.kind (next i)=.outer
      · exact OuterQuarter.actual C F hgap hw i hq hs ht
      · exact MixedQuarter.actual C F hgap hw i hq (Or.inl ⟨hs,ht⟩)
    · by_cases ht : C.kind (next i)=.outer
      · exact MixedQuarter.actual C F hgap hw i hq (Or.inr ⟨hs,ht⟩)
      · exact WrongWordCore.actual_core_pair C F hgap .short hw i hs ht

theorem threshold_total : (∑i : Vertex,(wrongGamma .short i:ℝ))=(31417/5000:ℝ) := by
  norm_num [wrongGamma,Fin.sum_univ_succ]
theorem threshold_total_gt_circle : 2*Real.pi<∑i : Vertex,(wrongGamma .short i:ℝ) := by
  rw [threshold_total]
  linarith [pi_hand_enclosure.2]

theorem excluded (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) : False := by
  have hsum : (∑i : Vertex,(wrongGamma .short i:ℝ))<
      ∑i : Vertex,(phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i)) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (actual_edge C F hgap hw i).le
    · exact ⟨0,Finset.mem_univ _,actual_edge C F hgap hw 0⟩
  rw [marker_budget C F hgap (wrongMarker C .short)] at hsum
  exact (not_lt_of_ge threshold_total_gt_circle.le) hsum

theorem not_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) : F.word hgap pi_lt_22_over_7≠wrongWord .short :=
  excluded C F hgap
theorem not_dihedral (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    ¬(F.word hgap pi_lt_22_over_7).DihedralEquivalent (wrongWord .short) := by
  intro he
  obtain ⟨G,hG⟩ := normalize_word C F hgap (wrongWord .short) he
  exact excluded (G.boundary C) (F.act G) (boundary_gap_lower (G.boundary C) le_rfl) hG

end SquaresInCircles.Eight.TableFree.ShortWord
