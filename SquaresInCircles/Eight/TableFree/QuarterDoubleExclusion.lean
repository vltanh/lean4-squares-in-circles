module

public import SquaresInCircles.Eight.TableFree.CommonZero
public import SquaresInCircles.Eight.TableFree.CommonOne

/-!
# The four double-increment words are impossible without tables

The complete continuous estimates for increments zero, one and two apply
to the actual source cycle and its original weak owner. Each original
vertex label cancels once. The remaining argument is the exact integer
classification already proved for quarter lifts, followed by a rational
comparison with `2*pi`.

Physical dihedral normalization is used only to express the four excluded
representatives; it preserves every original square and separator.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFreeWordGeometry

open Arithmetic WordProblems

/-- The full common cost inequality, with no radial, sign or owner case
left as an external assumption. -/
theorem common_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ)<
      phaseValue F hgap i+commonMarker C i-commonMarker C (next i) := by
  generalize hk : F.word hgap pi_lt_22_over_7 i=k
  fin_cases k
  · simpa [commonGamma] using CommonQuarter.actual_zero C F hgap i hk j hj
  · simpa [commonGamma] using CommonQuarter.actual_one C F hgap i hk j hj
  · simpa [commonGamma] using CommonQuarter.actual_jump_two C F hgap i hk j hj

theorem commonGamma_numerator (k : Fin 3) :
    (commonGamma k:ℝ)=(doubleWordCostNumerator k:ℝ)/10000 := by
  fin_cases k <;> norm_num [commonGamma,doubleWordCostNumerator]

/-- Every actual cycle is binary: the four zero, two one and one double
costs would exceed its exact full-turn budget. -/
theorem no_double (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    ¬∃i,F.word hgap pi_lt_22_over_7 i=2 := by
  apply no_double_word_of_cost_bound (F.word hgap pi_lt_22_over_7)
    (F.word_admissible hgap pi_lt_22_over_7)
    (fun i => phaseValue F hgap i+commonMarker C i-commonMarker C (next i))
  · intro i
    obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
    have hh := common_pair C F hgap i j (by simpa [← hj] using C.feasible i)
    rw [commonGamma_numerator] at hh
    exact hh.le
  · exact (marker_budget C F hgap (commonMarker C)).le
  · exact pi_lt_22_over_7

/-- All four representatives containing a double are excluded under every
actual cyclic relabeling and reflected orientation. -/
theorem four_double_exclusions (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (j : Fin 4) :
    ¬(F.word hgap pi_lt_22_over_7).DihedralEquivalent
      (quarterRepresentatives ⟨j.val,by omega⟩) := by
  intro heq
  obtain ⟨G,hword⟩ := normalize_word C F hgap
    (quarterRepresentatives ⟨j.val,by omega⟩) heq
  let D := G.boundary C
  let H := F.act G
  have hg : ∀i,19/25<angleGap D.beta i := boundary_gap_lower D le_rfl
  have he : H.word hg pi_lt_22_over_7=quarterRepresentatives ⟨j.val,by omega⟩ := hword
  apply no_double D H hg
  fin_cases j
  · exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · exact ⟨4,by rw [he]; norm_num [quarterRepresentatives]⟩
  · exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩

/-- The actual physical word is now one of exactly the three binary
classes. The two remaining wrong binary classes are stated explicitly. -/
theorem three_binary_classes (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent (wrongWord .short) ∨
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent (wrongWord .second) ∨
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  obtain ⟨j,hj⟩ := quarter_word_complete_classification _
    (F.word_admissible hgap pi_lt_22_over_7)
  have hs : wrongWord .short=quarterRepresentatives 4 := by
    funext i
    fin_cases i <;> rfl
  have hsec : wrongWord .second=quarterRepresentatives 5 := by
    funext i
    fin_cases i <;> rfl
  fin_cases j
  · exact (four_double_exclusions C F hgap 0 hj).elim
  · exact (four_double_exclusions C F hgap 1 hj).elim
  · exact (four_double_exclusions C F hgap 2 hj).elim
  · exact (four_double_exclusions C F hgap 3 hj).elim
  · left
    rw [hs]
    exact hj
  · right
    left
    rw [hsec]
    exact hj
  · right
    right
    exact hj

end SquaresInCircles.Eight.TableFreeWordGeometry
