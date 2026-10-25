module

public import SquaresInCircles.Eight.Words.FirstNegativeOutsideEntry
public import SquaresInCircles.Eight.Words.Second.WordExclusion
public import SquaresInCircles.Eight.Words.Short.WordExclusion

/-!
# Eight squares: the surviving quarter word from the complete continuous exclusions

The finite seven-class theorem is applied only to the actual
physical lift. Every continuous exclusion is supplied here, including
both nearest-axis choices and every original weak separating owner.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.QuarterWordGeometry

theorem quarter_word_candidate (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  rcases three_binary_classes C F hgap with hshort|hsecond|hcandidate
  · exact (Eight.ShortWord.not_dihedral C F hgap hshort).elim
  · exact (Eight.SecondWord.not_dihedral C F hgap hsecond).elim
  · exact hcandidate

end SquaresInCircles.Eight.QuarterWordGeometry
