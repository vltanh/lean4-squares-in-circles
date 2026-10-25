module

public import SquaresInCircles.Eight.TableFree.QuarterDoubleExclusion
public import SquaresInCircles.Eight.TableFree.SecondWordExclusion
public import SquaresInCircles.Eight.TableFree.ShortWordExclusion

/-!
# The surviving quarter word from the complete continuous exclusions

Uncompiled assembly of the common-quarter, short-word and second-word
successors. The finite seven-class theorem is applied only to the actual
physical lift. Every continuous exclusion is supplied here, including
both nearest-axis choices and every original weak separating owner.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFreeWordGeometry

theorem quarter_word_candidate (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  rcases three_binary_classes C F hgap with hshort|hsecond|hcandidate
  · exact (TableFree.ShortWord.not_dihedral C F hgap hshort).elim
  · exact (TableFree.SecondWord.not_dihedral C F hgap hsecond).elim
  · exact hcandidate

end SquaresInCircles.Eight.TableFreeWordGeometry
