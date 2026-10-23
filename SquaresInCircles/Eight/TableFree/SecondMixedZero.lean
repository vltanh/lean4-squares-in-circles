module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroSameCycle
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeCycle

/-!
# Every original mixed zero edge of the second wrong word

Uncompiled source draft.  The same-sign and opposite-sign analytic
families cover both radial orders, both closed core pieces, every
permitted literal sign, and each of the original weak physical owners.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

abbrev Mixed := Same.Mixed

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Mixed (C.kind i) (C.kind (next i))) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  by_cases hsign : positiveOf C i=positiveOf C (next i)
  · exact Same.actual_owner C F hgap hw i hi hmixed hsign j howner
  · exact Opposite.actual_owner C F hgap hw i hi hmixed hsign j howner

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Mixed (C.kind i) (C.kind (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hmixed j howner

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero
