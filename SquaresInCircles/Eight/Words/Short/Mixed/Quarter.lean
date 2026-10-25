module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOwners
public import SquaresInCircles.Eight.Words.Short.WordZero

/-!
# Eight squares: complete original-cycle mixed quarter-one component of 0010111

The selected physical separator supplies one of the
four original forward owners. Its literal state coordinates and actual
signed markers enter the now-complete mixed-quarter owner theorem.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry WordProblems

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short)
    (i : Vertex) (hq : wrongWord .short i=1) (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by rw [hw]; exact hq
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  exact original hq (actual_allowed C F hgap .short hw i) hmixed
    (actual_state C i) (actual_state C (next i)) hφ j (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short)
    (i : Vertex) (hq : wrongWord .short i=1) (hmixed : Mixed (C.kind i) (C.kind (next i))) :
    (wrongGamma .short i:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact (Zero.threshold_le i).trans_lt (actual_owner C F hgap hw i hq hmixed j howner)

end SquaresInCircles.Eight.ShortWord.MixedQuarter
