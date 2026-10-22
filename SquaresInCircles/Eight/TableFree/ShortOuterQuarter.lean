module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneSamePrimary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFive
public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveComplement

/-!
# Every original outer quarter-one owner of the short word

Uncompiled transcription of Section 5 of
`HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md`. The finite disjunction is
the displayed 48-owner cover, with zero-based original axes. Each entry
calls its complete continuous proof on the unchanged physical pair.
No selected owner or angle neighborhood is added as a hypothesis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.ShortWord.OuterQuarter
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry WordProblems ShortOuterOne

theorem owner_cover (i : Vertex) (σ τ : Bool) (j : Fin 4)
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ) :
    (σ=τ ∧ Unit.OriginalOwner i σ j) ∨
    (σ=τ ∧ Same.Secondary.OriginalOwner i σ j) ∨
    (σ=τ ∧ Same.Primary.OriginalOwner i σ j) ∨
    (σ=false ∧ τ=true ∧ OppositeSecondary.OriginalOwner i j) ∨
    (σ=false ∧ τ=true ∧ Opposite.Primary.OriginalOwner i j) ∨
    (i=4 ∧ σ=true ∧ τ=true) ∨
    EdgeFive.Complement i σ τ ∨
    (i=5 ∧ σ=false ∧ τ=true) := by
  fin_cases i <;> cases σ <;> cases τ <;> fin_cases j <;>
    norm_num [wrongWord,allowed,next,Unit.OriginalOwner,Same.Secondary.OriginalOwner,
      Same.Primary.OriginalOwner,OppositeSecondary.OriginalOwner,Opposite.Primary.OriginalOwner,
      EdgeFive.Complement] at *

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short)
    (i : Vertex) (hq : wrongWord .short i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (wrongGamma .short i:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  have hi : F.word hgap pi_lt_22_over_7 i=1 := by rw [hw]; exact hq
  have hc := owner_cover i (positiveOf C i) (positiveOf C (next i)) j hq
    (actual_allowed C F hgap .short hw i)
  rcases hc with ⟨hsg,hrole⟩|⟨hsg,hrole⟩|⟨hsg,hrole⟩|
    ⟨hσ,hτ,hrole⟩|⟨hσ,hτ,hrole⟩|⟨rfl,hσ,hτ⟩|hrole|⟨hrole,hσ,hτ⟩
  · exact Unit.actual_owner C F hgap hw i hi hs ht hsg j hrole howner
  · exact Same.Secondary.actual_owner C F hgap hw i hi hs ht hsg j hrole howner
  · exact Same.Primary.actual_owner C F hgap hw i hi hs ht hsg j hrole howner
  · exact OppositeSecondary.actual_owner C F hgap hw i hi hs ht hσ hτ j hrole howner
  · exact Opposite.Primary.actual_owner C F hgap hw i hi hs ht hσ hτ j hrole howner
  · exact RoleFour.actual_owner C F hgap hw hs ht hσ hτ j howner
  · exact EdgeFive.actual_owner C F hgap hw i hi hs ht hrole j howner
  · exact OppositeFive.actual_owner C F hgap hw i hi hs ht hrole hσ hτ j howner

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short)
    (i : Vertex) (hq : wrongWord .short i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    (wrongGamma .short i:ℝ)<phaseValue F hgap i+wrongMarker C .short i-wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hq hs ht j howner

end SquaresInCircles.Eight.TableFree.ShortWord.OuterQuarter
