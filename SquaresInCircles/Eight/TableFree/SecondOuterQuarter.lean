module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoCycle
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCycle
public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeCycle
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeCycle
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveNegativeThreeCycle
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeCycle

/-!
# Every outer quarter edge of the second wrong word

Uncompiled transcription of the finite role dispatch in
`HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md`.
All six continuous representative arguments have their original-owner
wrappers. This module joins exactly those wrappers, including reflected
roles, without changing a coordinate, frame, radius, or separating axis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.OuterQuarter
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

def Families (i : Vertex) (σ τ : Bool) : Prop :=
  ((i=2 ∨ i=6) ∧ σ=false ∧ τ=true) ∨
  ((i=2 ∧ σ=false ∧ τ=false) ∨ (i=6 ∧ σ=true ∧ τ=true)) ∨
  ((i=3 ∧ σ=false ∧ τ=false) ∨ (i=5 ∧ σ=true ∧ τ=true)) ∨
  ((i=3 ∧ σ=true ∧ τ=true) ∨ (i=5 ∧ σ=false ∧ τ=false)) ∨
  ((i=3 ∨ i=5) ∧ σ=false ∧ τ=true) ∨
  ((i=3 ∧ σ=true ∧ τ=false) ∨ (i=5 ∧ σ=true ∧ τ=false))

theorem classification (i : Vertex) (σ τ : Bool)
    (hq : WordProblems.wrongWord .second i=1)
    (ha : WordProblems.allowed .second i σ τ) : Families i σ τ := by
  fin_cases i <;> cases σ <;> cases τ <;>
    norm_num [WordProblems.wrongWord,WordProblems.allowed,next,Families] at hq ha ⊢

/-- A single interface for all outer/outer quarter states and original owners. -/
theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hq : WordProblems.wrongWord .second i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have ha := actual_allowed C F hgap .second hw i
  rcases classification i (positiveOf C i) (positiveOf C (next i)) hq ha with
    ⟨hi,hσ,hτ⟩ | h | h | h | ⟨hi,hσ,hτ⟩ | h
  · exact OppositeTwo.actual_owner C F hgap hw i hi hs ht hσ hτ j howner
  · exact NegativeTwo.actual_owner C F hgap hw i h hs ht j howner
  · exact NegativeThree.actual_owner C F hgap hw i h hs ht j howner
  · exact PositiveThree.actual_owner C F hgap hw i h hs ht j howner
  · exact OppositeThree.actual_owner C F hgap hw i hi hs ht hσ hτ j howner
  · exact PositiveNegativeThree.actual_owner C F hgap hw i h hs ht j howner

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hq : WordProblems.wrongWord .second i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hq hs ht j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.TableFree.SecondWord.OuterQuarter
