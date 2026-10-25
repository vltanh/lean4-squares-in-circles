module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeCycle
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoCycle
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeCycle
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.NegativeThreeCycle
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeCycle

/-!
# Eight squares: every outer quarter edge of the second wrong word

The six continuous representative arguments, each stated for the original owners, are joined
here, including reflected roles, without changing a coordinate, frame, radius or separating axis
(`classification`, `actual`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.OuterQuarter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

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
  revert hq ha
  fin_cases i <;> cases σ <;> cases τ <;>
    norm_num [WordProblems.wrongWord,WordProblems.allowed,next,Families]

/-- One statement for all outer/outer quarter states and original owners. -/
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

end SquaresInCircles.Eight.SecondWord.OuterQuarter
