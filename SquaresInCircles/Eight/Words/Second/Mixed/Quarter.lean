module

public import SquaresInCircles.Eight.Words.Second.Mixed.FourFamilies
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.TargetTwoCycle
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.OuterCycle
public import SquaresInCircles.Eight.Words.Second.Mixed.Negative.SourceThreeCycle
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeEarly
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.OuterTwoCycle
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeCycle

/-!
# Eight squares: every mixed quarter edge of the second wrong word

The twelve independent representatives and their exact reflected roles
cover every allowed original radial order and sign. The finite dispatch
uses only the literal word and role indices. Each continuous estimate
retains both core pieces, the original circle radius, and every weak
physical separating owner.
-/

section
/-!
## Original-cycle adapters for the four complete mixed quarter families

The finite family predicate records only the original radial order
and signs.  Reflection transports the exact labels and the selected
weak owner.  Every core-side/corner choice and both frame-error signs
remain in the resulting physical-cycle statement.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Four (source target : RadialKind) (σ τ : Bool) : Prop :=
  (source≠.outer ∧ target=.outer ∧ σ=false ∧ τ=false) ∨
  (source=.outer ∧ target≠.outer ∧ σ=true ∧ τ=true) ∨
  (source≠.outer ∧ target=.outer ∧ σ=true ∧ τ=false) ∨
  (source=.outer ∧ target≠.outer ∧ σ=true ∧ τ=false)

def FourRole (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=3 ∧ Four source target σ τ) ∨ (i=5 ∧ Four target source (!τ) (!σ))

theorem original_three {source target : RadialKind} {σ τ : Bool}
    (hfamily : Four source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    (9/10:ℝ)<cost 3 source target σ τ a b A B φ := by
  rcases hfamily with ⟨hk,rfl,rfl,rfl⟩ | ⟨rfl,hk,rfl,rfl⟩ |
    ⟨hk,rfl,rfl,rfl⟩ | ⟨rfl,hk,rfl,rfl⟩
  · have hc : CoreState a b := by simpa [State,hk] using hs
    have ho : OuterState A B := by simpa [State] using ht
    have hm' : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [negative_core_negative_outer hk hc ho hφ j hm']
  · have ho : OuterState a b := by simpa [State] using hs
    have hc : CoreState A B := by simpa [State,hk] using ht
    have hm' : 0≤Eight.forwardMargin j a b A B 1 1 φ := by
      simpa [WordProblems.sign] using hm
    linarith [positive_outer_positive_core hk ho hc hφ j hm']
  · have hc : CoreState a b := by simpa [State,hk] using hs
    have ho : OuterState A B := by simpa [State] using ht
    have hm' : 0≤Eight.forwardMargin j a b A B 1 (-1) φ := by
      simpa [WordProblems.sign] using hm
    exact positive_core_negative_outer hk hc ho hφ j hm'
  · have ho : OuterState a b := by simpa [State] using hs
    have hc : CoreState A B := by simpa [State,hk] using ht
    linarith [positive_outer_negative_core hk ho hc hφ]

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : FourRole i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<cost i source target σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,hfamily⟩ | ⟨rfl,hfamily⟩
  · linarith [original_three hfamily hs ht hφ j hm]
  · have hσ : (WordProblems.sign (!σ):ℝ)= -(WordProblems.sign σ:ℝ) := by
      cases σ <;> norm_num [WordProblems.sign]
    have hτ : (WordProblems.sign (!τ):ℝ)= -(WordProblems.sign τ:ℝ) := by
      cases τ <;> norm_num [WordProblems.sign]
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b
        (WordProblems.sign (!τ)) (WordProblems.sign (!σ)) φ := by
      rw [hσ,hτ,margin_reflection]
      exact hm
    have hh := original_three hfamily ht hs hφ (reflectedOwner j) hrev
    have he := cost_reflection (3:Vertex) target source (!τ) (!σ) A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : FourRole i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : FourRole i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedThree
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Mixed (source target : RadialKind) : Prop :=
  (source=.outer ∧ target≠.outer) ∨ (source≠.outer ∧ target=.outer)

def Families (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  MixedThree.FourRole i source target σ τ ∨
  MixedOuterNegative.Role i source target σ τ ∨
  MixedTwo.NegativeCore.Role i source target σ τ ∨
  MixedTwo.PositiveOuter.Role i source target σ τ ∨
  MixedTwo.PositiveCore.Role i source target σ τ ∨
  MixedThree.PositiveCore.Role i source target σ τ ∨
  MixedTwo.NegativeTarget.Role i source target σ τ ∨
  MixedThree.PositiveSource.Role i source target σ τ ∨
  MixedThree.NegativeSource.Role i source target σ τ

/-- Only the discrete original role, radial kinds and signs are split.
There is no real-coordinate or owner hypothesis in this dispatch. -/
theorem classification (i : Vertex) (source target : RadialKind) (σ τ : Bool)
    (hq : WordProblems.wrongWord .second i=1)
    (ha : WordProblems.allowed .second i σ τ) (hm : Mixed source target) :
    Families i source target σ τ := by
  revert ha
  fin_cases i <;> simp [WordProblems.wrongWord] at hq <;>
    cases source <;> cases target <;> simp [Mixed] at hm <;>
    cases σ <;> cases τ <;>
    simp [WordProblems.allowed,next,Families,MixedThree.FourRole,MixedThree.Four,
      MixedOuterNegative.Role,MixedTwo.NegativeCore.Role,MixedTwo.PositiveOuter.Role,
      MixedTwo.PositiveCore.Role,MixedThree.PositiveCore.Role,MixedTwo.NegativeTarget.Role,
      MixedThree.PositiveSource.Role,MixedThree.NegativeSource.Role]

theorem original {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hq : WordProblems.wrongWord .second i=1)
    (ha : WordProblems.allowed .second i σ τ) (hmixed : Mixed source target)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<cost i source target σ τ a b A B φ := by
  rcases classification i source target σ τ hq ha hmixed with
    h | h | h | h | h | h | h | h | h
  · exact MixedThree.original_role h hs ht hφ j hm
  · exact MixedOuterNegative.original_role h hs ht hφ j hm
  · exact MixedTwo.NegativeCore.original_role h hs ht hφ j hm
  · exact MixedTwo.PositiveOuter.original_role h hs ht hφ j hm
  · exact MixedTwo.PositiveCore.original_role h hs ht hφ j hm
  · exact MixedThree.PositiveCore.original_role h hs ht hφ j hm
  · exact MixedTwo.NegativeTarget.original_role h hs ht hφ j hm
  · exact MixedThree.PositiveSource.original_role h hs ht hφ j hm
  · exact MixedThree.NegativeSource.original_role h hs ht hφ j hm

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hq : WordProblems.wrongWord .second i=1)
    (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by rw [hw]; exact hq
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original hq (actual_allowed C F hgap .second hw i) hmixed
    (actual_state C i) (actual_state C (next i)) hφ j (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hq : WordProblems.wrongWord .second i=1)
    (hmixed : Mixed (C.kind i) (C.kind (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hq hmixed j howner

end SquaresInCircles.Eight.SecondWord.MixedQuarter
end
end
end
