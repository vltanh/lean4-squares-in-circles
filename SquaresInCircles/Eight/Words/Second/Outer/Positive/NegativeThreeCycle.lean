module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.NegativeThree
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: the original positive-to-negative quarter pair in a physical cycle

Reflected reversal preserves this sign pair and exchanges roles three and five
(`original_reflected`, `original_role`). The original selected weak owner and both original
circle coordinates are kept in the conclusion on the cycle (`actual`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveNegativeThree

open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<SecondWord.cost 3 .outer .outer true false a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (4493/5000:ℝ)<SecondWord.cost 5 .outer .outer true false a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b 1 (-1) φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(-1:ℝ)) (-(1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (3:Vertex) .outer .outer true false A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (σ τ : Bool)
    (hrole : (i=3 ∧ σ=true ∧ τ=false) ∨ (i=5 ∧ σ=true ∧ τ=false))
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<SecondWord.cost i .outer .outer σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_cost hs ht hφ j hmargin]
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_reflected hs ht hφ j hmargin]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false) ∨
      (i=5 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original_role i (positiveOf C i) (positiveOf C (next i)) hrole
    hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false) ∨
      (i=5 ∧ positiveOf C i=true ∧ positiveOf C (next i)=false))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole hs ht j howner

end SquaresInCircles.Eight.SecondWord.PositiveNegativeThree
