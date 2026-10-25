module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeSource
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTarget
public import SquaresInCircles.Eight.TableFree.SecondMixedZeroSameCycle

/-!
# Every original opposite-sign mixed zero edge of the second word

Uncompiled source draft.  J, P and L are the three literal core-to-outer
roles.  Exact reflection gives the reverse radial order.  The independent
original zero-owner theorem accounts for every original axis, including
weak ties, before invoking either secondary estimate.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

lemma zero_roles (i : Vertex) (hi : WordProblems.wrongWord .second i=0) :
    i=0 ∨ i=1 ∨ i=4 := by
  fin_cases i <;> simp [WordProblems.wrongWord] at hi ⊢

theorem original_core_row (r : Row) {kind : RadialKind} (hk : kind≠.outer)
    {a b A B x : ℝ} (hs : State kind a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    (17953/20000:ℝ)<cost (role r) kind .outer true false a b A B x := by
  have hc : CoreState a b := by simpa [State,hk] using hs
  rw [literal r kind hk ht]
  rcases hj with rfl | rfl
  · exact Source.original r hc ht hx hm
  · exact Target.original r hc ht hx hm

theorem original_core {i : Vertex} (hi : WordProblems.wrongWord .second i=0)
    {kind : RadialKind} (hk : kind≠.outer)
    {a b A B x : ℝ} (hs : State kind a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    threshold i<cost i kind .outer true false a b A B x := by
  rw [threshold_value]
  rcases zero_roles i hi with rfl | rfl | rfl
  · simpa [role] using original_core_row (0:Row) hk hs ht hx j hj hm
  · simpa [role] using original_core_row (1:Row) hk hs ht hx j hj hm
  · simpa [role] using original_core_row (2:Row) hk hs ht hx j hj hm

theorem original {i : Vertex} (hi : WordProblems.wrongWord .second i=0)
    {source target : RadialKind} (hmixed : Same.Mixed source target)
    {a b A B x : ℝ} (hs : State source a b) (ht : State target A B) (hx : |x|≤7/10)
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) x) :
    threshold i<cost i source target true false a b A B x := by
  rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
  · have ho : OuterState a b := by simpa [State] using hs
    have hir : WordProblems.wrongWord .second (reverseEdge i)=0 := by
      rcases zero_roles i hi with rfl | rfl | rfl <;>
        norm_num [WordProblems.wrongWord,reverseEdge]
    have hh : threshold (reverseEdge i)<cost (reverseEdge i) target .outer
        true false A B a b x := by
      rcases hj with rfl | rfl
      · exact original_core hir hcore ht ho hx 2 (Or.inr rfl)
          (by simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm)
      · exact original_core hir hcore ht ho hx 0 (Or.inl rfl)
          (by simpa [Eight.forwardMargin,add_comm,add_left_comm,add_assoc] using hm)
    have he := cost_reflection i .outer target true false a b A B x
    norm_num at he
    rw [he,threshold_value] at hh
    simpa only [threshold_value] using hh
  · have ho : OuterState A B := by simpa [State] using ht
    exact original_core hi hcore hs ho hx j hj hm

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Same.Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i≠positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .second hw i
  have hsigns : positiveOf C i=true ∧ positiveOf C (next i)=false := by
    cases hs : positiveOf C i <;> cases ht : positiveOf C (next i) <;>
      simp_all [WordProblems.allowed,hword]
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hm := original_margin C F hgap i j howner
  have hh := original hword hmixed (actual_state C i) (actual_state C (next i)) hx j haxis
    (by simpa [hsigns.1,hsigns.2,WordProblems.sign] using hm)
  have he : cost i (C.kind i) (C.kind (next i)) true false
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phaseValue F hgap i)=
      phaseValue F hgap i+wrongMarker C .second i-wrongMarker C .second (next i) := by
    simp only [cost,label,wrongMarker,hsigns.1,hsigns.2]
  rwa [he] at hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Same.Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i≠positiveOf C (next i)) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hmixed hsg j howner

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite
