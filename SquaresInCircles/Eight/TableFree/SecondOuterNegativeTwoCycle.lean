module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwo
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoCycle

/-!
# Original physical and cyclic negative edge-two inequalities

The literal role-two negative pair and its role-six positive reflection
retain the original weak owner.  The actual-cycle theorem uses the
existing selected separator, physical signs, common circle and quarter
lift; no new owner is chosen.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<SecondWord.cost 2 .outer .outer false false a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<SecondWord.cost 6 .outer .outer true true a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(1:ℝ)) (-(1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (2:Vertex) .outer .outer false false A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (σ τ : Bool)
    (hrole : (i=2 ∧ σ=false ∧ τ=false) ∨ (i=6 ∧ σ=true ∧ τ=true))
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<SecondWord.cost i .outer .outer σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hmargin : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_cost hs ht hφ j hmargin]
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 1 φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_reflected hs ht hφ j hmargin]

theorem original_physical (K J : UnitSquare) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hsource : K.center=rotate K (a,b))
    (htarget : J.center=rotate J (A,B))
    (hcos : relativeC K J=Real.cos φ) (hsin : relativeS K J=Real.sin φ)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (howner : (forwardAxis j).Feasible K J) :
    threshold 2<SecondWord.cost 2 .outer .outer false false a b A B φ := by
  have he := canonical_margin_identity j K J a b A B (-1) (-1) φ
    (by simpa using hsource) (by simpa using htarget) hcos hsin
  have hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ := by
    rw [←he]
    exact sub_nonneg.mpr howner
  rw [threshold_value]
  linarith [original_cost hs ht hφ j hm]

theorem original_reflected_physical (K J : UnitSquare) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hsource : K.center=rotate K (a,-b))
    (htarget : J.center=rotate J (A,-B))
    (hcos : relativeC K J=Real.cos φ) (hsin : relativeS K J=Real.sin φ)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (howner : (forwardAxis j).Feasible K J) :
    threshold 6<SecondWord.cost 6 .outer .outer true true a b A B φ := by
  have he := canonical_margin_identity j K J a b A B 1 1 φ
    (by simpa using hsource) (by simpa using htarget) hcos hsin
  have hm : 0≤Eight.forwardMargin j a b A B 1 1 φ := by
    rw [←he]
    exact sub_nonneg.mpr howner
  rw [threshold_value]
  linarith [original_reflected hs ht hφ j hm]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=2 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false) ∨
      (i=6 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
    ring
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,if_pos rfl] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,if_pos rfl] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original_role i (positiveOf C i) (positiveOf C (next i)) hrole
    hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=2 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false) ∨
      (i=6 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole hs ht j howner

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo
