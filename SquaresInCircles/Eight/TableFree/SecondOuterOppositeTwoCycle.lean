module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwo

/-!
# Original physical and cyclic opposite edge-two inequalities

The scalar theorem is restored to the original role labels and physical
weak separating axes.  Reflected reversal transports both the owner
and the two vertex labels.  The cycle theorem consumes the original
selected witness and retains the original circle, signs and frame lift.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

def reflectedOwner (j : Fin 4) : Fin 4 := j+2

lemma margin_reflection (j : Fin 4) (a b A B σ τ φ : ℝ) :
    SquaresInCircles.Eight.forwardMargin (reflectedOwner j) A B a b (-τ) (-σ) φ=
      SquaresInCircles.Eight.forwardMargin j a b A B σ τ φ := by
  fin_cases j <;> norm_num [reflectedOwner,SquaresInCircles.Eight.forwardMargin] <;> ring

namespace OppositeTwo

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<SecondWord.cost 2 .outer .outer false true a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<SecondWord.cost 6 .outer .outer false true a b A B φ := by
  have hrev : 0≤SquaresInCircles.Eight.forwardMargin (reflectedOwner j)
      A B a b (-1) 1 φ := by
    simpa only [neg_neg] using
      (show 0≤SquaresInCircles.Eight.forwardMargin (reflectedOwner j)
        A B a b (-(1:ℝ)) (-(-1:ℝ)) φ from by
          rw [margin_reflection]
          exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (2:Vertex) .outer .outer false true A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (hi : i=2 ∨ i=6)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold i<SecondWord.cost i .outer .outer false true a b A B φ := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · linarith [original_cost hs ht hφ j hm]
  · linarith [original_reflected hs ht hφ j hm]

/-- The original squares, frame normals and weak owner imply the
edge-two inequality directly through their actual coordinate identity. -/
theorem original_physical (K J : UnitSquare) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hsource : K.center=rotate K (a,b))
    (htarget : J.center=rotate J (A,-B))
    (hcos : relativeC K J=Real.cos φ) (hsin : relativeS K J=Real.sin φ)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (howner : (forwardAxis j).Feasible K J) :
    threshold 2<SecondWord.cost 2 .outer .outer false true a b A B φ := by
  have he := canonical_margin_identity j K J a b A B (-1) 1 φ
    (by simpa using hsource) (by simpa using htarget) hcos hsin
  have hm : 0≤SquaresInCircles.Eight.forwardMargin j a b A B (-1) 1 φ := by
    rw [←he]
    exact sub_nonneg.mpr howner
  exact original_role 2 (Or.inl rfl) hs ht hφ j hm

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=2 ∨ i=6)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hi with rfl | rfl <;> norm_num [WordProblems.wrongWord]
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
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,if_false,if_true,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := original_role i hi hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht,hσ,hτ] using hh

/-- Every original selected separator is covered.  Only its existing
forward-axis index is recovered; no owner is replaced by a favorable one. -/
theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : i=2 ∨ i=6)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hs ht hσ hτ j howner

end OppositeTwo

end SquaresInCircles.Eight.TableFree.SecondWord
