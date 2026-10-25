module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerSecondary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerPrimary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveUpperSecondary
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveUpperPrimary

/-!
# All four original opposite-sign edge-five owners

Uncompiled assembly of
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`.
Both entire angle halves are included. The target-owned axes are
restored by the literal reversal of the two adjacent coefficient
tuples. All original weak owner ties are retained, and the final
cycle statement uses the original role-five and role-six markers.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

theorem secondary (r : Bool) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 φ) :
    threshold<φ+c+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,u,hu,rfl⟩ := Unit.angle_cover hφ
  have hsep := OppositeSecondary.margin high hu hm
  cases high
  · have hh := LowerSecondary.original r hs ht hu (by
      simp only [Unit.direction,width,Bool.false_eq_true,↓reduceIte] at hsep ⊢
      linarith)
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh := UpperSecondary.original r hs ht hu (by
      simp only [Unit.direction,ite_true] at hsep
      linarith)
    simp only [Unit.angle,Unit.direction,ite_true,threshold]
    linarith

theorem primary (r : Bool) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 φ) :
    threshold<φ+c+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,u,hu,rfl⟩ := Unit.angle_cover hφ
  have hsep := Opposite.Primary.normalized_margin high hu hm
  cases high
  · have hh := LowerPrimary.original r hs ht hu (by
      simp only [Unit.direction,width,Opposite.Primary.width,Bool.false_eq_true,
        ↓reduceIte] at hsep ⊢
      linarith)
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh := UpperPrimary.original r hs ht hu (by
      simp only [Unit.direction,Opposite.Primary.width,ite_true] at hsep
      linarith)
    simp only [Unit.angle,Unit.direction,ite_true,threshold]
    linarith

theorem original_owner (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold<φ+c+p false*a-q false*b-P false*A-t false*B := by
  fin_cases j
  · exact secondary false hs ht hφ hm
  · have hh := primary true ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [p,q,P,t,pQ,qQ,PQ,tQ] at hh ⊢
    linarith
  · have hh := secondary true ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [p,q,P,t,pQ,qQ,PQ,tQ] at hh ⊢
    linarith
  · exact primary false hs ht hφ hm

theorem original {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : ∃j : Fin 4,0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold<φ+c+p false*a-q false*b-P false*A-t false*B := by
  obtain ⟨j,hj⟩ := hm
  exact original_owner j hs ht hφ hj

theorem marker_owner (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (WordProblems.wrongGamma .short 5:ℝ)<φ+wrongValue .short 5 .outer false a b-
      wrongValue .short (next 5) .outer true A B := by
  have hh := original_owner j hs ht hφ hm
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
    threshold,c,p,q,P,t,pQ,qQ,PQ,tQ] at hh ⊢
  linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) (hrole : i=5)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  subst hrole
  have he : phaseValue F hgap 5-Real.pi/2=difference F 5 := by
    simp [phaseValue,hi]
  have hφ : |phaseValue F hgap 5-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F 5).le
  have hsource : OuterState (C.a 5) (C.b 5) := by
    simpa [State,hs] using actual_state C 5
  have htarget : OuterState (C.a (next 5)) (C.b (next 5)) := by
    simpa [State,ht] using actual_state C (next 5)
  have hm := original_margin C F hgap 5 j howner
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,ite_false,ite_true,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := marker_owner j hsource htarget hφ hm
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive
