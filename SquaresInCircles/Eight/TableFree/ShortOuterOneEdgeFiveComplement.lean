module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneEdgeFiveAPrimary

/-!
# Every original owner in the edge-five complement

Uncompiled assembly of the 24 branches in
`HAND_SHORT_WORD_EDGE_FIVE_COMPLETE_WITHOUT_TABLES.md`.
The original ++ and -- owners are restored by the exact adjacent-state
reversals listed in Section 1; the +- owners and role-four corollary keep
their literal labels. Every weak separating-axis tie remains included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive
open CommonQuarter CorePairGeometry Arithmetic TableFreeWordGeometry

theorem secondary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Secondary r upper a b A B x) : (8981/10000:ℝ)<cost r upper a b A B x := by
  have hr : ARows r∨BRows r := by fin_cases r <;> norm_num [ARows,BRows]
  rcases hr with hr|hr
  · exact ASecondary.original r hr upper hs ht hx hm
  · linarith [BSecondary.original r hr upper hs ht hx hm]
theorem primary (r : Row) (upper : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : Primary r upper a b A B x) : (8981/10000:ℝ)<cost r upper a b A B x := by
  have hr : ARows r∨BRows r := by fin_cases r <;> norm_num [ARows,BRows]
  rcases hr with hr|hr
  · linarith [APrimary.original r hr upper hs ht hx hm]
  · linarith [BPrimary.original r hr upper hs ht hx hm]
theorem normalized (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (j : Fin 4) (hj : j=0∨j=3)
    (hm : 0≤Eight.forwardMargin j a b A B (σ r) (σ r) φ) :
    (8981/10000:ℝ)<φ+c r+p r*a+σ r*q r*b-P r*A-σ r*t r*B := by
  obtain ⟨upper,x,hx,rfl⟩ := ShortWord.MixedQuarter.angle_cover hφ
  rcases hj with rfl|rfl
  · exact secondary r upper hs ht hx (secondary_margin r upper hx hm)
  · exact primary r upper hs ht hx (primary_margin r upper hx hm)

macro "short_edge_five_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t,σ,positive] at * <;> linarith)

theorem same_original (sgn : Bool) (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign sgn) (WordProblems.sign sgn) φ) :
    (8981/10000:ℝ)<φ+wrongValue .short 5 .outer sgn a b-
      wrongValue .short (next 5) .outer sgn A B := by
  cases sgn
  · fin_cases j
    · have hh := normalized 2 hs ht hφ 0 (Or.inl rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal
    · have hh := normalized 1 ht hs hφ 3 (Or.inr rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 1 ht hs hφ 0 (Or.inl rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 2 hs ht hφ 3 (Or.inr rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal
  · fin_cases j
    · have hh := normalized 0 hs ht hφ 0 (Or.inl rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal
    · have hh := normalized 3 ht hs hφ 3 (Or.inr rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 3 ht hs hφ 0 (Or.inl rfl)
        (by simp [σ,positive,WordProblems.sign,Eight.forwardMargin] at hm ⊢; linarith)
      short_edge_five_literal
    · have hh := normalized 0 hs ht hφ 3 (Or.inr rfl)
        (by simpa [σ,positive,WordProblems.sign] using hm)
      short_edge_five_literal

def Complement (i : Vertex) (sgn target : Bool) : Prop :=
  (i=5 ∧ (sgn=target∨(sgn=true∧target=false)))∨(i=4∧sgn=true∧target=false)
theorem complement_original (i : Vertex) (sgn target : Bool)
    (hcase : Complement i sgn target) (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign sgn) (WordProblems.sign target) φ) :
    (8981/10000:ℝ)<φ+wrongValue .short i .outer sgn a b-
      wrongValue .short (next i) .outer target A B := by
  rcases hcase with ⟨rfl,hcase⟩|⟨rfl,rfl,rfl⟩
  · rcases hcase with rfl|⟨rfl,rfl⟩
    · exact same_original _ j hs ht hφ hm
    · have hh := PositiveNegative.original_five hs ht hφ j (by simpa [WordProblems.sign] using hm)
      linarith
  · linarith [PositiveNegative.original_four hs ht hφ]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hcase : Complement i (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hh := complement_original i (positiveOf C i) (positiveOf C (next i)) hcase j
    hsource htarget hφ (original_margin C F hgap i j howner)
  have hv : (8981/10000:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
    simpa only [wrongMarker,hs,ht] using hh
  have hΓ := ShortWord.Zero.threshold_le i
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.EdgeFive
