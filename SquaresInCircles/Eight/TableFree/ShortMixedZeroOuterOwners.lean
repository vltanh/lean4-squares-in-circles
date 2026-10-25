module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroContact

/-!
# Original role labels and original owners for the mixed opposite cases

The analytic outer-source family is restored to the actual short-word
roles without changing a chosen vertex label. Source-secondary outer/core
pairs and target-secondary core/outer pairs are covered on both complete
angle halves. The reflected presentation of the latter is an exact
coordinate and coefficient identity. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems TableFreeWordGeometry

def outerRow (i : Vertex) : Row := if i=0 then 0 else if i=1 then 2 else 4
def coreRow (i : Vertex) : Row := if i=0 then 1 else if i=1 then 3 else 5

lemma zero_role (i : Vertex) (hi : wrongWord .short i=0) : i=0 ∨ i=1 ∨ i=3 := by
  revert hi
  fin_cases i <;> decide

lemma outer_role_cost (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) (a b A B φ : ℝ) :
    φ+wrongValue .short i .outer true a b-wrongValue .short (next i) kind false A B=
      φ+c (outerRow i)-p (outerRow i)*a+q (outerRow i)*b+g (outerRow i)*B := by
  rcases hi with rfl | rfl | rfl <;>
    norm_num [outerRow,wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next,c,p,q,g] <;> ring

lemma core_role_reversed_cost (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) (a b A B φ : ℝ) :
    φ+wrongValue .short i kind true a b-wrongValue .short (next i) .outer false A B=
      φ+c (coreRow i)-p (coreRow i)*A+q (coreRow i)*B+g (coreRow i)*b := by
  rcases hi with rfl | rfl | rfl <;>
    norm_num [coreRow,wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next,c,p,q,g] <;> ring

theorem opposite_outer_signed (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+c r-p r*a+q r*b+g r*B := by
  have hm' : pairWidth φ≤b+A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    linarith
  by_cases hp : 0≤φ
  · have hx : φ∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hφ).2⟩
    have hw := signed_width hφ
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    apply opposite_outer_positive r hs ht hx
    rw [hw] at hm'
    linarith
  · have hx : -φ∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    have hsin : Real.sin φ≤0 := by
      have hh := (positive_trig hx).2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hφ
    rw [abs_of_nonpos hsin] at hw
    have hh := opposite_outer_negative r hs ht hx (by
      rw [hw] at hm'
      rw [Real.sin_neg,Real.cos_neg]
      linarith)
    simpa only [neg_neg] using hh

/-- Original source-secondary outer/core owner, with the exact fixed
short-word role labels at both ends. -/
theorem original_outer_secondary (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer true a b-
      wrongValue .short (next i) kind false A B := by
  rw [outer_role_cost i hi kind hk]
  exact opposite_outer_signed (outerRow i) hs ht hφ hm

/-- Original target-secondary core/outer owner. Reflection/reversal
only changes the presentation of its original projection and labels. -/
theorem original_core_target_secondary (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind true a b-
      wrongValue .short (next i) .outer false A B := by
  have hrev : 0≤forwardMargin 0 A B a b 1 (-1) φ := by
    simpa [forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  rw [core_role_reversed_cost i hi kind hk]
  exact opposite_outer_signed (coreRow i) ht hs hφ hrev

theorem actual_outer_opposite (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hsign : positiveOf C i=true) (htsign : positiveOf C (next i)=false)
    (hs : C.kind i=.outer) (ht : C.kind (next i)≠.outer)
    (howner : (forwardAxis 0).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hi : i=0 ∨ i=1 ∨ i=3 := zero_role i (by simpa [hw] using hk)
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : CoreState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hangle : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  have hm := original_margin C F hgap i 0 howner
  have hm' : 0≤forwardMargin 0 (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      1 (-1) (phaseValue F hgap i) := by simpa [hsign,htsign,sign] using hm
  have hh := original_outer_secondary i hi (C.kind (next i)) ht hsource htarget hangle hm'
  simpa [wrongMarker,hs,hsign,htsign] using hh

theorem actual_core_target_opposite (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hsign : positiveOf C i=true) (htsign : positiveOf C (next i)=false)
    (hs : C.kind i≠.outer) (ht : C.kind (next i)=.outer)
    (howner : (forwardAxis 2).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hi : i=0 ∨ i=1 ∨ i=3 := zero_role i (by simpa [hw] using hk)
  have hsource : CoreState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hangle : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  have hm := original_margin C F hgap i 2 howner
  have hm' : 0≤forwardMargin 2 (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      1 (-1) (phaseValue F hgap i) := by simpa [hsign,htsign,sign] using hm
  have hh := original_core_target_secondary i hi (C.kind i) hs hsource htarget hangle hm'
  simpa [wrongMarker,ht,hsign,htsign] using hh

end SquaresInCircles.Eight.TableFree.ShortMixedZero
