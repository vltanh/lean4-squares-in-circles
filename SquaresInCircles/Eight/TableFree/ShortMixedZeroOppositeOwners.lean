module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroCoreNegative

/-!
# All original secondary owners of the mixed opposite-sign zero edges

Both directions of the core/outer edge are covered, with the exact
short-word label at every original vertex. Reflection is used only as
an algebraic presentation of a target-secondary owner. The physical
cycle, the selected weak separator and both endpoint states are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems TableFreeWordGeometry

theorem opposite_core_signed (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+c r+g r*b-p r*A+q r*B := by
  have hm' : pairWidth φ≤b+A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    linarith
  by_cases hp : 0≤φ
  · have hx : φ∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hφ).2⟩
    have hw := signed_width hφ
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    apply opposite_core_positive r hs ht hx
    rw [hw] at hm'
    linarith
  · have hx : -φ∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    have hsin : Real.sin φ≤0 := by
      have hh := (positive_trig hx).2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hφ
    rw [abs_of_nonpos hsin] at hw
    have hh := opposite_core_negative r hs ht hx (by
      rw [hw] at hm'
      rw [Real.sin_neg,Real.cos_neg]
      linarith)
    simpa only [neg_neg] using hh

theorem original_core_secondary (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind true a b-
      wrongValue .short (next i) .outer false A B := by
  rw [core_role_reversed_cost i hi kind hk]
  have hh := opposite_core_signed (coreRow i) hs ht hφ hm
  linarith

theorem original_outer_target_secondary (i : Vertex) (hi : i=0 ∨ i=1 ∨ i=3)
    (kind : RadialKind) (hk : kind≠.outer) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B 1 (-1) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer true a b-
      wrongValue .short (next i) kind false A B := by
  have hrev : 0≤forwardMargin 0 A B a b 1 (-1) φ := by
    simpa [forwardMargin,add_comm,add_left_comm,add_assoc] using hm
  rw [outer_role_cost i hi kind hk]
  have hh := opposite_core_signed (outerRow i) ht hs hφ hrev
  linarith

theorem actual_core_opposite (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hsign : positiveOf C i=true) (htsign : positiveOf C (next i)=false)
    (hs : C.kind i≠.outer) (ht : C.kind (next i)=.outer)
    (howner : (forwardAxis 0).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hi := zero_role i (by simpa [hw] using hk)
  have hsource : CoreState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hangle : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  have hm := original_margin C F hgap i 0 howner
  have hm' : 0≤forwardMargin 0 (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      1 (-1) (phaseValue F hgap i) := by simpa [hsign,htsign,sign] using hm
  have hh := original_core_secondary i hi (C.kind i) hs hsource htarget hangle hm'
  simpa [wrongMarker,ht,hsign,htsign] using hh

theorem actual_outer_target_opposite (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hsign : positiveOf C i=true) (htsign : positiveOf C (next i)=false)
    (hs : C.kind i=.outer) (ht : C.kind (next i)≠.outer)
    (howner : (forwardAxis 2).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hi := zero_role i (by simpa [hw] using hk)
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : CoreState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hangle : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  have hm := original_margin C F hgap i 2 howner
  have hm' : 0≤forwardMargin 2 (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      1 (-1) (phaseValue F hgap i) := by simpa [hsign,htsign,sign] using hm
  have hh := original_outer_target_secondary i hi (C.kind (next i)) ht hsource htarget hangle hm'
  simpa [wrongMarker,hs,hsign,htsign] using hh

end SquaresInCircles.Eight.TableFree.ShortMixedZero
