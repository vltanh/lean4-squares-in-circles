module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroCoreNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroOuterOwners
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroSameOwners

/-!
# Eight squares: complete mixed zero-quarter component of the short wrong word

Every original mixed secondary witness is covered with its original
signed role labels and both closed core pieces. The cyclic zero-primary
theorem supplies a secondary witness from the actual selected separator
once the independent continuous G1 pair theorem is available on this
same cycle.
-/

section
/-!
## All original secondary owners of the mixed opposite-sign zero edges

Both directions of the core/outer edge are covered (`original_core_secondary`,
`original_outer_target_secondary`), with the exact short-word label at every original vertex.
Reflection only presents a target-secondary owner algebraically. The physical cycle, the
selected weak separator and both endpoint states are kept.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems QuarterWordGeometry

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

end SquaresInCircles.Eight.ShortMixedZero
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems QuarterWordGeometry

lemma zero_signs (i : Vertex) (hi : wrongWord .short i=0) (σ τ : Bool)
    (ha : allowed .short i σ τ) : σ=τ ∨ (σ=true ∧ τ=false) := by
  have hn := ha.2.2.2.2 hi
  cases σ <;> cases τ <;> simp_all

/-- The exhaustive original secondary-axis join. The only finite
case splits identify signs, radial roles and exact fixed coefficients. -/
theorem original_mixed_secondary (i : Vertex) (hi : wrongWord .short i=0)
    (source target : RadialKind) (σ τ : Bool) (ha : allowed .short i σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hmixed : (source=.outer ∧ target≠.outer) ∨ (source≠.outer ∧ target=.outer))
    (hφ : |φ|≤7/10) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i source σ a b-
      wrongValue .short (next i) target τ A B := by
  rcases zero_signs i hi σ τ ha with he | ⟨rfl,rfl⟩
  · subst τ
    rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
    · have ho : OuterState a b := by simpa [State] using hs
      have hc : CoreState A B := by simpa [State,hcore] using ht
      rcases hj with rfl | rfl
      · exact same_outer_source i hi target hcore σ ha ho hc hφ hm
      · exact same_outer_target i hi target hcore σ ha ho hc hφ hm
    · have hc : CoreState a b := by simpa [State,hcore] using hs
      have ho : OuterState A B := by simpa [State] using ht
      rcases hj with rfl | rfl
      · exact same_core_source i hi source hcore σ ha hc ho hφ hm
      · exact same_core_target i hi source hcore σ ha hc ho hφ hm
  · have hr := zero_role i hi
    have hm' : 0≤forwardMargin j a b A B 1 (-1) φ := by simpa [sign] using hm
    rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
    · have ho : OuterState a b := by simpa [State] using hs
      have hc : CoreState A B := by simpa [State,hcore] using ht
      rcases hj with rfl | rfl
      · exact original_outer_secondary i hr target hcore ho hc hφ hm'
      · exact original_outer_target_secondary i hr target hcore ho hc hφ hm'
    · have hc : CoreState a b := by simpa [State,hcore] using hs
      have ho : OuterState A B := by simpa [State] using ht
      rcases hj with rfl | rfl
      · exact original_core_secondary i hr source hcore hc ho hφ hm'
      · exact original_core_target_secondary i hr source hcore hc ho hφ hm'

theorem actual_mixed_zero_secondary (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord .short) (i : Vertex)
    (hk : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : (C.kind i=.outer ∧ C.kind (next i)≠.outer) ∨
      (C.kind i≠.outer ∧ C.kind (next i)=.outer))
    (j : Fin 4) (hj : j=0 ∨ j=2)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hi : wrongWord .short i=0 := by simpa [hw] using hk
  have hangle : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hk] using (difference_small F i).le
  exact original_mixed_secondary i hi (C.kind i) (C.kind (next i))
    (positiveOf C i) (positiveOf C (next i)) (actual_allowed C F hgap .short hw i)
    (actual_state C i) (actual_state C (next i)) hmixed hangle j hj
    (original_margin C F hgap i j howner)

end SquaresInCircles.Eight.ShortMixedZero
end
end
end
