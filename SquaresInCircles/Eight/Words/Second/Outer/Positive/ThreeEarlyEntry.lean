module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeContactOrder
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeDiagonalSource
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeDiagonalTarget
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCut
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyTarget

/-!
# Eight squares: every original first owner on the early positive-quarter arc

The actual weak separator either reaches the short-source support,
or determines a closed physical contact interval.  Its left endpoint
is the actual `0.35` cut; its right endpoint is the target diagonal
or the first source-diagonal contact, constructed by IVT.  The
concave derivative reduces to these proved geometric endpoints.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.Early

open CommonQuarter CorePairGeometry Arithmetic

lemma short_of_cut {b B φ : ℝ} (hb : b∈Icc (0:ℝ) (7/20))
    (hB : B∈Icc 0 outerDiagonal) (hφ : φ∈Icc lowerAngle (13/10))
    (hc : FirstContact.source B φ≤b) : (451/500:ℝ)<value b B φ := by
  have hminor := (minorant_lower hφ).trans_le (minorant_le_support hB hφ)
  have hV := V_chord_short hb
  have hz := V_zero_bounds.1
  have hcost : support B φ<value b B φ := by
    dsimp [FirstContact.source,support,value,g] at *
    linarith
  exact hminor.trans hcost

lemma cut_source {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    FirstContact.source (SourceCurve.target EarlyCut.parameter φ) φ=7/20 := by
  have hh := SourceCurve.contact (EarlyCut.domain hφ) (EarlyCut.target_mem hφ)
  norm_num [EarlyCut.parameter] at hh
  exact hh

lemma cut_value {φ : ℝ} (hφ : φ∈Icc lowerAngle (13/10)) :
    (451/500:ℝ)<FirstContact.cost (SourceCurve.target EarlyCut.parameter φ) φ := by
  have hh := short_of_cut (show (7/20:ℝ)∈Icc 0 (7/20) by norm_num)
    (EarlyCut.target_mem hφ) hφ (cut_source hφ).le
  simpa only [FirstContact.cost,value,cut_source hφ] using hh

lemma physical_cap {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hc : FirstContact.source B φ≤outerDiagonal) :
    ∃ e : ℝ, e∈Icc B outerDiagonal ∧ FirstContact.source e φ≤outerDiagonal ∧
      (e=outerDiagonal ∨ FirstContact.source e φ=outerDiagonal) := by
  by_cases hd : FirstContact.source outerDiagonal φ≤outerDiagonal
  · exact ⟨outerDiagonal,⟨hB.2,le_rfl⟩,hd,Or.inl rfl⟩
  · have hcont : ContinuousOn (fun t => FirstContact.source t φ) (Icc B outerDiagonal) := by
      intro t ht
      exact (FirstContact.source_hasDerivAt ⟨hB.1.trans ht.1,ht.2⟩ φ).continuousAt.continuousWithinAt
    obtain ⟨e,he,heq⟩ := intermediate_value_Icc hB.2 hcont
      (show outerDiagonal∈Icc (FirstContact.source B φ)
        (FirstContact.source outerDiagonal φ) from ⟨hc,le_of_not_ge hd⟩)
    exact ⟨e,he,heq.le,Or.inr heq⟩

theorem active_contact {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : φ∈Icc lowerAngle (13/10))
    (hsource : FirstContact.source B φ∈Icc (7/20:ℝ) outerDiagonal) :
    (44889/50000:ℝ)<FirstContact.cost B φ := by
  let b0 := SourceCurve.target EarlyCut.parameter φ
  have hb0 : b0∈Icc 0 outerDiagonal := EarlyCut.target_mem hφ
  have hcut : FirstContact.source b0 φ=7/20 := cut_source hφ
  have hB0 : b0≤B := FirstContact.source_order hb0 hB (early_lower hφ)
    (by rw [hcut]; exact hsource.1)
  obtain ⟨e,he,hecap,hend⟩ := physical_cap hB hsource.2
  have heout : e∈Icc 0 outerDiagonal := ⟨hB.1.trans he.1,he.2⟩
  have hdom : ∀ t∈Icc b0 e, FirstContact.Domain t φ := by
    intro t ht
    have htout : t∈Icc 0 outerDiagonal := ⟨hb0.1.trans ht.1,ht.2.trans he.2⟩
    have hlo := FirstContact.source_monotone (early_lower hφ) hb0 htout ht.1
    have hhi := FirstContact.source_monotone (early_lower hφ) htout heout ht.2
    dsimp only at hlo hhi
    rw [hcut] at hlo
    exact ⟨htout,⟨by linarith,hhi.trans hecap⟩,early_lower hφ⟩
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (show B∈Icc b0 e from ⟨hB0,he.1⟩)
    (fun t ht => FirstContact.cost_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.first_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.second_hasDerivAt (hdom t ht))
    (fun t ht => (FirstContact.third_negative (hdom t ht)).le)
    (EarlyCut.original_derivative hφ)
  have hleft : (44889/50000:ℝ)<FirstContact.cost b0 φ := by
    have h := cut_value hφ
    dsimp [b0]
    linarith
  have hright : (44889/50000:ℝ)<FirstContact.cost e φ := by
    have heDom := hdom e ⟨hB0.trans he.1,le_rfl⟩
    rcases hend with hend | hend
    · subst e
      exact DiagonalTarget.original_contact heDom.2.1 (early_lower hφ) rfl
    · have h := DiagonalSource.original_contact heout (early_lower hφ) hend
      simpa only [FirstContact.cost,value,hend] using h
  exact (lt_min hleft hright).trans_le hh

theorem original {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : φ∈Icc lowerAngle (13/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hc := FirstContact.original_cut ht (early_lower hφ) hm
  by_cases hshort : b≤7/20
  · have hh := original_short hs ht hφ hshort hm
    linarith
  · by_cases hcut : FirstContact.source B φ≤7/20
    · have hh := short_of_cut (show (7/20:ℝ)∈Icc 0 (7/20) by norm_num) hB hφ hcut
      have hV := V_monotone V_short_mem hb (le_of_not_ge hshort)
      dsimp [value] at *
      linarith
    · have hsrc : FirstContact.source B φ∈Icc (7/20:ℝ) outerDiagonal :=
        ⟨le_of_not_ge hcut,hc.trans hb.2⟩
      have hh := active_contact hB hφ hsrc
      have hV := V_monotone ⟨by linarith [hsrc.1],hsrc.2⟩ hb hc
      dsimp [FirstContact.cost,value] at *
      linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.Early
