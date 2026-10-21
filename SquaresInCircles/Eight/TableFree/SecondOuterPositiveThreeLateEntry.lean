module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeZeroScalar
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeEarlyEntry

/-!
# Every original first owner on the later positive-quarter arc

An inactive source is controlled by the actual zero-source contact.
An active source lies on a closed physical contact interval beginning
there.  Its concave first derivative reduces the minimum to that
zero endpoint or to one of the two proved diagonal boundaries.
Every original weak tie is retained.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Late

open CommonQuarter CorePairGeometry Arithmetic

lemma zero_source {φ : ℝ} (hφ : ZeroContact.Domain φ) :
    FirstContact.source (SourceCurve.target ZeroContact.parameter φ) φ=0 := by
  have hh := SourceCurve.contact (ZeroContact.domain hφ) (ZeroContact.target_mem hφ)
  norm_num [ZeroContact.parameter] at hh
  exact hh

lemma zero_value {φ : ℝ} (hφ : ZeroContact.Domain φ) :
    (451/500:ℝ)<FirstContact.cost (SourceCurve.target ZeroContact.parameter φ) φ := by
  have hh := ZeroContact.cost_lower hφ
  simpa only [FirstContact.cost,ZeroContact.cost,value,zero_source hφ] using hh

theorem active_contact {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hφ : ZeroContact.Domain φ)
    (hsource : FirstContact.source B φ∈Icc 0 outerDiagonal) :
    (44889/50000:ℝ)<FirstContact.cost B φ := by
  let b0 := SourceCurve.target ZeroContact.parameter φ
  have hb0 : b0∈Icc 0 outerDiagonal := ZeroContact.target_mem hφ
  have hcut : FirstContact.source b0 φ=0 := zero_source hφ
  have hLower := (ZeroContact.domain hφ).2
  have hB0 : b0≤B := FirstContact.source_order hb0 hB hLower
    (by rw [hcut]; exact hsource.1)
  obtain ⟨e,he,hecap,hend⟩ := Early.physical_cap hB hsource.2
  have heout : e∈Icc 0 outerDiagonal := ⟨hB.1.trans he.1,he.2⟩
  have hdom : ∀ t∈Icc b0 e, FirstContact.Domain t φ := by
    intro t ht
    have htout : t∈Icc 0 outerDiagonal := ⟨hb0.1.trans ht.1,ht.2.trans he.2⟩
    have hlo := FirstContact.source_monotone hLower hb0 htout ht.1
    have hhi := FirstContact.source_monotone hLower htout heout ht.2
    rw [hcut] at hlo
    exact ⟨htout,⟨hlo,hhi.trans hecap⟩,hLower⟩
  have hh := MinimumCalculus.endpoint_minimum_of_third_nonpos
    (show B∈Icc b0 e from ⟨hB0,he.1⟩)
    (fun t ht => FirstContact.cost_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.first_hasDerivAt (hdom t ht))
    (fun t ht => FirstContact.second_hasDerivAt (hdom t ht))
    (fun t ht => (FirstContact.third_negative (hdom t ht)).le)
    (ZeroContact.original_derivative hφ)
  have hleft : (44889/50000:ℝ)<FirstContact.cost b0 φ := by
    have h := zero_value hφ
    dsimp [b0]
    linarith
  have hright : (44889/50000:ℝ)<FirstContact.cost e φ := by
    have heDom := hdom e ⟨hB0.trans he.1,le_rfl⟩
    rcases hend with hend | hend
    · subst e
      exact DiagonalTarget.original_contact heDom.2.1 hLower rfl
    · have h := DiagonalSource.original_contact heout hLower hend
      simpa only [FirstContact.cost,value,hend] using h
  exact (lt_min hleft hright).trans_le hh

theorem original {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : ZeroContact.Domain φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hLower := (ZeroContact.domain hφ).2
  have hc := FirstContact.original_cut ht hLower hm
  by_cases hinactive : FirstContact.source B φ≤0
  · have hzero := ZeroContact.cost_lower hφ
    have horder := FirstContact.source_order hB (ZeroContact.target_mem hφ) hLower
      (by rw [zero_source hφ]; exact hinactive)
    have hL := L_monotone hB (ZeroContact.target_mem hφ) horder
    have hV := V_monotone outer_zero_mem hb hb.1
    dsimp [ZeroContact.cost,value] at *
    linarith
  · have hsrc : FirstContact.source B φ∈Icc 0 outerDiagonal :=
      ⟨le_of_not_ge hinactive,hc.trans hb.2⟩
    have hh := active_contact hB hφ hsrc
    have hV := V_monotone hsrc hb hc
    dsimp [FirstContact.cost,value] at *
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.Late
