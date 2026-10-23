module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroNegativeCore

/-!
# Same-sign mixed zero edges with their original role labels

The finite steps below identify only the exact role coefficients and
the two secondary-axis presentations. Their analytic estimates are
whole-interval theorems on the original core and outer states. No
geometric branch is discharged by a generated certificate.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems TableFreeWordGeometry

lemma positive_zero_roles (i : Vertex) (hi : wrongWord .short i=0)
    (ha : allowed .short i true true) : i=0 ∨ i=3 := by
  fin_cases i <;> norm_num [wrongWord,allowed,next] at hi ha ⊢

lemma negative_zero_roles (i : Vertex) (hi : wrongWord .short i=0)
    (ha : allowed .short i false false) : i=1 ∨ i=3 := by
  fin_cases i <;> norm_num [wrongWord,allowed,next] at hi ha ⊢

theorem same_outer_source (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) kind σ A B := by
  cases σ
  · exact (negative_source_core_target_false false hs.1 ht (by simpa [sign] using hm)).elim
  · have hm' : 0≤forwardMargin 0 a b A B 1 1 φ := by simpa [sign] using hm
    rcases positive_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveOuter.original_cost 0 hs ht hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveOuter.original_cost 2 hs ht hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith

theorem same_core_source (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind σ a b-
      wrongValue .short (next i) .outer σ A B := by
  cases σ
  · have hm' : 0≤forwardMargin 0 a b A B (-1) (-1) φ := by simpa [sign] using hm
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := NegativeContact.original_cost 0 hs ht hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := NegativeContact.original_cost 1 hs ht hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 a b A B 1 1 φ := by simpa [sign] using hm
    rcases positive_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveCore.original_cost 0 hs ht hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveCore.original_cost 3 hs ht hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith

theorem same_outer_target (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) kind σ A B := by
  cases σ
  · have hm' : 0≤forwardMargin 0 A B a b 1 1 φ := by
      simpa [forwardMargin,sign,add_comm,add_left_comm,add_assoc] using hm
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveCore.original_cost 1 ht hs hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveCore.original_cost 2 ht hs hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 A B a b (-1) (-1) φ := by
      simpa [forwardMargin,sign,add_comm,add_left_comm,add_assoc] using hm
    rcases positive_zero_roles i hi ha with rfl | rfl
    · have hh := NegativeContact.original_cost 2 ht hs hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := NegativeContact.original_cost 3 ht hs hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith

theorem same_core_target (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind σ a b-
      wrongValue .short (next i) .outer σ A B := by
  cases σ
  · have hm' : 0≤forwardMargin 0 A B a b 1 1 φ := by
      simpa [forwardMargin,sign,add_comm,add_left_comm,add_assoc] using hm
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveOuter.original_cost 1 ht hs hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveOuter.original_cost 3 ht hs hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 A B a b (-1) (sign false) φ := by
      simpa [forwardMargin,sign,add_comm,add_left_comm,add_assoc] using hm
    exact (negative_source_core_target_false false ht.1 hs hm').elim

end SquaresInCircles.Eight.TableFree.ShortMixedZero
