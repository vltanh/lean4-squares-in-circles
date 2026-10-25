module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroNegativeCore
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveCore
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveOuter

/-!
# Eight squares: same-sign mixed zero edges with their original role labels

The finite steps below identify only the exact role coefficients and the two secondary-axis
presentations (`positive_zero_roles`, `negative_zero_roles`). Their analytic estimates are
whole-interval theorems on the original core and outer states (`same_outer_source`,
`same_core_source`, `same_outer_target`, `same_core_target`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems QuarterWordGeometry

lemma positive_zero_roles (i : Vertex) (hi : wrongWord .short i=0)
    (ha : allowed .short i true true) : i=0 ∨ i=3 := by
  revert hi ha
  fin_cases i <;> decide

lemma negative_zero_roles (i : Vertex) (hi : wrongWord .short i=0)
    (ha : allowed .short i false false) : i=1 ∨ i=3 := by
  revert hi ha
  fin_cases i <;> decide

/-- The case `τ = false` of `CommonQuarter.negative_source_core_target_false`: a negative source
cannot own a core target on the negative secondary axis. -/
private lemma negative_source_core_target_false {a b A B φ : ℝ}
    (hb : 0≤b) (ht : CoreState A B)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : False := by
  have hcore := CorePairGeometry.core_radius_sq ht
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  have hproj : 1≤A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    linarith
  have hid : (A*Real.sin φ+B*Real.cos φ)^2+
      (A*Real.cos φ-B*Real.sin φ)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
  nlinarith [sq_nonneg (A*Real.cos φ-B*Real.sin φ),
    sq_nonneg (A*Real.sin φ+B*Real.cos φ-1)]

theorem same_outer_source (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) kind σ A B := by
  cases σ
  · exact (negative_source_core_target_false hs.1 ht (by simpa [sign] using hm)).elim
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
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
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
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
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
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveOuter.original_cost 1 ht hs hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveOuter.original_cost 3 ht hs hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 A B a b (-1) (-1) φ := by
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
    exact (negative_source_core_target_false ht.1 hs hm').elim

end SquaresInCircles.Eight.ShortMixedZero
