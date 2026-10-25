module

public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.TwoLabels
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoLower
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoUpper

/-!
# Eight squares: all original role-two negative-outer to positive-core owners

The four weak physical axes are exhausted on the full closed quarter
window.  The estimates keep the original circle point, radius and
core piece, and require no separately supplied strip theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds ht
  have hrad := core_radius_sq ht
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.sin φ-B*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [hs.1]
      have he : (A*Real.sin φ-B*Real.cos φ)^2+
          (A*Real.cos φ+B*Real.sin φ)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.cos φ+B*Real.sin φ)]
    · have hac := mul_nonneg (show 0≤a by linarith [hs.1,hs.2.1]) htr.2.2.1
      have hbs := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.sin φ)
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1]
    · apply lower_secondary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply lower_primary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    have htr := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htr.2.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.cos x+B*Real.sin x := by
        norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
        linarith [hs.1]
      have he : (A*Real.cos x+B*Real.sin x)^2+
          (A*Real.sin x-B*Real.cos x)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq x)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.sin x-B*Real.cos x)]
    · apply upper_second hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_secondary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_primary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 2<cost 2 .outer kind false true a b A B φ := by
  rw [threshold_value,outer_core_negative_positive hk hs]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
