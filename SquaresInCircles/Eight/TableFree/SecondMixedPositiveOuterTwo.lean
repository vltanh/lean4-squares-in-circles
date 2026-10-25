module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveOuterTwoOwners

/-!
# Complete negative-core to positive-outer role-two family

Every original weak axis is covered on both closed quarter halves.
The transverse core support excludes the third owner directly.  The
other owners use the proved whole-angle supports or the direct late
bound.  Both physical core pieces are retained.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hrad := core_radius_sq hs
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · apply lower_first hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply lower_primary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · have hlarge : 1≤a*Real.sin φ-b*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [ht.1]
      have he : (a*Real.sin φ-b*Real.cos φ)^2+
          (a*Real.cos φ+b*Real.sin φ)^2=a^2+b^2 := by
        linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (a*Real.cos φ+b*Real.sin φ)]
    · have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
      have hBs := mul_nonneg ht.1 (by linarith [htr.1] : 0≤Real.sin φ)
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1]
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    have htr := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htr.2.2.2.2.2]
    fin_cases j
    · apply upper_first ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_primary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · have hlarge : 1≤a*Real.cos x+b*Real.sin x := by
        norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
        linarith [ht.1]
      have he : (a*Real.cos x+b*Real.sin x)^2+
          (a*Real.sin x-b*Real.cos x)^2=a^2+b^2 := by
        linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq x)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (a*Real.sin x-b*Real.cos x)]
    · apply upper_fourth hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 2<cost 2 kind .outer false true a b A B φ := by
  rw [threshold_value,core_outer_negative_positive hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
