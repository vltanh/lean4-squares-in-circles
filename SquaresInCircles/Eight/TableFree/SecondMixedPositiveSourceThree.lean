module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeEarly
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreeLate
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveSourceThreePrimary

/-!
# All original positive-core to positive-outer role-three owners

The complete lower primary and transverse estimates are joined with
the upper finite aligned comparison. The remaining axes are excluded
at their original signed projections, including every weak tie.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · have hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith
      by_cases he : φ≤13/10
      · exact Early.original ht ⟨hlow.1,he⟩ hsep
      · exact Late.original hcore.2.2.1 ht ⟨by linarith,hlo⟩ hsep
    · apply Primary.original hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · have hlarge : 1≤a*Real.sin φ+b*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [ht.1]
      have he : (a*Real.sin φ+b*Real.cos φ)^2+(a*Real.cos φ-b*Real.sin φ)^2=a^2+b^2 := by
        linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [core_radius_sq hs,sq_nonneg (a*Real.cos φ-b*Real.sin φ)]
    · have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
      have hBs := mul_nonneg ht.1 (show 0≤Real.sin φ by linarith [htr.1])
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith [hcore.2.1]
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    exact EdgeThreeAligned.positive_upper_original hs ht hx j hm

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    SecondWord.threshold 3<cost 3 kind .outer true true a b A B φ := by
  rw [threshold_value,core_outer_positive_positive hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveSource
