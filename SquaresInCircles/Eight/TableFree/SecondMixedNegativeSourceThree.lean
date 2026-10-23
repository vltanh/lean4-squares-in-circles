module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreePrimary

/-!
# All original negative-core to positive-outer role-three owners

The completed lower transverse and primary estimates join the upper
finite aligned comparison. Both remaining lower axes are excluded at
their original signed projections. Every weak tie and core-side join
is included. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value a b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds hs
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · apply transverse_original hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply Primary.original hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · have ha := mul_nonneg (show 0≤a by linarith [hcore.1])
        (show 0≤1-Real.sin φ by linarith [htr.2.1])
      have hb := mul_nonneg hcore.2.2.1 htr.2.2.1
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1,ht.1]
    · have hAc := mul_nonneg (show 0≤A by linarith [ht.1,ht.2.1]) htr.2.2.1
      have hBs := mul_nonneg ht.1 (show 0≤Real.sin φ by linarith [htr.1])
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith [hcore.2.1]
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    exact EdgeThreeAligned.negative_upper_original hs ht hx j hm

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 3<cost 3 kind .outer false true a b A B φ := by
  rw [threshold_value,core_outer_negative_positive hk ht]
  exact original hs ht hφ j hm

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource
