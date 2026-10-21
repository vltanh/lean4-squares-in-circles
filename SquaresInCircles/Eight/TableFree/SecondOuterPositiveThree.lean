module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeLateEntry
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeProjection
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeUpperEasy
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeUpperFirst
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeOwnerOrder

/-!
# Every original weak owner for the positive second-word edge three

Both closed angle halves and all four original axes are included.
The lower first owner uses actual short-source and zero-source
contacts with the original physical diagonal endpoints.  No
contact reduction or endpoint bound is an input to this theorem.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_source_secondary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  by_cases h : φ≤13/10
  · exact Early.original hs ht ⟨hφ.1,h⟩ hm
  · exact Late.original hs ht ⟨le_of_not_ge h,hφ.2⟩ hm

theorem original_lower_target_primary {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 1 a b A B 1 1 φ) :
    (44889/50000:ℝ)<value b B φ :=
  original_lower_source_secondary hs ht hφ (lower_second_implies_first hs ht hφ hm)

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · exact original_upper_source_secondary hs ht hupper hm
    · exact original_upper_target_primary hs ht hupper hm
    · linarith [original_upper_target_secondary hs ht hupper hm]
    · exact original_upper_source_primary hs ht hupper hm
  · have hlower : Lower (Real.pi/2+x) := by
      dsimp [Lower,lowerAngle]
      constructor <;> linarith [hx.1]
    fin_cases j
    · linarith [original_lower_source_secondary hs ht hlower hm]
    · linarith [original_lower_target_primary hs ht hlower hm]
    · linarith [original_lower_target_secondary hs ht hlower hm]
    · linarith [original_lower_source_primary hs ht hlower hm]

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

theorem original_some_axis {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : ∃j : Fin 4, 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<value b B φ := by
  obtain ⟨j,hj⟩ := hm
  exact original_at_angle hs ht hφ j hj

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree
