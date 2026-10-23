module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerTargetSecondary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerPrimary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerTargetPrimary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoUpperSecondary

/-!
# Every original weak owner for the second-word opposite edge two

Both physical half-angle intervals and all four original separating
axes are included.  The endpoint ties are retained; all contact
concentration and endpoint choices were proved in the preceding
geometric modules.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · exact original_upper_source_secondary hs ht hupper hm
    · exact original_upper_target_primary hs ht hupper hm
    · exact original_upper_target_secondary hs ht hupper hm
    · exact original_upper_source_primary hs ht hupper hm
  · have hlower : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [hx.1]⟩
    have he : Real.pi/2+x=Real.pi/2-(-x) := by ring
    rw [he] at hm ⊢
    fin_cases j
    · exact LowerSecondary.original hs ht hlower hm
    · have hh := original_lower_target_primary hs ht hlower hm
      linarith
    · exact original_lower_target_secondary hs ht hlower hm
    · exact original_lower_source_primary hs ht hlower hm

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

theorem original_some_axis {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : ∃j : Fin 4, 0≤forwardMargin j a b A B (-1) 1 φ) :
    (44889/50000:ℝ)<value b B φ := by
  obtain ⟨j,hj⟩ := hm
  exact original_at_angle hs ht hφ j hj

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

