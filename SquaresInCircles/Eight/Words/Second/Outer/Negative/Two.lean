module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoUpperTarget
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoUpperSource
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLowerTarget
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLowerSource

/-!
# Eight squares: every original weak owner for the second-word negative edge two

Both closed physical half-angle intervals and all four original axes are
included.  The lower target-secondary contact and the lower source-primary
contact have actual, complete boundary reductions.  No favorable owner
or endpoint is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · linarith [original_upper_source_secondary hs ht hupper hm]
    · linarith [original_upper_target_primary hs ht hupper hm]
    · linarith [original_upper_target_secondary hs ht hupper hm]
    · linarith [original_upper_source_primary hs ht hupper hm]
  · have hlower : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [hx.1]⟩
    have he : Real.pi/2+x=Real.pi/2-(-x) := by ring
    rw [he] at hm ⊢
    fin_cases j
    · linarith [original_lower_source_secondary hs ht hlower hm]
    · linarith [original_lower_target_primary hs ht hlower hm]
    · exact original_lower_target_secondary hs ht hlower hm
    · linarith [original_lower_source_primary hs ht hlower hm]

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

end SquaresInCircles.Eight.SecondWord.NegativeTwo
