module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerFirst
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeLowerReverse
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeSourcePrimary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperSecondary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ThreeUpperTarget

/-!
# Eight squares: all original owners of the negative-to-positive outer edge three

The four weak separating axes are covered on both sides of the
quarter angle.  The lower-secondary minima use their complete physical
contact domains; the remaining owners use the original aligned,
primary and diagonal comparisons.  Both closed angle endpoints and
all owner ties remain in the statement.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeThree
open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  fin_cases j
  · exact original_lower_source_secondary hs ht hx hm
  · exact original_lower_target_primary hs ht hx hm
  · exact original_lower_target_secondary hs ht hx hm
  · linarith [original_lower_source_primary hs ht hx hm]

theorem original_upper {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  fin_cases j
  · linarith [original_upper_source_secondary hs ht hx hm]
  · exact original_upper_target_primary hs ht hx hm
  · linarith [original_upper_target_secondary hs ht hx hm]
  · linarith [original_upper_source_primary hs ht hx hm]

theorem original_at_angle {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (89777/100000:ℝ)<value b B φ := by
  by_cases hupper : Real.pi/2≤φ
  · have hx : φ-Real.pi/2∈Icc 0 (7/10) :=
      ⟨by linarith,(abs_le.mp hφ).2⟩
    have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
    have hmargin : 0≤Eight.forwardMargin j a b A B (-1) 1
        (Real.pi/2+(φ-Real.pi/2)) := by simpa only [he] using hm
    simpa only [he] using original_upper hs ht hx j hmargin
  · have hx : Real.pi/2-φ∈Icc 0 (7/10) :=
      ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    have he : Real.pi/2-(Real.pi/2-φ)=φ := by ring
    have hmargin : 0≤Eight.forwardMargin j a b A B (-1) 1
        (Real.pi/2-(Real.pi/2-φ)) := by simpa only [he] using hm
    simpa only [he] using original_lower hs ht hx j hmargin

end SquaresInCircles.Eight.SecondWord.OppositeThree
