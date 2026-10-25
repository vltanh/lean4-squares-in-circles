module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeLowerReverse
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperSecondary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeSourcePrimary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperTarget

/-!
# All original owners of the negative-to-positive outer edge three

The four weak separating axes are covered on both sides of the
quarter angle.  The lower-secondary minima use their complete physical
contact domains; the remaining owners use the original aligned,
primary and diagonal comparisons.  Both closed angle endpoints and
all owner ties remain in the statement.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
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

theorem original_scalar {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  apply original_at_angle hs ht ?_ j hm
  have he : Real.pi/2+x-Real.pi/2=x := by ring
  rw [he]
  exact abs_le.mpr hx

theorem original_some_axis {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : ∃j : Fin 4, 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (89777/100000:ℝ)<value b B φ := by
  obtain ⟨j,hj⟩ := hm
  exact original_at_angle hs ht hφ j hj

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree
