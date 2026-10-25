module

public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeFirstContact

/-!
# Order on the actual first-contact circle arc

The contact source coordinate increases by at least `0.19` times
the target-coordinate increase.  This quantitative order statement
retains equality and lets an original weak separator determine an
actual closed contact interval.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.FirstContact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

lemma sourceFirst_lower {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    (19/100:ℝ)<sourceFirst B φ := by
  have ht := lower_trig hφ
  have hr := (outer_ratio_bounds hB).1
  have hm := mul_lt_mul hr ht.1.le
    (by norm_num : (0:ℝ)<19121/25000)
    (by linarith [hr] : 0≤ratio B)
  dsimp [sourceFirst]
  nlinarith [ht.2.2.1]

lemma source_shift_monotone {φ : ℝ} (hφ : Lower φ) :
    MonotoneOn (fun B => source B φ-(19/100)*B) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => ((source_hasDerivAt hB φ).sub
      ((hasDerivAt_id B).const_mul (19/100))).continuousAt.continuousWithinAt)
    (fun B hB => (source_hasDerivAt (Ioo_subset_Icc_self hB) φ).sub
      ((hasDerivAt_id B).const_mul (19/100)))
    (fun B hB => by linarith [sourceFirst_lower (Ioo_subset_Icc_self hB) hφ])

theorem source_order {B C φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hC : C∈Icc 0 outerDiagonal) (hφ : Lower φ) (h : source B φ≤ source C φ) : B≤C := by
  rcases le_total B C with horder | horder
  · exact horder
  · have hh := source_shift_monotone hφ hC hB horder
    linarith

theorem source_le_iff {B C φ : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hC : C∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    source B φ≤ source C φ ↔ B≤C :=
  ⟨source_order hB hC hφ,source_monotone hφ hB hC⟩

end SquaresInCircles.Eight.TableFree.SecondWord.PositiveThree.FirstContact
