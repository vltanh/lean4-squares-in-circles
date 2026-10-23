module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeUpperDiagonalReference

/-!
# The entire original target-diagonal boundary

One tangent parabola controls the whole initial source interval; the
analytic source motion controls its entire complement.  The result is
strictly above the opposite edge-three entry on every source state.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperDiagonal
open CommonQuarter CorePairGeometry Arithmetic

theorem early_lower {b : ℝ} (hb : b∈Icc 0 (1/10)) :
    (89777/100000:ℝ)<value b := by
  have ht := curvature_tangent (κ := (9/10:ℝ)) hb reference_mem
    (fun t ht => value_hasDerivAt (early_domain ht))
    (fun t ht => first_hasDerivAt (early_domain ht))
    (fun t ht => (early_curvature ht).le)
  have hs := abs_lt.mp reference_first
  have hsq : (first reference)^2<(1/1000000:ℝ)^2 := by nlinarith
  nlinarith [reference_value,sq_nonneg ((9/10)*(b-reference)+first reference)]

theorem lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (89777/100000:ℝ)<value b := by
  by_cases hearly : b≤1/10
  · exact early_lower ⟨hb.1,hearly⟩
  · have hh := late_monotone
      ⟨le_rfl,UpperTarget.tenth_mem.2⟩ ⟨by linarith,hb.2⟩ (by linarith)
    exact (early_lower (show (1/10:ℝ)∈Icc 0 (1/10) by norm_num)).trans_le hh

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeThree.UpperDiagonal
