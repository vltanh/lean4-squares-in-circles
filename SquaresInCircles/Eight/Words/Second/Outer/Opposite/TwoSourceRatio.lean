module

public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoData

/-!
# Eight squares: the whole-circle source speed comparison

Convexity supplies one affine upper bound for the source derivative.
Two exact circle supports then pay the full angular displacement on
the original interval.  The argument has no source-coordinate cells.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma P_first_zero : PLabel.d1 0<387/500 := P_first_zero_bounds.2

lemma P_first_affine {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    PLabel.d1 b<387/500+(223/1000)*b := by
  have hh := positive_of_second_nonpos
    (f := fun t => 387/500+(223/1000)*t-PLabel.d1 t)
    (d := fun t => 223/1000-PLabel.d2 t)
    (dd := fun t => -PLabel.d3 t) hb
    (fun t ht => ((((hasDerivAt_id t).const_mul (223/1000)).const_add (387/500)).sub
        (PLabel.d1_hasDerivAt (outer_domain ht))).congr_deriv (by ring))
    (fun t ht => (PLabel.d2_hasDerivAt (outer_domain ht)).const_sub (223/1000))
    (fun t ht => neg_nonpos.mpr (P_third_positive ht).le)
    (by simpa using sub_pos.mpr P_first_zero)
    (by rw [P_first_diagonal]; linarith [fine_outer_endpoint_bounds.2])
  linarith

lemma k_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<k b x := by
  have hh := mul_nonneg (by linarith [(outer_ratio_bounds hb).1] : 0≤ratio b)
    (positive_trig hx).2.2.1
  dsimp [k]
  linarith [(positive_trig hx).1]

end SquaresInCircles.Eight.SecondWord.OppositeTwo
