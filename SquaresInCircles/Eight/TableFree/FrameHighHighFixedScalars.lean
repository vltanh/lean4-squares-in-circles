module

public import SquaresInCircles.Eight.TableFree.FrameHighHighFixedReferences

/-!
# All fixed-target high/high support intervals

Uncompiled source draft.  Actual endpoint comparisons, convexity of the
first derivative, and the two exact amplitude bounds cover every fixed
support in the high/high geometric decomposition.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighHighFixedScalars
open FrameHighHighFixedCalculus FrameHighHighFixedReferences

theorem positive_lower (cut : Bool) {x : ℝ} (hx : x∈Icc (7/20:ℝ) (6/5)) :
    (9099/10000:ℝ)<F false true true cut (39/100) x := by
  have hc := positive_coefficients cut
  have hm := endpoint_minimum false true true cut (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le (positive_last_slope cut)
  exact (lt_min (positive_left cut) (positive_right cut)).trans_le hm

theorem plus_minus_first_lower {x : ℝ} (hx : x∈Icc (7/20:ℝ) (3/5)) :
    (9099/10000:ℝ)<F true true false true (11/20) x := by
  have hc := plus_minus_first_coefficients
  have hm := endpoint_minimum true true false true (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le plus_minus_first_slope
  exact (lt_min plus_minus_first_left plus_minus_first_right).trans_le hm

theorem plus_minus_middle_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (4/5)) :
    (9099/10000:ℝ)<F false true false true (43/100) x := by
  have hc := plus_minus_middle_coefficients
  have hm := endpoint_minimum false true false true (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le plus_minus_middle_slope
  exact (lt_min plus_minus_middle_left plus_minus_middle_right).trans_le hm

theorem plus_minus_last_lower (cut : Bool) {x : ℝ} (hx : (4/5:ℝ)≤x) :
    (9099/10000:ℝ)<F false true false cut (17/50) x :=
  (plus_minus_last_left cut).trans_le
    (amplitude_monotone false true false cut (small_multiplier_amplitude cut) hx)

theorem minus_minus_last_lower (cut : Bool) {x : ℝ} (hx : (19/20:ℝ)≤x) :
    (9099/10000:ℝ)<F true false false cut (17/50) x :=
  (minus_minus_last_left cut).trans_le
    (amplitude_monotone true false false cut (small_multiplier_amplitude cut) hx)

theorem minus_plus_first_lower {x : ℝ} (hx : x∈Icc (1:ℝ) (13/10)) :
    (9099/10000:ℝ)<F true false true false (2/5) x := by
  have hc := minus_plus_first_coefficients
  have hm := endpoint_minimum true false true false (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le minus_plus_first_slope
  exact (lt_min minus_plus_first_left minus_plus_first_right).trans_le hm

end SquaresInCircles.Eight.TableFree.FrameHighHighFixedScalars
