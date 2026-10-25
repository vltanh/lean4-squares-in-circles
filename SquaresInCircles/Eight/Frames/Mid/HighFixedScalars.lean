module

public import SquaresInCircles.Eight.Frames.Mid.HighFixedReferences

/-!
# Eight squares: the remaining fixed-target middle/high support intervals

Each estimate belongs to the literal signed source and target support.
The first-quadrant intervals use endpoint minima or concavity, and the
two small-amplitude families are increasing on their entire real domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighFixedScalars
open FrameDiagonalArc FrameMidHighFixedCalculus FrameMidHighFixedReferences

theorem mh_plus_minus_lower {x : ℝ} (hx : x∈Icc (1/10:ℝ) (61/100)) :
    (4463/5000:ℝ)< mhPlusMinus x := by
  have hc := mh_plus_minus_coefficients
  have hm := endpoint_minimum true true false true false
    (S := FrameDiagonalSupport.sourceCircle true true (11/20))
    (by norm_num) (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le mh_plus_minus_last_slope
  exact (lt_min mh_plus_minus_left mh_plus_minus_right).trans_le hm

theorem mh_negative_lower {x : ℝ} (hx : (9/10:ℝ)≤x) :
    (4463/5000:ℝ)< mhNegative x :=
  mh_negative_left.trans_le
    (amplitude_monotone true true false false false (S := middleSource) mh_negative_amplitude hx)

theorem mh_opposite_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (13/10)) :
    (4463/5000:ℝ)< mhOpposite x := by
  have hc := mh_opposite_coefficients
  have hm := endpoint_minimum true true false false true (S := middleSource)
    (by norm_num) (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le mh_opposite_last_slope
  exact (lt_min mh_opposite_left mh_opposite_right).trans_le hm

theorem hm_positive_lower {x : ℝ} (hx : x∈Icc (11/10:ℝ) (71/50)) :
    (4463/5000:ℝ)<hmPositive x := by
  have hc := hm_positive_coefficients
  have hm := endpoint_minimum true false true true true
    (S := FrameDiagonalSupport.sourceCircle false true (1/2))
    (by norm_num) (by linarith [FrameLowPair.pi_lower]) hx hc.1.le hc.2.le hm_positive_last_slope
  exact (lt_min hm_positive_left hm_positive_right).trans_le hm

theorem hm_opposite_before_lower (cut : Bool) {x : ℝ}
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2-1/50)) :
    (4463/5000:ℝ)<hmOpposite true cut x := by
  cases cut
  · have hc := hm_opposite_first_coefficients
    have hm := endpoint_minimum true false true false true
      (S := FrameDiagonalSupport.sourceCircle false false (2/5))
      (by norm_num) (by linarith) hx hc.1.le hc.2.le hm_opposite_first_last_slope
    exact (lt_min (hm_opposite_left false) (hm_opposite_before_quarter false)).trans_le hm
  · have hc := hm_opposite_last_coefficients
    have hcon := concave true false true false true (2/5)
      (FrameDiagonalSupport.sourceCircle false false (2/5)) b2
      (by norm_num : (0:ℝ)≤13/10) (by linarith : Real.pi/2-1/50≤Real.pi/2) hc.1.le hc.2.le
    exact concave_gt_of_endpoints hcon hx (hm_opposite_left true) (hm_opposite_before_quarter true)

theorem hm_opposite_after_lower (cut : Bool) {x : ℝ} (hx : Real.pi/2+1/50≤x) :
    (4463/5000:ℝ)<hmOpposite false cut x :=
  (hm_opposite_after_quarter cut).trans_le
    (amplitude_monotone false false true false true
      (S := FrameDiagonalSupport.sourceCircle false false (2/5)) (hm_opposite_after_amplitude cut) hx)

end SquaresInCircles.Eight.FrameMidHighFixedScalars
