module

public import SquaresInCircles.Eight.TableFree.GeometricExistenceCoordinates

/-!
# Boundary signs for the actual compact circle minimum

Uncompiled reconstruction.  The nominal circle stress is applied to
the actual radical chain at every point of the fixed position window.
The rational trial supplies the opposite sign at the upper radius.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GeometricExistence
open ExactFamily.FiveCornerGeometry Eight.FiveCorner

theorem lower_radius_defect_positive {u t : ℝ}
    (hu : u∈positionWindow) (ht : t∈closedTilts) :
    0<defect lowerRadius (Real.cos t) (Real.sin t) u := by
  by_contra! hF
  have hg := actual_gap_nonpos radius_order.1.le
    (radius_order.2.1.le.trans radius_order.2.2.le) hu ht hF
  linarith [lower_radius_gap_positive ht]

theorem endpoint_defect_positive {q u : ℝ}
    (hq : q∈Icc lowerRadius upperRadius) (hu : u∈positionWindow) :
    0<defect q (Real.cos 0) (Real.sin 0) u ∧
      0<defect q (Real.cos (Real.arctan (1/5))) (Real.sin (Real.arctan (1/5))) u := by
  have hql : (79/40:ℝ)^2≤q := radius_order.1.le.trans hq.1
  have hqu : q≤9789/2500 := hq.2.trans radius_order.2.2.le
  have ha : 0<Real.arctan (1/5:ℝ) := Real.arctan_pos.mpr (by norm_num)
  constructor
  · by_contra! hF
    have hg := actual_gap_nonpos hql hqu hu (show (0:ℝ)∈closedTilts from ⟨le_rfl,ha.le⟩) hF
    linarith [zero_tilt_gap_positive hq.2]
  · by_contra! hF
    have hg := actual_gap_nonpos hql hqu hu
      (show Real.arctan (1/5:ℝ)∈closedTilts from ⟨ha.le,le_rfl⟩) hF
    linarith [last_tilt_gap_positive hq.2]

theorem lower_radius_positionEnvelope_positive {t : ℝ} (ht : t∈closedTilts) :
    0<positionEnvelope lowerRadius t := by
  rw [positionEnvelope_eq]
  exact lower_radius_defect_positive (windowMinimizer_mem _ _ _) ht

theorem endpoint_positionEnvelope_positive {q : ℝ}
    (hq : q∈Icc lowerRadius upperRadius) :
    0<positionEnvelope q 0 ∧ 0<positionEnvelope q (Real.arctan (1/5)) := by
  constructor
  · rw [positionEnvelope_eq]
    exact (endpoint_defect_positive hq (windowMinimizer_mem _ _ _)).1
  · rw [positionEnvelope_eq]
    exact (endpoint_defect_positive hq (windowMinimizer_mem _ _ _)).2

theorem upper_radius_positionEnvelope_negative :
    positionEnvelope upperRadius RationalTrial.angle<0 := by
  have hu : RationalTrial.height∈positionWindow := by
    norm_num [RationalTrial.height,positionWindow]
  have hm := windowMinimizer_le upperRadius (Real.cos RationalTrial.angle)
    (Real.sin RationalTrial.angle) hu
  rw [positionEnvelope_eq]
  exact lt_of_le_of_lt hm RationalTrial.defect_negative

end SquaresInCircles.Eight.TableFree.GeometricExistence
