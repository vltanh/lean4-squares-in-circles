module

public import SquaresInCircles.Eight.TableFree.CrossedClampAngleCapture
public import SquaresInCircles.Eight.TableFree.CrossedLowerHardRate
public import SquaresInCircles.Eight.TableFree.CrossedUpperRate

/-!
# Every active common-frame boundary has a strictly favorable cap rate

Uncompiled source draft.  The original H/T budget first forces the
active transverse corner above 48/49.  Its two lower-tangent angle
captures give a rate gap above 1/500; the full upper-tangent theorem
covers the remaining interval.  All cap rates use the actual q, and
the only contact hypotheses are the weak original-source bounds.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace CrossedClampRates

theorem lower_gap_small {q Y r u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (48/49:ℝ) 1) (hr : r∈Icc (0:ℝ) (1/25))
    (hu : u∈Icc (0:ℝ) (3/50)) :
    1/500<angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  have ha := CrossedLowerRate.angular_inverse_small hqL hq hY hr
  have hB : (2-Y)∈Icc (1:ℝ) EndpointRotationPenalty.charge := by
    dsimp [EndpointRotationPenalty.charge]
    constructor <;> linarith [hY.1,hY.2]
  have hb := CrossedLowerRate.angular_hard_small hqL hq hB hu
  linarith

theorem lower_gap_medium {q Y r u : ℝ} (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (1:ℝ) (26/25)) (hr : r∈Icc (0:ℝ) (1/25))
    (hu : u∈Icc (0:ℝ) (79/500)) :
    1/500<angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  have ha := CrossedLowerRate.angular_inverse_medium hqL hq hY hr
  have hB : (2-Y)∈Icc (24/25:ℝ) 1 := by constructor <;> linarith [hY.1,hY.2]
  have hb := CrossedLowerRate.angular_hard_medium hqL hq hB hu
  linarith

end CrossedClampRates

namespace CrossedClampBudget
open CrossedClampRates

theorem BoundaryData.lower_gap {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) (hY : Y≤26/25) :
    1/500<angularHardRate q (2-Y) u-angularInverseRate q Y r := by
  have hfloor := C.Y_gt
  by_cases hY1 : Y≤1
  · exact lower_gap_small C.floor C.ceiling ⟨hfloor.le,hY1⟩ C.r_mem
      ⟨C.u_mem.1,(C.angle_small hY1).le⟩
  · have hYi : Y∈Icc (1:ℝ) (26/25) := ⟨(lt_of_not_ge hY1).le,hY⟩
    exact lower_gap_medium C.floor C.ceiling hYi C.r_mem
      ⟨C.u_mem.1,(C.angle_medium hYi).le⟩

theorem BoundaryData.rate {q Y r u bH bT : ℝ}
    (C : BoundaryData q Y r u bH bT) :
    48/49<Y ∧ angularInverseRate q Y r<angularHardRate q (2-Y) u := by
  refine ⟨C.Y_gt,?_⟩
  by_cases hY : Y≤26/25
  · have hh := C.lower_gap hY
    linarith
  · apply upper_gap_positive C.floor C.ceiling
      ⟨(lt_of_not_ge hY).le,C.Y_mem.2⟩ C.r_mem C.u_mem
    linarith [C.BT,C.T_nonneg]

end CrossedClampBudget

namespace CrossedClampRates

/-- The weak active-boundary interface supplied by the actual inverse
HG cap and the unchanged opposite hard cap.  The original tangents
bH and bT occur only in the original necessary contacts and budget. -/
theorem active_boundary_rate {q Y r u bH bT : ℝ}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hY : Y∈Icc (23/25:ℝ) (Real.sqrt (q-9/4)))
    (hr : r∈Icc (0:ℝ) (1/25)) (hu : u∈Icc 0 frameCap)
    (hT : 0≤bT)
    (hHG : 1/2+(1-transverse q Y)*Real.cos r-(adjacent q Y-1)*Real.sin r≤bH)
    (hBT : bT+1/2≤(radius q (2-Y)-1)*Real.cos u-(2-Y)*Real.sin u)
    (hbudget : bH-bT+EndpointRotationPenalty.charge*(r-u)<1-S0) :
    48/49<Y ∧ angularInverseRate q Y r<angularHardRate q (2-Y) u :=
  CrossedClampBudget.BoundaryData.rate ⟨hqL,hq,hY,hr,hu,hT,hHG,hBT,hbudget⟩

end CrossedClampRates
end SquaresInCircles.Eight.TableFree
