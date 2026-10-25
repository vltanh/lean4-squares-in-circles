module

public import SquaresInCircles.Eight.Owners.BT.HighPrimarySupport

/-!
# Eight squares: complete negative-BT1 transport on the restricted original T disk

The explicit split covers the whole necessary-cap domain.  The
comparison retains arbitrary fixed TD force angle and every
multiplier at least three fifths.  No numerical minimizer, residual
derivative hypothesis or asserted feasible aligned state is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.HighPrimary

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem circle_transport {a b c eta z : ℝ}
    (hcirc : (a+1/2)^2+(b+1/2)^2≤Q0) (ha : a≤283/200)
    (hprimary : X z≤a+1/2) (hc : (3/5:ℝ)≤c)
    (heta : eta∈Icc 0 frameCap) (hz : OnCap z) :
    aligned c eta≤charge c eta z a b := by
  by_cases hsmall : z≤1/8
  · exact small_lower hcirc ha ⟨hz.1.1,hsmall⟩ c eta
  · have hlarge : (1/8:ℝ)≤z := by linarith
    have hstart : OnCap (1/8) := cap_down hz ⟨by norm_num,hlarge⟩
    have hstartCircle : (X (1/8)-1/2+1/2)^2+(Z (1/8)-1/2+1/2)^2≤Q0 := by
      nlinarith only [Z_sq hstart]
    have hstartPrimary : X (1/8)-1/2≤283/200 := by
      linarith [cap_X_upper hstart]
    have hbase := small_lower hstartCircle hstartPrimary
      (show (1/8:ℝ)∈Icc 0 (1/8:ℝ) by norm_num) c eta
    rw [boundary_identity hstart.1] at hbase
    have hmono := boundary_monotone hc heta hz hlarge
      ⟨le_rfl,hlarge⟩ ⟨hlarge,le_rfl⟩ hlarge
    have hsupport := restricted_support hcirc hprimary hc heta hz hlarge
    have hlast : boundary c eta z≤charge c eta z a b := by
      rw [← boundary_identity hz.1]
      dsimp [charge]
      linarith only [hsupport]
    exact hbase.trans (hmono.trans hlast)

/-- The actual necessary prefix supplies every domain hypothesis of
the full transport theorem. -/
theorem state_transport (a t : State) {c eta z : ℝ}
    (hc : (3/5:ℝ)≤c) (heta : eta∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hpref : «prefix» z≤a.b+t.a/Real.cos z) :
    aligned c eta≤charge c eta z t.a t.b := by
  obtain ⟨hprimary,hcap⟩ := cap_of_prefix a t hz hpref
  exact circle_transport (state_circle t) (ZeroPrimary.coordinates t).2.1.le
    hprimary hc heta hcap

end SquaresInCircles.Eight.GlobalBT.HighPrimary
