module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirst
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDSource

/-!
# Eight squares: a core E with both secondary owners at the same state

If DE2 and EH0 are feasible on the cycle with E then A moved, E is reselected on them at the same
state, without moving. The selected E charge is then zero, and with a nonnegative selected A total
the stress `NonnegativeTotals.all_TD_false` excludes the cycle for every T owner and every T error
(`nonnegative_A_secondary_E_all_T_false`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

theorem nonnegative_A_secondary_E_all_T_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hDE : R.A.cycle.Feasible D 2)
    (hEH : R.A.cycle.Feasible E 0) : False := by
  have hE : 0≤GlobalGA.NonnegativeTotals.Source.eTotal
      R.A.cycle false false := by
    simp [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected]
  have hHG : R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
    (original_HG R.E.source).imp
      (ATransport.HG R.A 0) (ATransport.HG R.A 2)
  have hTD : R.A.cycle.Feasible T 0∨R.A.cycle.Feasible T 2 :=
    (original_TD R.E.source).imp
      (ATransport.TD R.A 0) (ATransport.TD R.A 2)
  have hH : 0≤(R.A.cycle.point H).y := by
    rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  have hG : (R.A.cycle.point G).y≤0 := by
    rw [ATransport.G_point R.A]
    exact R.E.source.G_negative.le
  have hB : (R.A.cycle.point B).y≤0 := by
    rw [ATransport.B_point R.A]
    exact R.E.source.B_negative.le
  have hD : (R.A.cycle.point D).y≤0 := by
    rw [ATransport.D_point R.A]
    exact R.E.source.D_negative.le
  exact GlobalGA.NonnegativeTotals.all_TD_false
    R.A.ga R.A.ab false false
    R.A.necessary.sorted R.A.necessary.contained
    (R.A.necessary.core T) hqU hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le)
    ha hE hHG R.A.GA R.A.AB (R.BT2 hBT) hTD hDE hEH

end SquaresInCircles.Eight.HighGABT2
