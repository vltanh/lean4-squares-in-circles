module

public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirst
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDSource

/-!
# Eight squares: normalizing E first and A second, with nonnegative A and E totals

Once E is normalized on a source domain, A moves, and the moved cycle need not be a source domain.
The selected DE and EH normals of E, the HG and TD normals, the four sign anchors of H, G, B and D
and the selected E total carry over to the moved cycle, which satisfies the necessary conditions.
The signed stress of nonnegative totals `NonnegativeTotals.all_TD_false` then excludes both T
owners and both signs of the TD2 error, zero included (`reduced_nonnegative_AE_false`). The cycle
with A moved is used only as a signed cycle, not as a packing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- On the cycle with E then A moved, the owners of the source domain on the edges other than GA
and AB stay feasible. -/
private theorem witness_HG :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp
    (ATransport.HG R.A 0) (ATransport.HG R.A 2)

private theorem witness_TD :
    R.A.cycle.Feasible T 0∨R.A.cycle.Feasible T 2 :=
  (original_TD R.E.source).imp
    (ATransport.TD R.A 0) (ATransport.TD R.A 2)

/-- With E then A normalized, nonnegative selected A and E totals and a BT2 witness are impossible,
for both TD owners and every sign of the T error. -/
theorem reduced_nonnegative_AE_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (ha : 0≤GlobalGA.NegativeANormalForm.total R.A.ga R.A.ab
      (delta R.A.cycle.theta G) (delta R.A.cycle.theta A))
    (he : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle
      (deFlag R.E.source) (ehFlag R.E.source)) : False := by
  have hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal R.A.cycle
      R.A.ga R.A.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,GlobalGA.PairedE.total,
      GlobalGA.PairedE.selected] using ha
  have hDE : R.A.cycle.Feasible D (if deFlag R.E.source then 3 else 2) := by
    rw [←de_owner R.E.source]
    exact R.DE
  have hEH : R.A.cycle.Feasible E (if ehFlag R.E.source then 1 else 0) := by
    rw [←eh_owner R.E.source]
    exact R.EH
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
    R.A.ga R.A.ab (deFlag R.E.source) (ehFlag R.E.source)
    R.A.necessary.sorted R.A.necessary.contained
    (R.A.necessary.core T) hqU hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le) hA he
    (witness_HG R) R.A.GA R.A.AB (R.BT2 hBT)
    (witness_TD R) hDE hEH

end SquaresInCircles.Eight.HighGABT2
