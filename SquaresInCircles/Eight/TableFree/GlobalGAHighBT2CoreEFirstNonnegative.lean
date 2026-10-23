module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2CoreEFirst
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSource

/-!
# E-first, A-second normalization: the doubly nonnegative terminal

Once E is normalized on a genuine original SourceDomain, A can move
without recreating that original domain. The old E's selected DE/EH
normals, H/T normals, all four original sign anchors and the selected
E total remain actual on the new *necessary* cycle. The raw
nonnegative-totals signed stress then excludes both T owners and both
TD2 error signs, including zero.

No step asserts the transported A is an original physical packing.
Uncompiled proof source, not kernel verified.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- On the composed A/E necessary cycle, all original source owners
except G,A continue to be genuinely feasible. -/
private theorem witness_HG :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp
    (ATransport.HG R.A 0) (ATransport.HG R.A 2)

private theorem witness_TD :
    R.A.cycle.Feasible T 0∨R.A.cycle.Feasible T 2 :=
  (original_TD R.E.source).imp
    (ATransport.TD R.A 0) (ATransport.TD R.A 2)

/-- The complete actual high-GA BT2 E-first/A-second nonnegative
totals source has no feasible realization for any TD owner or sign. -/
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
  exact GlobalGA.NonnegativeTotals.NegativeTD.Source.all_TD_false
    R.A.ga R.A.ab (deFlag R.E.source) (ehFlag R.E.source)
    R.A.necessary.sorted R.A.necessary.contained
    (R.A.necessary.core T) hqU hH hG hB hD
    (R.A.variation.trans R.E.source.positive_variation.le) hA he
    (witness_HG R) R.A.GA R.A.AB (R.BT2 hBT)
    (witness_TD R) hDE hEH

end SquaresInCircles.Eight.TableFree.HighGABT2
