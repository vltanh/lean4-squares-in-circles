module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2ReducedANonpositiveT

/-!
# Transported-A nonnegative selected total, actual outer E

After moving A, the result is a necessary seven-circle cycle, not
necessarily an ordered original packing. This exclusion deliberately
uses the raw nonnegative-A/E signed-stress lemma rather than building a
fictitious SourceDomain on the moved A cycle. E remains literally the
original outer E; its weak owner reselection occurs on original I, at
the unchanged q, and its true projections carry over to the new cycle.

Both actual T owners and every signed TD2 error are included.
No kernel compilation or CI was run.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

include I in
/-- Moving A cannot invalidate the outer-E selection, signed E total,
the original BT2 witness, or either actual TD owner. -/
theorem reduced_nonnegative_A_outer_E_false
    (hqU : q≤qCap) (hBT : C.Feasible B 2)
    (houter : (C.point E).Outer q)
    (ha : 0≤GlobalGA.NegativeANormalForm.total O.ga O.ab
      (delta O.cycle.theta G) (delta O.cycle.theta A)) : False := by
  let S := GlobalGA.OuterE.select I hqU houter
  have hBT' := ATransport.BT2 O hBT
  have hHG' : O.cycle.Feasible H 0∨O.cycle.Feasible H 2 :=
    (original_HG I).imp (ATransport.HG O 0) (ATransport.HG O 2)
  have hTD' : O.cycle.Feasible T 0∨O.cycle.Feasible T 2 :=
    (original_TD I).imp (ATransport.TD O 0) (ATransport.TD O 2)
  have hDE' := ATransport.DE O _ S.DE
  have hEH' := ATransport.EH O _ S.EH
  have hA : 0≤GlobalGA.NonnegativeTotals.Source.aTotal O.cycle O.ga O.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected] using ha
  have hE : 0≤GlobalGA.NonnegativeTotals.Source.eTotal O.cycle S.de S.eh := by
    simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.cycleTotal,
      ATransport.original_D_error O,ATransport.original_E_error O]
      using S.total_nonneg
  have hH : 0≤(O.cycle.point H).y := by
    rw [ATransport.H_point O]
    exact I.H_positive.le
  have hG : (O.cycle.point G).y≤0 := by
    rw [ATransport.G_point O]
    exact I.G_negative.le
  have hB : (O.cycle.point B).y≤0 := by
    rw [ATransport.B_point O]
    exact I.B_negative.le
  have hD : (O.cycle.point D).y≤0 := by
    rw [ATransport.D_point O]
    exact I.D_negative.le
  exact GlobalGA.NonnegativeTotals.all_TD_false
    O.ga O.ab S.de S.eh O.necessary.sorted O.necessary.contained
    (O.necessary.core T) hqU hH hG hB hD
    (O.variation.trans I.positive_variation.le) hA hE hHG'
    O.GA O.AB hBT' hTD' hDE' hEH'

end SquaresInCircles.Eight.TableFree.HighGABT2
