module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2CoreEFirstNonnegative
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Source

/-!
# E-first/A-second: nonnegative A and positive TD2, all E normal forms

The true-core E normal form has exactly three alternatives at the same
radius: E total nonnegative, negative DE3/EH0, or negative EH1/DE2.
The last alternative must first check actual EH0 on the *current
necessary cycle*: if it is feasible, select secondary E0 without
moving the point; otherwise the genuine EH1 stress uses the original
short-angle entry inequality. Both choices keep the original H/D
anchors, BT2 and TD2 with the same signed T error.

No ordering or source-reconstruction is assumed after moving A.
Lean draft only, without compilation/CI.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm
variable {q : ℝ} {C : SignedCycle} {I : GlobalGA.SourceDomain q C}
  (R : CoreEFirstResult I)

/-- The necessary A transport retains all original five anchors other
than A, with exactly the original signs and variation budget. -/
private theorem anchor_signs :
    0≤(R.A.cycle.point H).y ∧
      (R.A.cycle.point G).y≤0 ∧
      (R.A.cycle.point B).y≤0 ∧
      (R.A.cycle.point D).y≤0 := by
  constructor
  · rw [ATransport.H_point R.A]
    exact R.E.source.H_positive.le
  constructor
  · rw [ATransport.G_point R.A]
    exact R.E.source.G_negative.le
  constructor
  · rw [ATransport.B_point R.A]
    exact R.E.source.B_negative.le
  · rw [ATransport.D_point R.A]
    exact R.E.source.D_negative.le

private theorem hg :
    R.A.cycle.Feasible H 0∨R.A.cycle.Feasible H 2 :=
  (original_HG R.E.source).imp (ATransport.HG R.A 0) (ATransport.HG R.A 2)

private theorem budget :
    positiveVariation R.A.cycle.theta≤frameCap :=
  R.A.variation.trans R.E.source.positive_variation.le

/-- A raw signed-circle theorem handles any *actually feasible* choice
of DE2 and EH0, not necessarily the originally selected E pair. -/
theorem positive_TD2_secondary_E_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab)
    (hDE : R.A.cycle.Feasible D 2)
    (hEH : R.A.cycle.Feasible E 0) : False := by
  obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
  have he : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle false false := by
    simp [GlobalGA.NonnegativeTotals.Source.eTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected]
  exact GlobalGA.NonnegativeTotals.Source.actual_false
    R.A.ga R.A.ab false false
    R.A.necessary.sorted R.A.necessary.contained hqU
    hH hG hB hD (budget R) ha hz he
    (hg R) R.A.GA R.A.AB (R.BT2 hBT) (R.TD 2 hTD) hDE hEH

/-- The whole nonnegative-A, nonnegative-TD2 part of the E-first
true-core source, including arbitrary selected signs on D and E. -/
theorem nonnegative_A_positive_TD2_all_E_false
    (hqU : q≤qCap) (hBT : R.E.cycle.Feasible B 2)
    (hTD : R.E.cycle.Feasible T 2)
    (hz : 0≤delta R.A.cycle.theta T)
    (ha : 0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A)) : False := by
  have ha' : 0≤GlobalGA.NonnegativeTotals.Source.aTotal
      R.A.cycle R.A.ga R.A.ab := by
    simpa [GlobalGA.NegativeANormalForm.total,
      GlobalGA.NonnegativeTotals.Source.aTotal,
      GlobalGA.PairedE.total,GlobalGA.PairedE.selected] using ha
  rcases R.E_reduced with he|⟨hflat,hcase⟩
  · have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal R.A.cycle
        (deFlag R.E.source) (ehFlag R.E.source) := by
      simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
        GlobalGA.PairedE.total,GlobalGA.CoreENegativeTotal.selected_total,
        GlobalGA.PairedE.cycleTotal,de_owner R.E.source,eh_owner R.E.source]
        using he
    exact reduced_nonnegative_AE_false R hqU hBT ha he'
  · obtain ⟨hH,hG,hB,hD⟩ := anchor_signs R
    rcases hcase with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : R.A.cycle.Feasible D 3 := by
        simpa [hde] using R.DE
      have hEH : R.A.cycle.Feasible E 0 := by
        simpa [heh] using R.EH
      exact GlobalGA.NegativeDEPositiveTD.Source.actual_false
        R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
        hqU hH hG hB hD (budget R) ha' hz hd.le hflat
        (hg R) R.A.GA R.A.AB (R.BT2 hBT) (R.TD 2 hTD) hDE hEH
    · have hDE : R.A.cycle.Feasible D 2 := by
        simpa [hde] using R.DE
      have hEH : R.A.cycle.Feasible E 1 := by
        simpa [heh] using R.EH
      by_cases hE0 : R.A.cycle.Feasible E 0
      · exact positive_TD2_secondary_E_false R hqU hBT hTD hz ha' hDE hE0
      · have hEy : (R.A.cycle.point E).y≤0 := by
          rw [R.E_point]
          exact R.E.source.E_nonpos
        exact GlobalGA.NegativeEHPositiveTD.Source.actual_false
          R.A.ga R.A.ab R.A.necessary.sorted R.A.necessary.contained
          hqU hH hG hB hD hEy R.E_core (budget R)
          ha' hz he hE0 (hg R) R.A.GA R.A.AB
          (R.BT2 hBT) (R.TD 2 hTD) hDE hEH

end SquaresInCircles.Eight.TableFree.HighGABT2
