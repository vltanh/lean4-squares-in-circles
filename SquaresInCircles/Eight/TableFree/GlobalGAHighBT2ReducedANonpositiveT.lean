module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NegativeANormalForm
public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NonnegativeAAllT

/-!
# Negative A normalization, nonpositive T: full E original-source exclusion

The A normalization is a necessary-system transport. In particular the
moved A is *not* asserted to be a new original packing, to retain
physical neighbor order, or to possess a newly selected physical normal.
Only the initial original source I is used to select outer E owners.
Raw seven-circle stress lemmas are applied to the moved necessary cycle.

This closes the reduced single-negative-A / nonpositive-T terminal
for both E radial kinds, all selected DE/EH signs and weak ties.
Source-only Lean transcription, not compiled or audited.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C)
  (O : CycleResult q C)

include I in
/-- Every retained non-A source separator is still feasible on O's
same-radius necessary cycle; none is selected hypothetically. -/
private theorem reduced_HG :
    O.cycle.Feasible H 0∨O.cycle.Feasible H 2 :=
  (original_HG I).imp (ATransport.HG O 0) (ATransport.HG O 2)

private theorem reduced_TD :
    O.cycle.Feasible T (if tdFlag I then 2 else 0) := by
  apply ATransport.TD O
  rw [←td_owner I]
  exact I.feasible T

private theorem reduced_DE :
    O.cycle.Feasible D (if deFlag I then 3 else 2) := by
  apply ATransport.DE O
  rw [←de_owner I]
  exact I.feasible D

private theorem reduced_EH :
    O.cycle.Feasible E (if ehFlag I then 1 else 0) := by
  apply ATransport.EH O
  rw [←eh_owner I]
  exact I.feasible E

/-- A transported necessary cycle with both selected A primaries
nonpositive and the actual T primary nonpositive cannot coexist with
BT2. This theorem takes every E regime, including negative E totals.
It does not assume an ordered or radial original copy of moved A. -/
theorem reduced_A_nonpositive_T_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2)
    (hga : O.ga=true→delta O.cycle.theta G≤0)
    (hab : O.ab=true→delta O.cycle.theta A≤0)
    (htd : tdFlag I=true→delta C.theta T≤0) : False := by
  have hBT' := ATransport.BT2 O hBT
  have hTD' := reduced_TD I O
  have hHG' := reduced_HG I O
  have hT : tdFlag I=true→delta O.cycle.theta T≤0 := by
    intro ht
    rw [ATransport.original_T_error O]
    exact htd ht
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
  have hv : positiveVariation O.cycle.theta≤frameCap :=
    O.variation.trans I.positive_variation.le
  rcases I.radial E with houter|hcore
  · -- E's secondaries are selected on the unchanged *original* E/D/H.
    let S := GlobalGA.OuterE.select I hqU houter
    have hDE := ATransport.DE O _ S.DE
    have hEH := ATransport.EH O _ S.EH
    have he : 0≤GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh := by
      simpa [GlobalGA.PairedE.cycleTotal,GlobalGA.PairedE.total,
        GlobalGA.PairedE.selected,ATransport.original_D_error O,
        ATransport.original_E_error O] using S.total_nonneg
    exact GlobalGA.PairedE.Negative.actual_false
      O.ga O.ab (tdFlag I) S.de S.eh
      O.necessary.sorted O.necessary.contained O.necessary.core hqU
      hH hG hB hD hv hHG' O.GA O.AB hBT' hTD' hDE hEH
      hga hab hT he
  · -- The true-core E negative-total reduction itself requires no
    -- original ordering after moving A: use its raw seven-circle lemma.
    have hEc : (O.cycle.point E).Core := by
      rw [ATransport.E_point O]
      exact hcore
    have hEy : (O.cycle.point E).y≤0 := by
      rw [ATransport.E_point O]
      exact I.E_nonpos
    have hHo : (O.cycle.point H).Outer q := by
      rw [ATransport.H_point O]
      exact I.outer H (by simp)
    have hDo : (O.cycle.point D).Outer q := by
      rw [ATransport.D_point O]
      exact I.outer D (by simp)
    exact GlobalGA.CoreENegativeTotal.actual_false
      O.ga O.ab (tdFlag I) (deFlag I) (ehFlag I)
      O.necessary hqL hqU hH hG hB hD hHo hDo hEy hEc
      hv hHG' O.GA O.AB hBT' hTD' (reduced_DE I O) (reduced_EH I O)
      hga hab hT

/-- The two *negative* branches of the A normal form have exactly one
negative selected primary. The positivity/flat bounds are retained in
O.reduced but are not needed by the nonpositive-T stress. -/
theorem negative_reduced_A_nonpositive_T_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2)
    (htd : tdFlag I=true→delta C.theta T≤0)
    (hnegative : ¬ 0≤
      GlobalGA.NegativeANormalForm.total O.ga O.ab
        (delta O.cycle.theta G) (delta O.cycle.theta A)) : False := by
  rcases O.reduced with hnonneg|⟨hg,ha,hflat,hy,hu⟩|⟨hg,ha,hflat,hy,hv⟩
  · exact hnegative hnonneg
  · exact reduced_A_nonpositive_T_false I O hqL hqU hBT
      (by intro _; simpa [hg] using hu.2.le)
      (by intro hab; cases ha.symm.trans hab)
      htd
  · exact reduced_A_nonpositive_T_false I O hqL hqU hBT
      (by intro hga; cases hg.symm.trans hga)
      (by intro _; simpa [ha] using hv.2.le)
      htd

end SquaresInCircles.Eight.TableFree.HighGABT2
