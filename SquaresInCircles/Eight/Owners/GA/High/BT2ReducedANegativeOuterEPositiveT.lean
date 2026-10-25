module

public import SquaresInCircles.Eight.Owners.GA.High.BT2NegativeANormalForm
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESource
public import SquaresInCircles.Eight.Owners.GA.Negative.AShortESource
public import SquaresInCircles.Eight.Owners.GA.OuterESelection

/-!
# Eight squares: a single negative flat A primary, positive TD2 and an outer E

`reduced_negative_A_outer_E_positive_TD2_false` splits the selected E total against the angle `s`
of the negative A primary, short (`NegativeA.ShortE.original`) or long
(`NegativeA.LongE.original`), on the cycle with A moved. E does not move. Its DE and EH witnesses
are reselected on the source domain (`OuterE.select`) and stay feasible on the cycle with A moved;
neither the gap order of that cycle nor its selected normals are used.

The angle and the tangent cut of the negative A primary are hypotheses here; they come from the
entry lemmas or from a reselection of a secondary at the same state.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

include I in
/-- Both sizes of the nonnegative selected total of an outer E, against the negative error of a
flat A, are excluded, for either weak HG owner and either negative primary of A. -/
theorem reduced_negative_A_outer_E_positive_TD2_false
    (hqU : q≤qCap)
    (houter : (C.point E).Outer q)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hz : 0≤delta C.theta T)
    (atG : Bool)
    (hGA : O.cycle.Feasible G (if atG then 3 else 2))
    (hAB : O.cycle.Feasible A (if atG then 0 else 2))
    (hflat : (O.cycle.point A).a=7/12)
    (hy : 0≤(O.cycle.point A).y)
    (hcut : (O.cycle.point A).y≤ if atG then 39/250 else 1/2)
    (s : ℝ)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError O.cycle atG= -s) :
    False := by
  let S := GlobalGA.OuterE.select I hqU houter
  have hBT' := ATransport.BT2 O hBT
  have hTD' := ATransport.TD O 2 hTD
  have hHG' : O.cycle.Feasible H 0∨O.cycle.Feasible H 2 :=
    (original_HG I).imp (ATransport.HG O 0) (ATransport.HG O 2)
  have hDE' := ATransport.DE O _ S.DE
  have hEH' := ATransport.EH O _ S.EH
  have hH : 0≤(O.cycle.point H).y := by
    rw [ATransport.H_point O]; exact I.H_positive.le
  have hG : (O.cycle.point G).y≤0 := by
    rw [ATransport.G_point O]; exact I.G_negative.le
  have hB : (O.cycle.point B).y≤0 := by
    rw [ATransport.B_point O]; exact I.B_negative.le
  have hD : (O.cycle.point D).y≤0 := by
    rw [ATransport.D_point O]; exact I.D_negative.le
  have hvar : positiveVariation O.cycle.theta≤frameCap :=
    O.variation.trans I.positive_variation.le
  have hz' : 0≤delta O.cycle.theta T := by
    rw [ATransport.original_T_error O]
    exact hz
  have he : 0≤GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh := by
    simpa [GlobalGA.PairedE.cycleTotal,GlobalGA.PairedE.total,
      GlobalGA.PairedE.selected,ATransport.original_D_error O,
      ATransport.original_E_error O] using S.total_nonneg
  have hfinish (hg : Fin 4) (hhg : hg=0∨hg=2)
      (hHG : O.cycle.Feasible H hg) : False := by
    by_cases hsmall : GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh ≤ s
    · exact GlobalGA.NegativeA.ShortE.original atG S.de S.eh
        O.necessary.sorted O.necessary.contained hqU
        hH hG hB hD hvar hs ha hflat hy hcut
        ⟨he,hsmall⟩ hz' hhg hHG hGA hAB hBT' hTD' hDE' hEH'
    · exact GlobalGA.NegativeA.LongE.original atG S.de S.eh
        O.necessary.sorted O.necessary.contained hqU
        hH hG hB hD hvar hs ha hflat hy
        (le_of_lt (lt_of_not_ge hsmall)) hz' hhg hHG hGA hAB
        hBT' hTD' hDE' hEH'
  rcases hHG' with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

end SquaresInCircles.Eight.HighGABT2
