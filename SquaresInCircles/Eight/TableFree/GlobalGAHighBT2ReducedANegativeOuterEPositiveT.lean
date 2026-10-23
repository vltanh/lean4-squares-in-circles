module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2ReducedANonnegativeOuterE
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeAShortESource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongESource

/-!
# Negative single flat A primary, positive TD2, outer original E

This is the exact source-level short/long-E scalar partition on the
*necessary* A-transport cycle. The original E is unchanged. Its selected
DE/EH witnesses are reselected only on the genuine original SourceDomain
and remain actual on the moved A cycle. Neither the moved A cycle's
physical gap order nor its original selected normals are assumed.

A flat single-negative A source must also supply its genuine-primary
angle and tangent cut; these are discharged separately by the entry
lemmas or a same-state secondary re-selection. Source-only draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
open GlobalGA.NegativeANormalForm

variable {q : ℝ} {C : SignedCycle}
  (I : GlobalGA.SourceDomain q C) (O : CycleResult q C)

/-- Exclude both possible sizes of the nonnegative selected outer-E
total against the exact negative flat-A error, for every weak HG
owner and both negative-A primary locations. -/
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
    (hcut : (O.cycle.point A).y≤if atG then 39/250 else 1/2)
    (s : ℝ)
    (hs : s∈Icc 0 (GlobalGA.NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : GlobalGA.NegativeAPositiveTD.Source.aError O.cycle atG= -s) :
    False := by
  let S := GlobalGA.OuterE.select I hqU houter
  have hBT' := ATransport.BT2 O hBT
  have hTD' := ATransport.TD O 2 hTD
  have hHG' := reduced_HG I O
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
    by_cases hsmall : GlobalGA.PairedE.cycleTotal O.cycle S.de S.eh≤s
    · exact GlobalGA.NegativeA.ShortE.original atG S.de S.eh
        O.necessary.sorted O.necessary.contained hqU
        hH hG hB hD hvar hs ha hflat hy hcut
        ⟨he,hsmall⟩ hz' hhg hHG hGA hAB hBT' hTD' hDE' hEH'
    · exact GlobalGA.NegativeA.LongE.Source.original atG S.de S.eh
        O.necessary.sorted O.necessary.contained hqU
        hH hG hB hD hvar hs ha hflat hy
        (le_of_lt (lt_of_not_ge hsmall)) hz' hhg hHG hGA hAB
        hBT' hTD' hDE' hEH'
  rcases hHG' with hh|hh
  · exact hfinish 0 (Or.inl rfl) hh
  · exact hfinish 2 (Or.inr rfl) hh

end SquaresInCircles.Eight.TableFree.HighGABT2
