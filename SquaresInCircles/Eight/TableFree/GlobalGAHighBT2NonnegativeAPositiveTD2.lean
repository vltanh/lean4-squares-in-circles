module

public import SquaresInCircles.Eight.TableFree.GlobalGAHighBT2NonpositiveTD2
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Source
public import SquaresInCircles.Eight.TableFree.GlobalGACoreENormalForm
public import SquaresInCircles.Eight.TableFree.GlobalGAOuterESelection

/-!
# BT2 / positive TD2: every E radial kind and sign at nonnegative A total

The scalar leaf proofs for nonnegative E, genuine negative DE3 and
genuine negative EH1 already exist. This module joins their *actual*
seven-source hypotheses after reducing E at the original q. E motion
keeps G,A,B,T, the signed A total, and the positive TD2 error exactly;
the resulting SourceDomain is established by the E-normal-form theorem.
The source's chosen HG, GA, AB, BT and TD witnesses are retained; no
E owner or signed A constituent is assumed by the caller.

Uncompiled source-only transcription; no Lean, CI or tests.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.HighGABT2
open Candidate SignedCycle
variable {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)

include I in
/-- The nonnegative selected E total, for all four E owner pairs. -/
theorem nonnegative_E_positive_TD2_false
    (hqU : q≤qCap) (ga ab de eh : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal C ga ab)
    (he : 0≤GlobalGA.NonnegativeTotals.Source.eTotal C de eh)
    (hz : 0≤delta C.theta T) : False :=
  GlobalGA.NonnegativeTotals.Source.actual_false ga ab de eh
    I.necessary.sorted I.necessary.contained hqU
    I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
    I.positive_variation.le ha hz he (original_HG I)
    hGA hAB hBT hTD hDE hEH

/-- Exactly the three possible normal-form E regimes, all on one
current same-radius SourceDomain. The negative EH case retains the
actual secondary-failure test, not a fabricated E0 witness. -/
theorem reduced_core_positive_TD2_false
    (hqU : q≤qCap) (hEc : (C.point E).Core)
    (hr : GlobalGA.CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (ga ab : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (ha : 0≤GlobalGA.NonnegativeTotals.Source.aTotal C ga ab)
    (hz : 0≤delta C.theta T) : False := by
  rcases hr with he|⟨hflat,hnegative⟩
  · obtain ⟨de,hde⟩ : ∃ de : Bool,
      I.owner D=(if de then 3 else 2) := by
      have h : I.owner D=2∨I.owner D=3 := by
        simpa [GlobalGA.highGAOwners,D] using I.allowed D
      rcases h with h|h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    obtain ⟨eh,heh⟩ : ∃ eh : Bool,
      I.owner E=(if eh then 1 else 0) := by
      have h : I.owner E=0∨I.owner E=1 := by
        simpa [GlobalGA.highGAOwners,E] using I.allowed E
      rcases h with h|h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    have hDE : C.Feasible D (if de then 3 else 2) := by
      simpa [hde] using I.feasible D
    have hEH : C.Feasible E (if eh then 1 else 0) := by
      simpa [heh] using I.feasible E
    have he' : 0≤GlobalGA.NonnegativeTotals.Source.eTotal C de eh := by
      rw [hde,heh,GlobalGA.CoreENegativeTotal.selected_total] at he
      simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
        GlobalGA.PairedE.cycleTotal,GlobalGA.PairedE.total]
        using he
    exact nonnegative_E_positive_TD2_false I hqU ga ab de eh
      hGA hAB hBT hTD hDE hEH ha he' hz
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by
        simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by
        simpa [heh] using I.feasible E
      exact GlobalGA.NegativeDEPositiveTD.Source.actual_false ga ab
        I.necessary.sorted I.necessary.contained hqU
        I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
        I.positive_variation.le ha hz hd.le hflat
        (original_HG I) hGA hAB hBT hTD hDE hEH
    · have hDE : C.Feasible D 2 := by
        simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by
        simpa [heh] using I.feasible E
      by_cases hE0 : C.Feasible E 0
      · have he0 : 0≤GlobalGA.NonnegativeTotals.Source.eTotal C false false := by
          simp [GlobalGA.NonnegativeTotals.Source.eTotal,
            GlobalGA.PairedE.total,GlobalGA.PairedE.selected]
        exact nonnegative_E_positive_TD2_false I hqU ga ab false false
          hGA hAB hBT hTD hDE hE0 ha he0 hz
      · exact GlobalGA.NegativeEHPositiveTD.Source.actual_false ga ab
          I.necessary.sorted I.necessary.contained hqU
          I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
          I.E_nonpos hEc I.positive_variation.le ha hz he hE0
          (original_HG I) hGA hAB hBT hTD hDE hEH

/-- All selected E owners, core/outer kinds, signed primary errors
and mixed-sign A constituents with nonnegative A total. -/
theorem nonnegative_A_positive_TD2_false
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hz : 0≤delta C.theta T)
    (ha : 0≤aTotal I) : False := by
  have hGA : C.Feasible G (if gaFlag I then 3 else 2) := by
    rw [←ga_owner I]
    exact I.feasible G
  have hAB : C.Feasible A (if abFlag I then 2 else 0) := by
    rw [←ab_owner I]
    exact I.feasible A
  have ha' : 0≤GlobalGA.NonnegativeTotals.Source.aTotal C (gaFlag I) (abFlag I) := ha
  rcases I.radial E with houter|hcore
  · let S := GlobalGA.OuterE.select I hqU houter
    have he : 0≤GlobalGA.NonnegativeTotals.Source.eTotal C S.de S.eh := by
      simpa [GlobalGA.NonnegativeTotals.Source.eTotal,
        GlobalGA.PairedE.cycleTotal,GlobalGA.PairedE.total]
        using S.total_nonneg
    exact nonnegative_E_positive_TD2_false I hqU
      (gaFlag I) (abFlag I) S.de S.eh
      hGA hAB hBT hTD S.DE S.EH ha' he hz
  · obtain ⟨O⟩ := GlobalGA.CoreENormalForm.reduce I hqL hqU hcore
    have hGA' := (O.other_feasible G
      (by norm_num [G,D]) (by norm_num [G,E]) _).2 hGA
    have hAB' := (O.other_feasible A
      (by norm_num [A,D]) (by norm_num [A,E]) _).2 hAB
    have hBT' := (O.other_feasible B
      (by norm_num [B,D]) (by norm_num [B,E]) 2).2 hBT
    have hTD' := (O.other_feasible T
      (by norm_num [T,D]) (by norm_num [T,E]) 2).2 hTD
    have hG := O.other_delta G (by norm_num [G,D]) (by norm_num [G,E])
    have hA := O.other_delta A (by norm_num [A,D]) (by norm_num [A,E])
    have hT := O.other_delta T (by norm_num [T,D]) (by norm_num [T,E])
    have ha'' : 0≤GlobalGA.NonnegativeTotals.Source.aTotal O.cycle
        (gaFlag I) (abFlag I) := by
      simpa [GlobalGA.NonnegativeTotals.Source.aTotal,
        GlobalGA.PairedE.total,hG,hA] using ha'
    have hz' : 0≤delta O.cycle.theta T := by
      rw [hT]
      exact hz
    exact reduced_core_positive_TD2_false O.source hqU O.E_core O.reduced
      (gaFlag I) (abFlag I) hGA' hAB' hBT' hTD' ha'' hz'

end SquaresInCircles.Eight.TableFree.HighGABT2
