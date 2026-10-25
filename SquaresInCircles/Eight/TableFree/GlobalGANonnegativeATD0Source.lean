module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD0Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD0Source
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeENonpositiveTDSource
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsTD0Source

/-!
# All E owners at original BT2/TD0 with nonnegative signed A total

The low A interval is already excluded for both E kinds and all E
owners. At high A, outer E selects its actual nonnegative-total witnesses.
Core E is normalized by an E-only original-radius transport to either
nonnegative total or one negative E primary. The genuine EH1 and DE3
branches use the two new zero-tilt original-source comparisons.

No physical T, A, B or D point, frame or selected primary is changed
by the core-E normalization, and the original TD0 error is unrestricted.
This completes the nonnegative-A/TD0 finite owner matrix as an
UNCOMPILED formalization draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeATD0
open Candidate SignedCycle

theorem nonnegative_e_false {q : ℝ} {C : SignedCycle}
    (I : SourceDomain q C) (hq : q≤qCap)
    (ga ab de eh : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : 0≤PairedE.LowA.aTotal C ga ab)
    (he : 0≤PairedE.cycleTotal C de eh) : False := by
  have hHG := NegativeELowA.original_HG I
  have heq : NonnegativeTotals.Source.eTotal C de eh=
      PairedE.cycleTotal C de eh := rfl
  exact NonnegativeTotals.TD0.actual_false ga ab de eh
    I.necessary.sorted I.necessary.contained (I.necessary.core T) hq
    I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
    I.positive_variation.le ha (by rw [heq]; exact he)
    hHG hGA hAB hBT hTD hDE hEH

/-- Exhaust the three actual core-E normal forms. -/
theorem reduced_core_high_false {q : ℝ} {C : SignedCycle}
    (I : SourceDomain q C) (hq : q≤qCap)
    (hcore : (C.point E).Core)
    (hr : CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (ga ab : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (ha : PairedE.LowA.aTotal C ga ab∈Icc (1/6:ℝ) frameCap) : False := by
  let hn := I.necessary
  have hHG := NegativeELowA.original_HG I
  have ha0 : 0≤PairedE.LowA.aTotal C ga ab := by linarith [ha.1]
  rcases hr with hnonneg|⟨hflat,hnegative⟩
  · obtain ⟨de,hde⟩ : ∃de : Bool,I.owner D=(if de then 3 else 2) := by
      have hd : I.owner D=2∨I.owner D=3 := by
        simpa [highGAOwners,D] using I.allowed D
      rcases hd with hd|hd
      · exact ⟨false,hd⟩
      · exact ⟨true,hd⟩
    obtain ⟨eh,heh⟩ : ∃eh : Bool,I.owner E=(if eh then 1 else 0) := by
      have he : I.owner E=0∨I.owner E=1 := by
        simpa [highGAOwners,E] using I.allowed E
      rcases he with he|he
      · exact ⟨false,he⟩
      · exact ⟨true,he⟩
    have hDE : C.Feasible D (if de then 3 else 2) := by simpa [hde] using I.feasible D
    have hEH : C.Feasible E (if eh then 1 else 0) := by simpa [heh] using I.feasible E
    have he : 0≤PairedE.cycleTotal C de eh := by
      rw [hde,heh,CoreENegativeTotal.selected_total] at hnonneg
      exact hnonneg
    exact nonnegative_e_false I hq ga ab de eh hGA hAB hBT hTD hDE hEH ha0 he
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by simpa [heh] using I.feasible E
      exact NegativeDETD0.original_high_false ga ab hn.sorted hn.contained hq
        I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
        I.E_nonpos hcore I.positive_variation.le ha hd.le hHG
        hGA hAB hBT hTD hDE hEH
    · have hDE : C.Feasible D 2 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      by_cases hEH0 : C.Feasible E 0
      · exact nonnegative_e_false I hq ga ab false false hGA hAB hBT hTD hDE
          hEH0 ha0 (by simp [PairedE.cycleTotal,PairedE.total,PairedE.selected])
      · exact NegativeEHTD0.original_high_false ga ab hn.sorted hn.contained hq
          I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
          I.E_nonpos hcore I.positive_variation.le ha he hEH0
          hHG hGA hAB hBT hTD hDE hEH

/-- Original BT2/TD0, every E owner and sign, both E kinds,
arbitrary sign of the actual B and T errors, and every A pair. -/
theorem source_false {q : ℝ} {C : SignedCycle}
    (I : SourceDomain q C) (hqL : qLow≤q) (hqU : q≤qCap)
    (ga ab : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (ha : 0≤PairedE.LowA.aTotal C ga ab) : False := by
  by_cases hlow : PairedE.LowA.aTotal C ga ab≤1/6
  · exact NegativeELowA.source_false I hqL hqU ga ab false hGA hAB hBT hTD
      ⟨ha,hlow⟩ (by intro h; cases h)
  · have ha' : PairedE.LowA.aTotal C ga ab∈Icc (1/6:ℝ) frameCap :=
      ⟨(lt_of_not_ge hlow).le,
        (NegativeENonpositiveTD.a_total_bounds I ga ab ha).2⟩
    rcases I.radial E with houter|hcore
    · let S := OuterE.select I hqU houter
      exact nonnegative_e_false I hqU ga ab S.de S.eh hGA hAB hBT hTD
        S.DE S.EH ha S.total_nonneg
    · obtain ⟨O⟩ := CoreENormalForm.reduce I hqL hqU hcore
      have hGA' := (O.other_feasible G
        (by norm_num [G,D]) (by norm_num [G,E]) _).2 hGA
      have hAB' := (O.other_feasible A
        (by norm_num [A,D]) (by norm_num [A,E]) _).2 hAB
      have hBT' := (O.other_feasible B
        (by norm_num [B,D]) (by norm_num [B,E]) 2).2 hBT
      have hTD' := (O.other_feasible T
        (by norm_num [T,D]) (by norm_num [T,E]) 0).2 hTD
      have hG := O.other_delta G (by norm_num [G,D]) (by norm_num [G,E])
      have hA := O.other_delta A (by norm_num [A,D]) (by norm_num [A,E])
      have ha'' : PairedE.LowA.aTotal O.cycle ga ab∈Icc (1/6:ℝ) frameCap := by
        simpa [PairedE.LowA.aTotal,hG,hA] using ha'
      exact reduced_core_high_false O.source hqU O.E_core O.reduced
        ga ab hGA' hAB' hBT' hTD' ha''

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeATD0
