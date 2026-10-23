module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAStress
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELowASource
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDSource

/-!
# Every original E owner with nonnegative A and nonpositive TD2

Uncompiled source completion of
`HAND_G3_CORE_E_NONNEGATIVE_A_NONPOSITIVE_TD2_EXCLUSION.md`.

The original E normal form leaves all A/T geometry, errors and selected
witnesses fixed. Its nonnegative-total endpoint uses the completed
nonnegative A/E theorem. Its single negative DE or genuine negative EH
endpoint uses the exact fixed-family stress. Outer E is handled by
proved same-state owner selection. No scalar or endpoint premise is
left at this source entry.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeENonpositiveTD
open Candidate SignedCycle PairedE

theorem a_total_bounds {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (ga ab : Bool) (ha : 0≤LowA.aTotal C ga ab) :
    LowA.aTotal C ga ab∈Icc 0 frameCap := by
  have hb := original_pair_budgets (i:=G) (j:=A)
    I.positive_variation.le I.negative_variation.le (by norm_num [G,A])
  exact total_bounds ga ab hb.1 hb.2 ha

theorem nonnegative_e_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (ga ab de eh : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : 0≤LowA.aTotal C ga ab) (he : 0≤cycleTotal C de eh)
    (ht : delta C.theta T≤0) : False := by
  have hn := I.necessary
  exact NonnegativeTotals.NegativeTD.Source.actual_false ga ab de eh
    hn.sorted hn.contained (hn.core T) hq I.H_positive.le I.G_negative.le
    I.B_negative.le I.D_negative.le I.positive_variation.le ha he ht
    (NegativeELowA.original_HG I) hGA hAB hBT hTD hDE hEH

theorem reduced_core_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hEc : (C.point E).Core)
    (hr : CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (ga ab : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (ha : LowA.aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (ht : delta C.theta T≤0) : False := by
  have hn := I.necessary
  have ha0 : 0≤LowA.aTotal C ga ab := by linarith [ha.1]
  have hHG := NegativeELowA.original_HG I
  rcases hr with hnonneg|⟨hflat,hnegative⟩
  · obtain ⟨de,hde⟩ : ∃de : Bool,I.owner D=(if de then 3 else 2) := by
      have ho : I.owner D=2∨I.owner D=3 := by simpa [highGAOwners,D] using I.allowed D
      rcases ho with ho|ho
      · exact ⟨false,ho⟩
      · exact ⟨true,ho⟩
    obtain ⟨eh,heh⟩ : ∃eh : Bool,I.owner E=(if eh then 1 else 0) := by
      have ho : I.owner E=0∨I.owner E=1 := by simpa [highGAOwners,E] using I.allowed E
      rcases ho with ho|ho
      · exact ⟨false,ho⟩
      · exact ⟨true,ho⟩
    have hDE : C.Feasible D (if de then 3 else 2) := by simpa [hde] using I.feasible D
    have hEH : C.Feasible E (if eh then 1 else 0) := by simpa [heh] using I.feasible E
    have he : 0≤cycleTotal C de eh := by
      rw [hde,heh,CoreENegativeTotal.selected_total] at hnonneg
      exact hnonneg
    exact nonnegative_e_false I hq ga ab de eh hGA hAB hBT hTD hDE hEH ha0 he ht
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by simpa [heh] using I.feasible E
      exact NegativeELargeA.Source.actual_false ga ab true false hn.sorted hn.contained
        (hn.core T) hq I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
        hflat I.positive_variation.le hHG hGA hAB hBT hTD hDE hEH ha ht
        (fun _ => hd.le) (by intro h; cases h)
    · have hDE : C.Feasible D 2 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      by_cases hEH0 : C.Feasible E 0
      · exact nonnegative_e_false I hq ga ab false false hGA hAB hBT hTD hDE hEH0
          ha0 (by simp [cycleTotal,total,selected]) ht
      · have hnE : -delta C.theta E∈Ioc 0 frameCap :=
          ⟨neg_pos.mpr he,(neg_le_abs _).trans (hn.spread (next E) E)⟩
        have hlocal : quarterFeasible (C.point E) (C.point H) (-(-delta C.theta E)) 1 := by
          simpa [Feasible,slack,edge,word,next,E,H,quarterFeasible,sub_nonneg] using hEH
        have hnot : ¬quarterFeasible (C.point E) (C.point H) (-(-delta C.theta E)) 0 := by
          intro hh
          apply hEH0
          simpa [Feasible,slack,edge,word,next,E,H,quarterFeasible,sub_nonneg] using hh
        have hcut := NegativeCoreE.genuine_negative_flat (hn.sorted E) I.E_nonpos hEc
          (hn.sorted H) I.H_positive.le (hn.contained H) hq hnE hlocal hnot
        exact NegativeELargeA.Source.actual_false ga ab false true hn.sorted hn.contained
          (hn.core T) hq I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
          hflat I.positive_variation.le hHG hGA hAB hBT hTD hDE hEH ha ht
          (by intro h; cases h) (fun _ => ⟨⟨hnE.1.le,hcut.2.2.le⟩,hcut.2.1.le⟩)

theorem core_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hEc : (C.point E).Core)
    (ga ab : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (ha : LowA.aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (ht : delta C.theta T≤0) : False := by
  obtain ⟨O⟩ := CoreENormalForm.reduce I hqL hqU hEc
  have hGA' := (O.other_feasible G (by norm_num [G,D]) (by norm_num [G,E]) _).2 hGA
  have hAB' := (O.other_feasible A (by norm_num [A,D]) (by norm_num [A,E]) _).2 hAB
  have hBT' := (O.other_feasible B (by norm_num [B,D]) (by norm_num [B,E]) 2).2 hBT
  have hTD' := (O.other_feasible T (by norm_num [T,D]) (by norm_num [T,E]) 2).2 hTD
  have hG := O.other_delta G (by norm_num [G,D]) (by norm_num [G,E])
  have hA := O.other_delta A (by norm_num [A,D]) (by norm_num [A,E])
  have hT := O.other_delta T (by norm_num [T,D]) (by norm_num [T,E])
  have ha' : LowA.aTotal O.cycle ga ab∈Icc (1/6:ℝ) frameCap := by
    simpa [LowA.aTotal,hG,hA] using ha
  have ht' : delta O.cycle.theta T≤0 := by rw [hT]; exact ht
  exact reduced_core_false O.source hqU O.E_core O.reduced ga ab hGA' hAB' hBT' hTD' ha' ht'

/-- Every E owner, every E-primary total, and both true E radial kinds
are covered. The sole retained T assumption is its actual nonpositive
TD2 witness, and A is specified only by its nonnegative selected total. -/
theorem source_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (ga ab : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (ha : 0≤LowA.aTotal C ga ab) (ht : delta C.theta T≤0) : False := by
  by_cases hlow : LowA.aTotal C ga ab≤1/6
  · exact NegativeELowA.source_false I hqL hqU ga ab true hGA hAB hBT hTD
      ⟨ha,hlow⟩ (fun _ => ht)
  · have ha' : LowA.aTotal C ga ab∈Icc (1/6:ℝ) frameCap :=
      ⟨(lt_of_not_ge hlow).le,(a_total_bounds I ga ab ha).2⟩
    rcases I.radial E with houter|hcore
    · let S := OuterE.select I hqU houter
      exact nonnegative_e_false I hqU ga ab S.de S.eh hGA hAB hBT hTD
        S.DE S.EH ha S.total_nonneg ht
    · exact core_false I hqL hqU hcore ga ab hGA hAB hBT hTD ha' ht

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeENonpositiveTD
