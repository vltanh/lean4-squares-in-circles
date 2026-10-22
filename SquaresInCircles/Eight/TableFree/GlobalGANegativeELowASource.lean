module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELowAStress
public import SquaresInCircles.Eight.TableFree.GlobalGACoreENormalForm
public import SquaresInCircles.Eight.TableFree.GlobalGAOuterESelection

/-!
# All original E owners at small nonnegative A total

Uncompiled completion of Section 5 of
`HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md`.

Outer E uses same-state actual secondary reselection. True-core E uses
the complete E-only normal form, including both mixed-sign transports
and the paired-negative intrinsic endpoint. The resulting single
negative EH1 either has an actual EH0 already, or its proved genuine-EH
cut supplies the short secant domain. Every A and T point, error, and
selected witness is retained through this source dispatch.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELowA
open Candidate SignedCycle PairedE

theorem original_HG {q : ℝ} {C : SignedCycle} (I : SourceDomain q C) :
    C.Feasible H 0∨C.Feasible H 2 := by
  have ho : I.owner H=0∨I.owner H=2 := by simpa [highGAOwners,H] using I.allowed H
  rcases ho with ho|ho
  · exact Or.inl (by simpa [ho] using I.feasible H)
  · exact Or.inr (by simpa [ho] using I.feasible H)

theorem reduced_core_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hq : q≤qCap) (hEc : (C.point E).Core)
    (hr : CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (ga ab td : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (ha : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0) : False := by
  have hn := I.necessary
  have hHG := original_HG I
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
    exact LowA.actual_false ga ab td de eh hn.sorted hn.contained (hn.core T) hq
      I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
      I.positive_variation.le hHG hGA hAB hBT hTD hDE hEH ha htd he
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by simpa [heh] using I.feasible E
      exact actual_false ga ab td true false hn.sorted hn.contained (hn.core T) hq
        I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le hflat
        I.positive_variation.le hHG hGA hAB hBT hTD hDE hEH ha htd
        (fun _ => hd.le) (by intro h; cases h)
    · have hDE : C.Feasible D 2 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      by_cases hEH0 : C.Feasible E 0
      · exact LowA.actual_false ga ab td false false hn.sorted hn.contained (hn.core T) hq
          I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
          I.positive_variation.le hHG hGA hAB hBT hTD hDE hEH0 ha htd
          (by simp [cycleTotal,total,selected])
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
        exact actual_false ga ab td false true hn.sorted hn.contained (hn.core T) hq
          I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le hflat
          I.positive_variation.le hHG hGA hAB hBT hTD hDE hEH ha htd
          (by intro h; cases h) (fun _ => ⟨hnE.1.le,hcut.2.2.le⟩)

/-- The E-only normalization leaves every actual datum used by the
small-A/TD premise literally unchanged. -/
theorem core_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hEc : (C.point E).Core)
    (ga ab td : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (ha : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0) : False := by
  obtain ⟨O⟩ := CoreENormalForm.reduce I hqL hqU hEc
  have hGA' := (O.other_feasible G (by norm_num [G,D]) (by norm_num [G,E]) _).2 hGA
  have hAB' := (O.other_feasible A (by norm_num [A,D]) (by norm_num [A,E]) _).2 hAB
  have hBT' := (O.other_feasible B (by norm_num [B,D]) (by norm_num [B,E]) 2).2 hBT
  have hTD' := (O.other_feasible T (by norm_num [T,D]) (by norm_num [T,E]) _).2 hTD
  have hG := O.other_delta G (by norm_num [G,D]) (by norm_num [G,E])
  have hA := O.other_delta A (by norm_num [A,D]) (by norm_num [A,E])
  have hT := O.other_delta T (by norm_num [T,D]) (by norm_num [T,E])
  have ha' : LowA.aTotal O.cycle ga ab∈Icc 0 (1/6:ℝ) := by
    simpa [LowA.aTotal,hG,hA] using ha
  have htd' : td=true→delta O.cycle.theta T≤0 := by
    intro ht
    rw [hT]
    exact htd ht
  exact reduced_core_false O.source hqU O.E_core O.reduced ga ab td hGA' hAB' hBT' hTD' ha' htd'

/-- Every DE2/3 and EH0/1 owner, every signed E total, and both true
radial kinds are now excluded for this A/T scope. -/
theorem source_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (ga ab td : Bool)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (ha : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0) : False := by
  rcases I.radial E with houter|hcore
  · let S := OuterE.select I hqU houter
    have hn := I.necessary
    exact LowA.actual_false ga ab td S.de S.eh hn.sorted hn.contained (hn.core T) hqU
      I.H_positive.le I.G_negative.le I.B_negative.le I.D_negative.le
      I.positive_variation.le (original_HG I) hGA hAB hBT hTD S.DE S.EH ha htd S.total_nonneg
  · exact core_false I hqL hqU hcore ga ab td hGA hAB hBT hTD ha htd

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELowA
