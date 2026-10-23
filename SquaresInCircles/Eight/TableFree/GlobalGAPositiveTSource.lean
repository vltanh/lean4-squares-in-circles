module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTRegimes

/-!
# Positive BT3 excluded for every original A/E source regime

Uncompiled complete SourceDomain dispatcher. Outer E uses its actual
nonnegative-primary reselection. Core E is normalized first at the same
radius, preserving A and T. Only afterward is A normalized as a necessary
cycle; no original-packing classification is applied to that endpoint.
The three A outcomes and three E outcomes all end in explicit source
stress contradictions. TD0 has arbitrary signed error throughout.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveT.Source
open Candidate SignedCycle Secondary PairedE NonpositiveT

theorem prepared_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hqL : qLow≤Q) (hqU : Q≤qCap) (de eh : Bool)
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0))
    (hreg : ERegime C de eh)
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0) (hz : 0≤delta C.theta B) : False := by
  obtain ⟨ga,hga⟩ : ∃ga : Bool,I.owner G=(if ga then 3 else 2) := by
    have ho : I.owner G=2∨I.owner G=3 := by simpa [highGAOwners,G] using I.allowed G
    rcases ho with ho|ho
    · exact ⟨false,ho⟩
    · exact ⟨true,ho⟩
  obtain ⟨ab,hab⟩ : ∃ab : Bool,I.owner A=(if ab then 2 else 0) := by
    have ho : I.owner A=0∨I.owner A=2 := by simpa [highGAOwners,A] using I.allowed A
    rcases ho with ho|ho
    · exact ⟨false,ho⟩
    · exact ⟨true,ho⟩
  have hGA : C.Feasible G (if ga then 3 else 2) := by simpa [hga] using I.feasible G
  have hAB : C.Feasible A (if ab then 2 else 0) := by simpa [hab] using I.feasible A
  obtain ⟨O⟩ := NegativeANormalForm.cycle_reduce ga ab
    (by norm_num [qLow] at hqL ⊢; linarith) hqU I.necessary I.radial I.G_negative.le
    (I.outer B (by simp [H,G,B,D])) I.B_negative.le I.A_upper I.A_nonpos_outer
    I.strict_spread hGA hAB
  have hH := O.point_other H (by norm_num [H,A])
  have hG := O.point_other G (by norm_num [G,A])
  have hB := O.point_other B (by norm_num [B,A])
  have hD := O.point_other D (by norm_num [D,A])
  have hE := O.point_other E (by norm_num [E,A])
  have hδB := O.other_delta B (by norm_num [B,G]) (by norm_num [B,A])
  have hδD := O.other_delta D (by norm_num [D,G]) (by norm_num [D,A])
  have hδE := O.other_delta E (by norm_num [E,G]) (by norm_num [E,A])
  have hHy : 0≤(O.cycle.point H).y := by rw [hH]; exact I.H_positive.le
  have hGy : (O.cycle.point G).y≤0 := by rw [hG]; exact I.G_negative.le
  have hBy : (O.cycle.point B).y≤0 := by rw [hB]; exact I.B_negative.le
  have hDy : (O.cycle.point D).y≤0 := by rw [hD]; exact I.D_negative.le
  have hvar := O.variation.trans I.positive_variation.le
  have hHG : O.cycle.Feasible H 0∨O.cycle.Feasible H 2 := by
    rcases NegativeELowA.original_HG I with hh|hh
    · exact Or.inl ((O.other_edges H (by norm_num [H,G,A]) 0).2 hh)
    · exact Or.inr ((O.other_edges H (by norm_num [H,G,A]) 2).2 hh)
  have hBT' := (O.other_edges B (by norm_num [B,G,A]) 3).2 hBT
  have hTD' := (O.other_edges T (by norm_num [T,G,A]) 0).2 hTD
  have hDE' := (O.other_edges D (by norm_num [D,G,A]) _).2 hDE
  have hEH' := (O.other_edges E (by norm_num [E,G,A]) _).2 hEH
  have hz' : 0≤delta O.cycle.theta B := by rw [hδB]; exact hz
  have hreg' : ERegime O.cycle de eh := by
    simpa only [ERegime,cycleTotal,total,hδD,hδE,hE] using hreg
  rcases O.reduced with ha|⟨hga,hab,hflat,hAy,hu⟩|⟨hga,hab,hflat,hAy,hv⟩
  · exact nonnegative_A_false O.ga O.ab de eh O.necessary.sorted O.necessary.contained hqU
      hHy hGy hBy hDy hvar ha hz' hreg' hHG O.GA O.AB hBT' hTD' hDE' hEH'
  · have hGA' : O.cycle.Feasible G 3 := by simpa [hga] using O.GA
    have hAB' : O.cycle.Feasible A 0 := by simpa [hab] using O.AB
    have hs : -delta O.cycle.theta G∈Ioc 0 frameCap :=
      ⟨by linarith [hu.2],by norm_num [frameCap]; linarith [hu.1]⟩
    have hlocal : quarterFeasible (O.cycle.point G) (O.cycle.point A)
        (-(-delta O.cycle.theta G)) 3 := by
      simpa [Feasible,slack,edge,word,next,G,A,quarterFeasible,sub_nonneg] using hGA'
    have hentry := NegativeA.GA_entry (O.necessary.sorted G) (O.necessary.contained G)
      (O.necessary.sorted A) (O.radial A) hqU hGy
      (fun h => (not_le_of_gt hAy.1 h).elim) hs hlocal
    rcases hentry with hsecondary|⟨hflat',hpos,hcut,hangle⟩
    · have hGA2 : O.cycle.Feasible G 2 := by
        simpa [Feasible,slack,edge,word,next,G,A,quarterFeasible,sub_nonneg] using hsecondary
      exact nonnegative_A_false false false de eh O.necessary.sorted O.necessary.contained hqU
        hHy hGy hBy hDy hvar (by simp [PositiveBT3.Source.aTotal,PairedE.total,selected])
        hz' hreg' hHG hGA2 hAB' hBT' hTD' hDE' hEH'
    · exact negative_A_false true de eh O.necessary.sorted O.necessary.contained hqU
        hHy hGy hBy hDy hvar
        (show -delta O.cycle.theta G∈Icc 0 (NegativeABT3.Explicit.angleCut true) from
          ⟨hs.1.le,hangle.le⟩)
        (by simp [NegativeABT3.Source.aError]) hflat hAy.1.le hcut.le
        hz' hreg' hHG hGA' hAB' hBT' hTD' hDE' hEH'
  · have hGA' : O.cycle.Feasible G 2 := by simpa [hga] using O.GA
    have hAB' : O.cycle.Feasible A 2 := by simpa [hab] using O.AB
    exact negative_A_false false de eh O.necessary.sorted O.necessary.contained hqU
      hHy hGy hBy hDy hvar
      (show -delta O.cycle.theta A∈Icc 0 (NegativeABT3.Explicit.angleCut false) from
        ⟨by linarith [hv.2],by change _≤(19/50:ℝ); linarith [hv.1]⟩)
      (by simp [NegativeABT3.Source.aError]) hflat hAy.1.le hAy.2.le
      hz' hreg' hHG hGA' hAB' hBT' hTD' hDE' hEH'

theorem reduced_core_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hqL : qLow≤Q) (hqU : Q≤qCap) (hEc : (C.point E).Core)
    (hr : CoreENormalForm.Reduced C (I.owner D) (I.owner E))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0) (hz : 0≤delta C.theta B) : False := by
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
    exact prepared_false I hqL hqU de eh hDE hEH (Or.inl he) hBT hTD hz
  · rcases hnegative with ⟨hde,heh,hd⟩|⟨hde,heh,he⟩
    · have hDE : C.Feasible D 3 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 0 := by simpa [heh] using I.feasible E
      exact prepared_false I hqL hqU true false hDE hEH
        (Or.inr ⟨hflat,Or.inl ⟨rfl,rfl,hd.le⟩⟩) hBT hTD hz
    · have hDE : C.Feasible D 2 := by simpa [hde] using I.feasible D
      have hEH : C.Feasible E 1 := by simpa [heh] using I.feasible E
      by_cases hEH0 : C.Feasible E 0
      · exact prepared_false I hqL hqU false false hDE hEH0
          (Or.inl (by simp [cycleTotal,total,selected])) hBT hTD hz
      · obtain ⟨hf,hb,hu⟩ := NegativeEHPositiveTD.Source.genuine_domain
          I.necessary.sorted I.necessary.contained hqU I.H_positive.le I.E_nonpos hEc
          I.positive_variation.le he hEH hEH0
        exact prepared_false I hqL hqU false true hDE hEH
          (Or.inr ⟨hf,Or.inr ⟨rfl,rfl,⟨neg_nonneg.mpr he.le,hu⟩,hb⟩⟩) hBT hTD hz

/-- Every A sign, every selected A total, and both E radial kinds are
resolved internally. This is the complete positive-BT3 source lane. -/
theorem original_false {Q : ℝ} {C : SignedCycle} (I : SourceDomain Q C)
    (hqL : qLow≤Q) (hqU : Q≤qCap)
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0) (hz : 0≤delta C.theta B) : False := by
  rcases I.radial E with houter|hcore
  · let S := OuterE.select I hqU houter
    exact prepared_false I hqL hqU S.de S.eh S.DE S.EH (Or.inl S.total_nonneg) hBT hTD hz
  · obtain ⟨O⟩ := CoreENormalForm.reduce I hqL hqU hcore
    have hBT' := (O.other_feasible B (by norm_num [B,D]) (by norm_num [B,E]) 3).2 hBT
    have hTD' := (O.other_feasible T (by norm_num [T,D]) (by norm_num [T,E]) 0).2 hTD
    have hδB := O.other_delta B (by norm_num [B,D]) (by norm_num [B,E])
    exact reduced_core_false O.source hqL hqU O.E_core O.reduced hBT' hTD'
      (by rw [hδB]; exact hz)

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveT.Source
