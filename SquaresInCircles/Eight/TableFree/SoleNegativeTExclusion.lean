module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTEndpoint
public import SquaresInCircles.Eight.TableFree.SolePositiveExclusion
public import SquaresInCircles.Eight.TableFree.SolePositiveTExclusion
public import SquaresInCircles.Eight.TableFree.NegativeSecondaryEExclusion

/-!
# The genuine negative-T sole-E exclusions on original states

Uncompiled source. A feasible secondary is selected on the same source
cycle. Otherwise the original boundary condition gives the short flat
T primary used in the stress argument. No G/T tangent sign or moved
source is assumed. EH permits either E sign; DE retains precisely its
nonpositive-E axis hypothesis.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTExclusion
open Candidate SoleTScalarModel SolePositiveTSplitModel
open SoleNegativeTCoefficients SoleNegativeTOrdinaryData
open NegativeSecondaryEExclusion

theorem original_flat_false {C : SignedCycle} {ab : Fin 4} (de td : Bool) {q s : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hs : s∈shortDomain td) (hs0 : 0<s) (hsource : tPrimary C td= -s)
    (hcore : (C.point T).a=7/12) (hflat : td=false → delta C.theta T=0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td)
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  let t := delta C.theta G+(if de then delta C.theta D else delta C.theta E)
  let f := SolePositiveTExclusion.choose de t
  have hde : isDE f=de := SolePositiveTExclusion.choose_isDE de t
  have hE' : 0≤ePrimary C f := by simpa [ePrimary,hde] using hE
  have htotal : delta C.theta G+ePrimary C f=t := by simp [t,ePrimary,hde]
  obtain ⟨ht0,hP,hN⟩ := SoleNegativeTOriginalBlocks.original_budgets hab f false td
    hvar hG hE' hs0.le hsource htotal
  have hP0 : 0≤∑i,(SoleNegativeTOriginalBlocks.blocks C ab f false td t s i).P :=
    Finset.sum_nonneg (fun i _ => (SoleNegativeTOriginalBlocks.blocks C ab f false td t s i).P_nonneg)
  have htcap : t∈Icc 0 frameCap := ⟨ht0,by linarith⟩
  have ht : t∈domain f := SolePositiveTExclusion.choose_mem de htcap
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by linarith⟩
  have hq0 : 0≤q := by norm_num [qLow] at hQL; linarith
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt hq0
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  have hRsq : (Real.sqrt q)^2≤qCap := by simpa only [hR2] using hcap
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hC.contained
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hC.contained i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hM : axisCoordinate q≤283/200 := by
    have hm := Real.sqrt_le_sqrt (sub_le_sub_right hQU (1/4))
    have hu : Real.sqrt (qTrial-1/4)<1914558470771/1000000000000 := by
      have h := SoleTScalarModel.axis_upper
      rw [show ((SoleTScalarModel.axisUpper:ℚ):ℝ)=1914558470771/1000000000000 by
        norm_num [SoleTScalarModel.axisUpper]] at h
      exact h
    simp only [axisCoordinate]
    linarith
  have hconc := SoleNegativeTSplit.concave (s := s) ab td hR hRsq hM ht hC.sorted hcCap ha
  have h0 : 0<SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s 0 := by
    have hh := SoleNegativeTEndpoint.endpoint_positive false td hab hQL hQU ht hs hs0
      hC hn hvar hG hE' hsource htotal hcore hflat
    simpa only [x,face,Bool.false_eq_true,if_false] using hh
  have h1 : 0<SoleNegativeTSplit.value C ab f td (Real.sqrt q) (axisCoordinate q) t s t := by
    have hh := SoleNegativeTEndpoint.endpoint_positive true td hab hQL hQU ht hs hs0
      hC hn hvar hG hE' hsource htotal hcore hflat
    simpa only [x,face,if_true,sub_zero] using hh
  have hpos := SoleNegativeTSplit.positive_of_endpoints hconc hx h0 h1
  have hnec := SoleNegativeTSplit.necessary td hab hR ht (short_small hs) hG hE' htotal
    hC.sorted hc hn (SoleEndpointSupport.primary_le_axis hQL (hC.sorted E) (hC.contained E))
    (by intro h; apply hsign; simpa only [hde] using h)
    (by simpa only [deOwner,ehOwner,hde] using hf)
  exact (not_lt_of_ge hnec) hpos

theorem reselect_TD {C : SignedCycle} {ab td de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 td de eh i)) (hT : C.Feasible T 0) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · simpa [CoreEStress.owners] using hf 0
  · simpa [CoreEStress.owners] using hf 1
  · simpa [CoreEStress.owners] using hf 2
  · simpa [CoreEStress.owners] using hf 3
  · simpa [CoreEStress.owners,T] using hT
  · simpa [CoreEStress.owners] using hf 5
  · simpa [CoreEStress.owners] using hf 6

theorem reselect_BT {C : SignedCycle} {ab bt de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt 0 de eh i)) (hB : C.Feasible B 2) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · simpa [CoreEStress.owners] using hf 0
  · simpa [CoreEStress.owners] using hf 1
  · simpa [CoreEStress.owners] using hf 2
  · simpa [CoreEStress.owners,B] using hB
  · simpa [CoreEStress.owners] using hf 4
  · simpa [CoreEStress.owners] using hf 5
  · simpa [CoreEStress.owners] using hf 6

theorem negative_TD_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hsource : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hsource]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  obtain hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_TD_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core T) (hC.core D) hcap hn.D_nonpos hs hBT hTD
  · have hsame : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hsource] using hsecondary)
    exact SolePositiveExclusion.original_false de hQL hQU hC hn hvar hab hG hE hsign
      (reselect_TD hf hsame)
  · exact original_flat_false de true hQL hQU hC hn hvar hab hG hE
      (show s∈shortDomain true from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
      (by intro h; cases h) hsign hf

theorem negative_BT_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact SolePositiveExclusion.original_false de hQL hQU hC hn hvar hab hG hE hsign
      (reselect_BT hf hsecondary)
  let s := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hsource : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hsource]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hsource] using hh))
  have hcap : q≤qCap := hQU.trans uniform_radius_order.2.2.1.le
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hcap hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact original_flat_false de false hQL hQU hC hn hvar hab hG hE
    (show s∈shortDomain false from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
    (fun _ => halign) hsign hf

theorem all_TD_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  by_cases hT : 0≤delta C.theta T
  · exact SolePositiveTExclusion.original_false de true hQL hQU hC hn hvar hab hG hE hT hsign hf
  · exact negative_TD_false de hQL hQU hC hn hvar hab hG hE hTb (lt_of_not_ge hT) hsign hf

theorem all_BT_false {C : SignedCycle} {ab : Fin 4} (de : Bool) {q : ℝ}
    (hQL : qLow≤q) (hQU : q≤qTrial) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G)
    (hE : 0≤ if de then delta C.theta D else delta C.theta E)
    (hTb : (C.point T).Boundary q) (halign : delta C.theta B<0 → delta C.theta T=0)
    (hsign : de=true → (C.point E).y≤0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0
      (if de then 3 else 2) (if de then 0 else 1) i)) : False := by
  by_cases hB : 0≤delta C.theta B
  · exact SolePositiveTExclusion.original_false de false hQL hQU hC hn hvar hab hG hE hB hsign hf
  · have hB' := lt_of_not_ge hB
    exact negative_BT_false de hQL hQU hC hn hvar hab hG hE hTb hB' (halign hB') hsign hf

end SquaresInCircles.Eight.TableFree.SoleNegativeTExclusion
