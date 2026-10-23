module

public import SquaresInCircles.Eight.TableFree.NegativeCoreEReduction
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEExclusion
public import SquaresInCircles.Eight.TableFree.GlobalGAPairedENegativeSource
public import SquaresInCircles.Eight.TableFree.GlobalGASourceDomain

/-!
# Actual high-GA negative-core-E reduction and nonpositive A/T exclusion

Uncompiled transcription of the mixed negative-E hand reduction.  This
entry uses only the original necessary geometry, the outer D/H anchors,
and actual DE/EH owners.  In particular no low-GA owner restriction or
normalized hard-source hypothesis is used to move E.  The resulting
cycle retains every G/A/B/T point, frame, and selected separator.

The terminal source theorem closes all core-E signs and both E owners
when the selected A and T primary errors are individually nonpositive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.CoreENegativeTotal
open Candidate ActualCoreEBlocks NegativeCoreE

/-- The local E move requires only the D/E/H portion of the original
boundary-neighbor geometry.  The high-GA source constructs these fields
from its original points and retained weak separators. -/
structure Input (q : ℝ) where
  cycle : SignedCycle
  necessary : cycle.Necessary q
  E_nonpos : (cycle.point E).y≤0
  H_nonneg : 0≤(cycle.point H).y
  D_outer : (cycle.point D).Outer q
  H_outer : (cycle.point H).Outer q
  de : Fin 4
  eh : Fin 4
  de_allowed : de=2 ∨ de=3
  eh_allowed : eh=0 ∨ eh=1
  DE : cycle.Feasible D de
  EH : cycle.Feasible E eh

/-- Same-state owner selection after the corresponding actual projection
has been proved.  No other owner or frame is altered. -/
def identityMove {q : ℝ} (I : Input q)
    (hc : (I.cycle.point E).Core) (de eh : Fin 4)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hDE : I.cycle.Feasible D de) (hEH : I.cycle.Feasible E eh) : CycleMove q I.cycle where
  point := I.cycle.point E
  theta := I.cycle.theta E
  sorted := I.necessary.sorted E
  contained := I.necessary.contained E
  core := hc
  nonpos := I.E_nonpos
  frame_range := ⟨min_le_left _ _,le_max_left _ _⟩
  de := de
  eh := eh
  de_allowed := hde
  eh_allowed := heh
  DE := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,D,E,quarterFeasible,sub_nonneg] using hDE
  EH := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  positive_nonincrease := by simp

structure Reduction (q : ℝ) (I : Input q) where
  move : CycleMove q I.cycle
  flat : move.point.a=7/12
  normal_form : 0≤eTotal move.cycle move.de move.eh ∨
    (move.point.a=7/12 ∧ primaryDE move.cycle move.de≤0 ∧ primaryEH move.cycle move.eh≤0)

/-- A same-state EH0 selection is made only after its original weak
projection is known. The sole retained DE error then decides which
proved stress family applies; it is never silently discarded. -/
theorem reduce_with_secondary {q : ℝ} (I : Input q)
    (hq : q≤qCap) (hc : (I.cycle.point E).Core)
    (hEH : I.cycle.Feasible E 0) : Nonempty (Reduction q I) := by
  let de := I.de
  have hde : de=2 ∨ de=3 := by
    simpa [de] using I.de_allowed
  let O := identityMove I hc de 0 hde (Or.inl rfl) (I.DE) hEH
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H)
      (I.cycle.theta H-I.cycle.theta E) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hEH
  have hf := (secondary_flat (I.necessary.sorted E) I.E_nonpos hc
    (I.necessary.sorted H) (I.necessary.contained H) hq hEH').1
  refine ⟨⟨O,hf,?_⟩⟩
  by_cases hpos : 0≤primaryDE O.cycle O.de
  · left
    rw [eTotal,O.primary_EH]
    simpa [O,identityMove] using hpos
  · right
    refine ⟨hf,le_of_lt (lt_of_not_ge hpos),?_⟩
    rw [O.primary_EH]
    norm_num [O,identityMove]

/-- Complete owner and sign split at the original q. The two mixed cases
invoke the actual compact core-arc endpoint and explicit flat-gap endpoint;
no feasibility or terminal-event premise is supplied by the caller. -/
theorem reduce_negative_total {q : ℝ} (I : Input q)
    (hqL : qLow≤q) (hqU : q≤qCap) (hc : (I.cycle.point E).Core)
    (hneg : eTotal I.cycle (I.de) (I.eh)<0) :
    Nonempty (Reduction q I) := by
  by_cases hEH0 : I.cycle.Feasible E 0
  · exact reduce_with_secondary I hqU hc hEH0
  let C := I.cycle
  have heh : I.eh=1 := by
    have hh : I.eh=0 ∨ I.eh=1 := by
      exact I.eh_allowed
    rcases hh with hh | hh
    · exact False.elim (hEH0 (by simpa [hh] using I.EH))
    · exact hh
  have hde : I.de=2 ∨ I.de=3 := by
    exact I.de_allowed
  have hEH : quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 1 := by
    have hh : C.Feasible E 1 := by simpa [C,heh] using I.EH
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hnot : ¬quarterFeasible (C.point E) (C.point H) (C.theta H-C.theta E) 0 := by
    intro hh
    apply hEH0
    simpa [C,SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
      delta,next,H,E,quarterFeasible,sub_nonneg] using hh
  have hsmall (i : Vertex) : |delta C.theta i|≤frameCap := I.necessary.spread (next i) i
  have hflat {n : ℝ} (hn : n∈Ioc 0 frameCap)
      (heq : C.theta H-C.theta E= -n) : (C.point E).a=7/12 :=
    (genuine_negative_flat (I.necessary.sorted E) I.E_nonpos hc
      (I.necessary.sorted H) I.H_nonneg (I.necessary.contained H)
      hqU hn (by simpa only [heq] using hEH)
      (by simpa only [heq] using hnot)).1
  rcases hde with hde | hde
  · have hr : C.theta H-C.theta E<0 := by
      simpa [eTotal,primaryDE,primaryEH,hde,heh,C,delta,next,H,D,E] using hneg
    have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
      ⟨by linarith,(le_abs_self _).trans (I.necessary.spread E H)⟩
    have hf := hflat hn (by ring)
    let O := identityMove I hc 2 1 (Or.inl rfl) (Or.inr rfl)
      (by simpa [hde] using I.DE)
      (by simpa [heh] using I.EH)
    refine ⟨⟨O,hf,Or.inr ⟨hf,?_,?_⟩⟩⟩
    · rw [O.primary_DE]; norm_num [O,identityMove]
    · rw [O.primary_EH]; simpa [O,identityMove,C] using hr.le
  · have hsum : C.theta H-C.theta D<0 := by
      have hh := hneg
      simp [eTotal,primaryDE,primaryEH,hde,heh,C,delta,next,H,D,E] at hh
      linarith
    have hDE : quarterFeasible (C.point D) (C.point E) (C.theta E-C.theta D) 3 := by
      have hh : C.Feasible D 3 := by simpa [C,hde] using I.DE
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
        delta,next,D,E,quarterFeasible,sub_nonneg] using hh
    by_cases hEHneg : C.theta H<C.theta E
    · have hn : C.theta E-C.theta H∈Ioc 0 frameCap :=
        ⟨sub_pos.mpr hEHneg,(le_abs_self _).trans (I.necessary.spread E H)⟩
      have hf := hflat hn (by ring)
      by_cases hDEpos : C.theta D<C.theta E
      · obtain ⟨P⟩ := negative_EH_endpoint hqL hqU
          (I.necessary.sorted D) (I.necessary.core D) I.D_outer
          (I.necessary.sorted H) (I.necessary.core H) I.H_nonneg
          (I.necessary.contained H) (I.necessary.sorted E) I.E_nonpos hc hn
          ⟨sub_pos.mpr hDEpos,by linarith⟩ hDE
          (by simpa only [neg_sub] using hEH) (by simpa only [neg_sub] using hnot)
        let O := P.toCycle hDEpos
        refine ⟨⟨O,P.flat,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
        · rw [O.primary_DE]; norm_num [O,NegativeEHEndpoint.toCycle]
        · rw [O.primary_EH]
          simpa [O,NegativeEHEndpoint.toCycle] using hsum.le
      · let O := identityMove I hc 3 1 (Or.inr rfl) (Or.inr rfl)
          (by simpa [hde] using I.DE)
          (by simpa [heh] using I.EH)
        refine ⟨⟨O,hf,Or.inr ⟨hf,?_,?_⟩⟩⟩
        · rw [O.primary_DE]
          simpa [O,identityMove,C] using sub_nonpos.mpr (le_of_not_gt hDEpos)
        · rw [O.primary_EH]
          simpa [O,identityMove,C] using (sub_neg.mpr hEHneg).le
    · have hp : 0<C.theta H-C.theta E := by
        have hr0 : 0≤C.theta H-C.theta E := sub_nonneg.mpr (le_of_not_gt hEHneg)
        apply lt_of_le_of_ne hr0
        intro heq
        apply hnot
        simpa [heq.symm,quarterFeasible,quarterProjection] using hEH
      have hn : C.theta D-C.theta E∈Ioc 0 frameCap :=
        ⟨by linarith,(le_abs_self _).trans (I.necessary.spread D E)⟩
      obtain ⟨P⟩ := negative_DE_endpoint hqL hqU (I.necessary.sorted H)
        I.H_nonneg I.H_outer
        (I.necessary.sorted E) I.E_nonpos hc hn ⟨hp,by linarith⟩
        (by simpa only [neg_sub] using hDE) hEH
      let O := P.toCycle
      refine ⟨⟨O,P.flat,Or.inr ⟨P.flat,?_,?_⟩⟩⟩
      · rw [O.primary_DE]
        simp only [O,NegativeDEEndpoint.toCycle,ite_true]
        linarith [P.negative_remaining]
      · rw [O.primary_EH]; norm_num [O,NegativeDEEndpoint.toCycle]
/-- A true-core point with flat primary coordinate has tangent in the
flat interval; this is read from its actual core equation. -/
theorem flat_tangent {P : SignedPoint} (hc : P.Core) (hf : P.a=7/12)
    (hy : P.y≤0) : P.y∈Icc (-(1/2:ℝ)) 0 := by
  have h := hc
  norm_num [SignedPoint.Core,SignedPoint.coreDistance,hf] at h
  have hm : |P.y|-1/2≤max (|P.y|-1/2) 0 := le_max_left _ _
  have hn : 0≤max (|P.y|-1/2) 0 := le_max_right _ _
  rw [abs_of_nonpos hy] at h hm hn
  constructor
  · nlinarith
  · exact hy

theorem selected_total (C : SignedCycle) (de eh : Bool) :
    eTotal C (if de then 3 else 2) (if eh then 1 else 0)=
      PairedE.cycleTotal C de eh := by
  cases de <;> cases eh <;>
    simp [eTotal,primaryDE,primaryEH,PairedE.cycleTotal,PairedE.total,PairedE.selected]

/-- All core-E owners and signed E totals are covered.  The two mixed
signs are transported at the same q, and the paired-negative endpoint
is accepted directly by the simultaneous flat-core stress. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hn : C.Necessary q) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hHo : (C.point H).Outer q) (hDo : (C.point D).Outer q)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true → delta C.theta G≤0)
    (hab : ab=true → delta C.theta A≤0)
    (htd : td=true → delta C.theta T≤0) : False := by
  let I : Input q :=
    { cycle := C
      necessary := hn
      E_nonpos := hEy
      H_nonneg := hHy
      D_outer := hDo
      H_outer := hHo
      de := if de then 3 else 2
      eh := if eh then 1 else 0
      de_allowed := by cases de <;> simp
      eh_allowed := by cases eh <;> simp
      DE := hDE
      EH := hEH }
  by_cases he : 0≤PairedE.cycleTotal C de eh
  · exact PairedE.Negative.actual_false ga ab td de eh hn.sorted hn.contained
      hn.core hqU hHy hGy hBy hDy hvar hHG hGA hAB hBT hTD hDE hEH hga hab htd he
  have hnegative : eTotal I.cycle I.de I.eh<0 := by
    change eTotal C (if de then 3 else 2) (if eh then 1 else 0)<0
    rw [selected_total]
    exact lt_of_not_ge he
  obtain ⟨R⟩ := reduce_negative_total I hqL hqU hEc hnegative
  let O := R.move
  have hn' : O.cycle.Necessary q := O.necessary hn
  have hv' : positiveVariation O.cycle.theta≤frameCap :=
    O.positive_nonincrease.trans hvar
  have hHy' : 0≤(O.cycle.point H).y := by
    rw [(O.unchanged H (by decide)).1]; exact hHy
  have hGy' : (O.cycle.point G).y≤0 := by
    rw [(O.unchanged G (by decide)).1]; exact hGy
  have hBy' : (O.cycle.point B).y≤0 := by
    rw [(O.unchanged B (by decide)).1]; exact hBy
  have hDy' : (O.cycle.point D).y≤0 := by
    rw [(O.unchanged D (by decide)).1]; exact hDy
  have hHG' : O.cycle.Feasible H 0 ∨ O.cycle.Feasible H 2 :=
    hHG.imp ((O.other_feasible H (by decide) (by decide) 0).2)
      ((O.other_feasible H (by decide) (by decide) 2).2)
  have hGA' := (O.other_feasible G (by decide) (by decide) (if ga then 3 else 2)).2 hGA
  have hAB' := (O.other_feasible A (by decide) (by decide) (if ab then 2 else 0)).2 hAB
  have hBT' := (O.other_feasible B (by decide) (by decide) 2).2 hBT
  have hTD' := (O.other_feasible T (by decide) (by decide) (if td then 2 else 0)).2 hTD
  have hga' : ga=true → delta O.cycle.theta G≤0 := by
    intro hh; rw [O.other_delta G (by decide) (by decide)]; exact hga hh
  have hab' : ab=true → delta O.cycle.theta A≤0 := by
    intro hh; rw [O.other_delta A (by decide) (by decide)]; exact hab hh
  have htd' : td=true → delta O.cycle.theta T≤0 := by
    intro hh; rw [O.other_delta T (by decide) (by decide)]; exact htd hh
  obtain ⟨de',hde'⟩ : ∃de' : Bool,O.de=(if de' then 3 else 2) := by
    rcases O.de_allowed with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  obtain ⟨eh',heh'⟩ : ∃eh' : Bool,O.eh=(if eh' then 1 else 0) := by
    rcases O.eh_allowed with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hDE' : O.cycle.Feasible D (if de' then 3 else 2) := by
    simpa only [hde'] using O.DE_actual
  have hEH' : O.cycle.Feasible E (if eh' then 1 else 0) := by
    simpa only [heh'] using O.EH_actual
  rcases R.normal_form with hnonneg | ⟨hflat,hdenonpos,hehnonpos⟩
  · have he' : 0≤PairedE.cycleTotal O.cycle de' eh' := by
      rw [←selected_total]
      simpa only [hde',heh'] using hnonneg
    exact PairedE.Negative.actual_false ga ab td de' eh' hn'.sorted hn'.contained
      hn'.core hqU hHy' hGy' hBy' hDy' hv' hHG' hGA' hAB' hBT' hTD'
      hDE' hEH' hga' hab' htd' he'
  · have hflat' : (O.cycle.point E).a=7/12 := by
      simpa [CycleMove.cycle,replacePoint] using hflat
    have hEy' : (O.cycle.point E).y∈Icc (-(1/2:ℝ)) 0 := by
      simpa [CycleMove.cycle,replacePoint] using flat_tangent O.core hflat O.nonpos
    have hde0 : de'=true → delta O.cycle.theta D≤0 := by
      intro hh
      simpa [primaryDE,hde',hh] using hdenonpos
    have heh0 : eh'=true → delta O.cycle.theta E≤0 := by
      intro hh
      simpa [primaryEH,heh',hh] using hehnonpos
    exact NegativeFlatE.actual_false ga ab td de' eh' hn'.sorted hn'.contained
      hn'.core hqU hHy' hGy' hBy' hDy' hflat' hEy' hv' hHG' hGA' hAB'
      hBT' hTD' hDE' hEH' hga' hab' htd' hde0 heh0

/-- Original high-GA source adapter.  All geometry and allowed owner
classes are supplied by the actual candidate frame; only the selected
A/T sign regime is split by the caller. -/
theorem source_false {q : ℝ} {C : SignedCycle} (I : SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) (hEc : (C.point E).Core)
    (hBT : C.Feasible B 2)
    (hga : I.owner G=3 → delta C.theta G≤0)
    (hab : I.owner A=2 → delta C.theta A≤0)
    (htd : I.owner T=2 → delta C.theta T≤0) : False := by
  have hhg : I.owner H=0 ∨ I.owner H=2 := by
    simpa [highGAOwners,H] using I.allowed H
  have hHG : C.Feasible H 0 ∨ C.Feasible H 2 := by
    rcases hhg with hh | hh
    · exact Or.inl (by simpa [hh] using I.feasible H)
    · exact Or.inr (by simpa [hh] using I.feasible H)
  obtain ⟨ga,hga'⟩ : ∃ga : Bool,I.owner G=(if ga then 3 else 2) := by
    have hh : I.owner G=2 ∨ I.owner G=3 := by simpa [highGAOwners,G] using I.allowed G
    rcases hh with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  obtain ⟨ab,hab'⟩ : ∃ab : Bool,I.owner A=(if ab then 2 else 0) := by
    have hh : I.owner A=0 ∨ I.owner A=2 := by simpa [highGAOwners,A] using I.allowed A
    rcases hh with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  obtain ⟨td,htd'⟩ : ∃td : Bool,I.owner T=(if td then 2 else 0) := by
    have hh : I.owner T=0 ∨ I.owner T=2 := by simpa [highGAOwners,T] using I.allowed T
    rcases hh with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  obtain ⟨de,hde'⟩ : ∃de : Bool,I.owner D=(if de then 3 else 2) := by
    have hh : I.owner D=2 ∨ I.owner D=3 := by simpa [highGAOwners,D] using I.allowed D
    rcases hh with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  obtain ⟨eh,heh'⟩ : ∃eh : Bool,I.owner E=(if eh then 1 else 0) := by
    have hh : I.owner E=0 ∨ I.owner E=1 := by simpa [highGAOwners,E] using I.allowed E
    rcases hh with hh | hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  exact actual_false ga ab td de eh I.necessary hqL hqU I.H_positive.le
    I.G_negative.le I.B_negative.le I.D_negative.le
    (I.outer H (by simp)) (I.outer D (by simp)) I.E_nonpos hEc
    I.positive_variation.le hHG
    (by simpa only [hga'] using I.feasible G)
    (by simpa only [hab'] using I.feasible A) hBT
    (by simpa only [htd'] using I.feasible T)
    (by simpa only [hde'] using I.feasible D)
    (by simpa only [heh'] using I.feasible E)
    (fun hh => hga (by simpa [hh] using hga'))
    (fun hh => hab (by simpa [hh] using hab'))
    (fun hh => htd (by simpa [hh] using htd'))

end SquaresInCircles.Eight.TableFree.GlobalGA.CoreENegativeTotal
