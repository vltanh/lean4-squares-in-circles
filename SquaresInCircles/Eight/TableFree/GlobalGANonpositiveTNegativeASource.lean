module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTLowSource

/-!
# The fixed negative-A stress at an actual negative-BT3 alignment

Uncompiled Section 4 of the paired-T note, after the actual A-normal-form
reduction. The retained A primaries have their original secant weights.
Both T projections have weight two. Every E signed-total support charge
and each charged four-circle reference reserve is supplied internally.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.NegativeA
open Candidate Secondary NegativePrimary PairedE

abbrev owners := Paired.Source.owners
abbrev aMagnitude := PairedE.Negative.aMagnitude

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) : ℝ :=
  ∑i,weights ga ab C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))

def reference (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) : ℝ :=
  baseStress+
    (if hg=0 then
      oneIncrement k 1 (erase eh (delta C.theta E)) (C.point H)+
        pairIncrement k l (delta C.theta H) (erase ga (delta C.theta G)) (C.point G).reflect
    else
      pairIncrement k 1 (delta C.theta H) (erase eh (delta C.theta E)) (C.point H)+
        oneIncrement k l (erase ga (delta C.theta G)) (C.point G).reflect)+
    pairIncrement l 2 (erase ab (delta C.theta A)) 0 (C.point B).reflect+
    dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) : ℝ :=
  2*PairedA.work (C.point T) (delta C.theta B) 0+charge*delta C.theta B

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (hG : Real.cos (delta C.theta G)≠0)
    (hA : Real.cos (delta C.theta A)≠0) (hTD : delta C.theta T=0) :
    actualStress C hg ga ab de eh=
      reference C hg ga ab de eh+NegativePrimary.gains ga ab false C+tGain C+
        charge*cycleTotal C de eh+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) := by
  have hT : C.theta D-C.theta T=0 := by simpa [delta,next,T,D] using hTD
  cases ga <;> cases ab <;> cases de <;> cases eh <;> rcases hhg with rfl|rfl <;>
    simp [actualStress,weights,owners,Paired.Source.owners,reference,NegativePrimary.gains,erase,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,baseStress,oneIncrement,pairIncrement,
      pairF,pairG,dIncrement,dF,dG,primaryIncrement,tdIncrement,cycleTotal,total,selected,
      primaryGain,tGain,PairedA.work,edgeWidth,pairWidth,SignedPoint.reflect,k,l,charge,hT]
  all_goals
    have hG' : Real.cos (C.theta A-C.theta G)≠0 := hG
    have hA' : Real.cos (C.theta B-C.theta A)≠0 := hA
    field_simp [hG',hA']
    ring

theorem reference_reserve {q : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool) (hhg : hg=0∨hg=2)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    (7/10000:ℝ)<reference C hg ga ab de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab true
  simp only [erase_true] at hbb
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) true de
  simp only [erase_true] at hdb
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := actual_dIncrement_nonneg (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  rcases hhg with rfl|rfl
  · have hH := actual_H_one (x:=erase eh (delta C.theta E)) hHy (hc H) hq
      (erase_abs_bound eh (original_error_bound hvar hn E))
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) false ga
    simp only [erase_false] at hgb
    have hG := actual_G_pair (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [reference,if_pos rfl]
    linarith [baseStress_reserve]
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) false eh
    simp only [erase_false] at hhb
    have hH := actual_H_pair hHy (hc H) hq hhb.1 hhb.2
    have hG := actual_G_one (P:=(C.point G).reflect) (x:=erase ga (delta C.theta G))
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq (erase_abs_bound ga (original_error_bound hvar hn G))
    simp only [reference,show (2:Fin 4)≠0 by decide,if_false]
    linarith [baseStress_reserve]

theorem t_gain_lower {C : SignedCycle}
    (hs : (C.point T).Sorted) (hcore : (C.point T).AvoidsCore)
    (hb : delta C.theta B≤0) (hsmall : |delta C.theta B|≤frameCap) :
    (83/700)*(-delta C.theta B)≤tGain C := by
  have hsdom : -delta C.theta B∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hb,(neg_le_abs _).trans hsmall⟩
  have hw := Paired.aligned_work_weak hs hcore hsdom
  have hp := PairedE.phi_chord hsdom
  dsimp [tGain,PositiveAngularEnvelope.phi,charge] at *
  simp only [neg_neg] at hw
  linarith

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true→delta C.theta G≤0) (hab : ab=true→delta C.theta A≤0)
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (he : 0≤cycleTotal C de eh) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hgain := PairedE.Negative.gains_lower ga ab false hs hc hcore hQ hsmall hga hab (by simp)
  simp only [PairedE.Negative.tMagnitude,selected,if_false,neg_zero,mul_zero,add_zero] at hgain
  have hg0 : selected ga (delta C.theta G)≤0 := by
    cases hh : ga
    · simp [selected]
    · simpa [selected] using hga hh
  have hab0 : selected ab (delta C.theta A)≤0 := by
    cases hh : ab
    · simp [selected]
    · simpa [selected] using hab hh
  have ha0 : 0≤aMagnitude C ga ab := by dsimp [aMagnitude,PairedE.Negative.aMagnitude]; linarith
  have hTgain := t_gain_lower (hs T) (hcore T) hb (hsmall B)
  have hEmem := cycle_total_bounds de eh hvar he
  have hEcharge := selected_charge de eh (hs E) (hc E) hQ (hsmall D) (hsmall E) hEmem
  have hElinear := charge_linear hEmem
  have hreference := reference_reserve ga ab de eh hhg hs hc hQ hHy hGy hBy hDy hvar
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,Paired.Source.owners,H] using hHG
    · simpa [owners,Paired.Source.owners,G] using hGA
    · simpa [owners,Paired.Source.owners,A] using hAB
    · simpa [owners,Paired.Source.owners,B] using hBT
    · simpa [owners,Paired.Source.owners,T] using hTD
    · simpa [owners,Paired.Source.owners,D] using hDE
    · simpa [owners,Paired.Source.owners,E] using hEH
  have hu : actualStress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i _
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab C hsmall i) (by linarith)
  rw [decomposition C ga ab de eh hhg (cos_pos (hsmall G)).ne' (cos_pos (hsmall A)).ne' htd] at hu
  change TwoPositive.ASupport.charge (cycleTotal C de eh)≤
    primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) at hEcharge
  dsimp [charge] at hu
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.NegativeA

