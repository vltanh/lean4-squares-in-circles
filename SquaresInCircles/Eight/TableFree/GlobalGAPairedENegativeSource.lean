module

public import SquaresInCircles.Eight.TableFree.GlobalGAPairedEGains
public import SquaresInCircles.Eight.TableFree.GlobalGANegativePrimaryExclusion

/-!
# Nonnegative E total with nonpositive A/T alternatives

Uncompiled transcription of Section 6 of the combined-E hand proof.
Every weight multiplies an original weak separator. The five Boolean
flags indicate the original primary owners; no state or frame is moved.
The reference contains only angular deletions inside the same four
circle expressions, whose individual bounds require no zero-sum premise.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PairedE.Negative
open Candidate Secondary NegativePrimary

def owners (hg : Fin 4) (ga ab td de eh : Bool) : Vertex→Fin 4 :=
  ![hg,if ga then 3 else 2,if ab then 2 else 0,2,if td then 2 else 0,
    if de then 3 else 2,if eh then 1 else 0]

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab td de eh : Bool) : ℝ :=
  ∑i,weights ga ab C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab td de eh i))

def reference (C : SignedCycle) (hg : Fin 4) (ga ab td de eh : Bool) : ℝ :=
  baseStress+
    (if hg=0 then
      oneIncrement k 1 (erase eh (delta C.theta E)) (C.point H)+
        pairIncrement k l (delta C.theta H) (erase ga (delta C.theta G)) (C.point G).reflect
    else
      pairIncrement k 1 (delta C.theta H) (erase eh (delta C.theta E)) (C.point H)+
        oneIncrement k l (erase ga (delta C.theta G)) (C.point G).reflect)+
    pairIncrement l 2 (erase ab (delta C.theta A)) (delta C.theta B) (C.point B).reflect+
    dIncrement (erase td (delta C.theta T)) (erase de (delta C.theta D)) (C.point D).reflect

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab td de eh : Bool)
    (hhg : hg=0∨hg=2) (hG : Real.cos (delta C.theta G)≠0)
    (hA : Real.cos (delta C.theta A)≠0) :
    actualStress C hg ga ab td de eh=
      reference C hg ga ab td de eh+NegativePrimary.gains ga ab td C+
        charge*cycleTotal C de eh+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) := by
  cases ga <;> cases ab <;> cases td <;> cases de <;> cases eh <;>
    rcases hhg with rfl|rfl <;>
    simp [actualStress,weights,owners,reference,NegativePrimary.gains,erase,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,baseStress,oneIncrement,pairIncrement,
      pairF,pairG,dIncrement,dF,dG,primaryIncrement,tdIncrement,cycleTotal,total,selected,
      primaryGain,edgeWidth,pairWidth,SignedPoint.reflect,k,l,charge]
  all_goals
    have hG' : Real.cos (C.theta A-C.theta G)≠0 := hG
    have hA' : Real.cos (C.theta B-C.theta A)≠0 := hA
    field_simp [hG',hA']
    ring

theorem reference_reserve {q : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab td de eh : Bool) (hhg : hg=0∨hg=2)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    (7/10000:ℝ)<reference C hg ga ab td de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td de
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

def aMagnitude (C : SignedCycle) (ga ab : Bool) : ℝ :=
  -selected ga (delta C.theta G)-selected ab (delta C.theta A)
def tMagnitude (C : SignedCycle) (td : Bool) : ℝ := -selected td (delta C.theta T)

theorem gains_lower {q : ℝ} {C : SignedCycle} (ga ab td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hga : ga=true→delta C.theta G≤0) (hab : ab=true→delta C.theta A≤0)
    (htd : td=true→delta C.theta T≤0) :
    (71983/1000000)*aMagnitude C ga ab+(83/700)*tMagnitude C td≤
      NegativePrimary.gains ga ab td C := by
  have hA := SignedPoint.coordinate_bounds (hs A) (hcore A) (hc A) hq
  have hG := SignedPoint.coordinate_bounds (hs G) (hcore G) (hc G) hq
  have hB := SignedPoint.coordinate_bounds (hs B) (hcore B) (hc B) hq
  have hBu : -(C.point B).y≤283/200 := by linarith [neg_le_abs (C.point B).y,hB.2.2]
  have hg : (71983/1000000)*(-selected ga (delta C.theta G))≤
      (if ga then primaryIncrement (delta C.theta G) (C.point A).a (C.point G).a else 0) := by
    cases hh : ga
    · simp [selected]
    · simpa [selected] using negative_A_linear_signed (hga hh) (hsmall G) hA.1.le hG.2.1.le
  have ha : (71983/1000000)*(-selected ab (delta C.theta A))≤
      (if ab then primaryIncrement (delta C.theta A) (C.point A).a (-(C.point B).y) else 0) := by
    cases hh : ab
    · simp [selected]
    · simpa [selected] using negative_A_linear_signed (hab hh) (hsmall A) hA.1.le hBu
  have ht : (83/700)*tMagnitude C td≤
      (if td then tdIncrement (delta C.theta T) (C.point T) else 0) := by
    cases hh : td
    · simp [tMagnitude,selected]
    · simpa [tMagnitude,selected] using nonpositive_T_linear (hs T) (hcore T) (htd hh) (hsmall T)
  dsimp [NegativePrimary.gains,aMagnitude]
  linarith

theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true→delta C.theta G≤0) (hab : ab=true→delta C.theta A≤0)
    (htd : td=true→delta C.theta T≤0) (he : 0≤cycleTotal C de eh) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hgain := gains_lower ga ab td hs hc hcore hq hsmall hga hab htd
  have hg0 : selected ga (delta C.theta G)≤0 := by
    cases hh : ga
    · simp [selected]
    · simpa [selected] using hga hh
  have hab0 : selected ab (delta C.theta A)≤0 := by
    cases hh : ab
    · simp [selected]
    · simpa [selected] using hab hh
  have ha0 : 0≤aMagnitude C ga ab := by
    dsimp [aMagnitude]
    linarith
  have ht0 : 0≤tMagnitude C td := by
    cases htd' : td
    · simp [tMagnitude,selected]
    · simp [tMagnitude,selected]; exact htd htd'
  have hEmem := cycle_total_bounds de eh hvar he
  have hEcharge := selected_charge de eh (hs E) (hc E) hq (hsmall D) (hsmall E) hEmem
  have hElinear := charge_linear hEmem
  have hreference := reference_reserve ga ab td de eh hhg hs hc hq hHy hGy hBy hDy hvar
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu : actualStress C hg ga ab td de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab C hsmall i) (by linarith)
  rw [decomposition C ga ab td de eh hhg
    (ne_of_gt (cos_pos (hsmall G))) (ne_of_gt (cos_pos (hsmall A)))] at hu
  change TwoPositive.ASupport.charge (cycleTotal C de eh)≤
    primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) at hEcharge
  dsimp [charge] at hu
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PairedE.Negative
