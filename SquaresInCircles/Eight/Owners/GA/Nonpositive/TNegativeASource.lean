module

public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TAlignedGain
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TSourceData
public import SquaresInCircles.Eight.Owners.GA.Paired.ENegativeSource

/-!
# Eight squares: the fixed negative-A stress at a negative-BT3 alignment

The A primaries keep their secant weights. Both T projections have weight two. Every support charge
of the signed E total and every charged four-circle reference reserve is proved here
(`reference_reserve`, `actual_false`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.NegativeA
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
  2*PairedA.work (C.point T) (delta C.theta B) 0+GlobalGA.Secondary.charge*delta C.theta B

private def r92na_aslot (p x : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth x-1)-p*Real.sin x*P.a-p*Real.cos x*P.y+Secondary.charge*x

private def r92na_bslot (q x : ℝ) (P : SignedPoint) : ℝ :=
  q*(edgeWidth x-1)-q*Real.cos x*P.a-q*Real.sin x*P.y+Secondary.charge*x

private def r92na_zslot (x : ℝ) (P : SignedPoint) : ℝ :=
  2*edgeWidth x-2*Real.sin x*P.a-2*Real.cos x*P.y+Secondary.charge*x

private def r92na_dslot (x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-Real.cos x*P.a-Real.sin x*P.y+Secondary.charge*x

private theorem r92na_pair_split (p q a b : ℝ) (P : SignedPoint) :
    Secondary.pairIncrement p q a b P=r92na_aslot p a P+r92na_bslot q b P+fullSupport q p := by
  simp only [Secondary.pairIncrement,pairF,pairG,r92na_aslot,r92na_bslot]
  ring

private theorem r92na_one_split (p q x : ℝ) (P : SignedPoint) :
    Secondary.oneIncrement p q x P=r92na_bslot q x P+r92na_aslot p 0 P+fullSupport q p := by
  simp only [Secondary.oneIncrement,r92na_bslot,r92na_aslot,Real.sin_zero,Real.cos_zero,
    edgeWidth_zero]
  ring

private theorem r92na_d_split (z d : ℝ) (P : SignedPoint) :
    Secondary.dIncrement z d P=r92na_zslot z P+r92na_dslot d P-(3-3*Secondary.diagonal) := by
  simp only [Secondary.dIncrement,Secondary.dF,Secondary.dG,r92na_zslot,r92na_dslot]
  ring

private theorem r92na_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private theorem r92na_edge_H0 (ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab C 0*(edgeWidth (delta C.theta 0)-C.edge 0 (owners 0 ga ab de eh 0))=
      r92na_aslot Secondary.k (delta C.theta 0) (C.point 1).reflect+
      r92na_aslot Secondary.k 0 (C.point 0)+Secondary.k-Secondary.charge*delta C.theta 0 := by
  simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
    zeroProjection,r92na_aslot,SignedPoint.reflect]
  ring

private theorem r92na_edge_H2 (ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab C 0*(edgeWidth (delta C.theta 0)-C.edge 0 (owners 2 ga ab de eh 0))=
      r92na_aslot Secondary.k 0 (C.point 1).reflect+
      r92na_aslot Secondary.k (delta C.theta 0) (C.point 0)+Secondary.k-
        Secondary.charge*delta C.theta 0 := by
  simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
    zeroProjection,r92na_aslot,SignedPoint.reflect]
  ring

private theorem r92na_edge_G (hg : Fin 4) (ga ab de eh : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta 1)≠0) :
    weights ga ab C 1*(edgeWidth (delta C.theta 1)-C.edge 1 (owners hg ga ab de eh 1))=
      r92na_bslot Secondary.l (erase ga (delta C.theta 1)) (C.point 1).reflect+
      (if ga then NegativePrimary.primaryIncrement (delta C.theta 1) (C.point 2).a (C.point 1).a
        else 0)+Secondary.l+Secondary.l*(C.point 2).y-Secondary.charge*delta C.theta 1 := by
  cases ga
  · simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
      quarterProjection,r92na_bslot,SignedPoint.reflect]
    ring
  · simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
      quarterProjection,r92na_bslot,SignedPoint.reflect,NegativePrimary.primaryIncrement,G,A]
    field_simp
    ring

private theorem r92na_edge_A (hg : Fin 4) (ga ab de eh : Bool) (C : SignedCycle)
    (hA : Real.cos (delta C.theta 2)≠0) :
    weights ga ab C 2*(edgeWidth (delta C.theta 2)-C.edge 2 (owners hg ga ab de eh 2))=
      r92na_aslot Secondary.l (erase ab (delta C.theta 2)) (C.point 3).reflect+
      (if ab then NegativePrimary.primaryIncrement (delta C.theta 2) (C.point 2).a (-(C.point 3).y)
        else 0)+Secondary.l-Secondary.l*(C.point 2).y-Secondary.charge*delta C.theta 2 := by
  cases ab
  · simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
      zeroProjection,r92na_aslot,SignedPoint.reflect]
    ring
  · simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
      zeroProjection,r92na_aslot,SignedPoint.reflect,NegativePrimary.primaryIncrement,A]
    field_simp
    ring

private theorem r92na_edge_B (hg : Fin 4) (ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab C 3*(edgeWidth (delta C.theta 3)-C.edge 3 (owners hg ga ab de eh 3))=
      r92na_bslot 2 0 (C.point 3).reflect+tGain C+2+2*(C.point 4).y-
        Secondary.charge*delta C.theta 3 := by
  simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
    quarterProjection,r92na_bslot,SignedPoint.reflect,tGain,PairedA.work,B,T]
  ring

private theorem r92na_edge_T (hg : Fin 4) (ga ab de eh : Bool) (C : SignedCycle)
    (hT : delta C.theta 4=0) :
    weights ga ab C 4*(edgeWidth (delta C.theta 4)-C.edge 4 (owners hg ga ab de eh 4))=
      r92na_zslot 0 (C.point 5).reflect-2*(C.point 4).y := by
  simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
    zeroProjection,r92na_zslot,SignedPoint.reflect,hT]
  ring

private theorem r92na_edge_D (hg : Fin 4) (ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab C 5*(edgeWidth (delta C.theta 5)-C.edge 5 (owners hg ga ab de eh 5))=
      r92na_dslot (erase de (delta C.theta 5)) (C.point 5).reflect+
      (if de then edgeWidth (delta C.theta 5)-1-((C.point 6).a*Real.sin (delta C.theta 5)+
        (C.point 6).y*(1-Real.cos (delta C.theta 5))) else 0)+
      (C.point 6).y-Secondary.charge*erase de (delta C.theta 5) := by
  cases de <;>
    simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
      quarterProjection,r92na_dslot,SignedPoint.reflect] <;>
    ring

private theorem r92na_edge_E (hg : Fin 4) (ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab C 6*(edgeWidth (delta C.theta 6)-C.edge 6 (owners hg ga ab de eh 6))=
      r92na_bslot 1 (erase eh (delta C.theta 6)) (C.point 0)+
      (if eh then edgeWidth (delta C.theta 6)-1-((C.point 6).a*Real.sin (delta C.theta 6)+
        (C.point 6).y*(Real.cos (delta C.theta 6)-1)) else 0)+
      1-(C.point 6).y-Secondary.charge*erase eh (delta C.theta 6) := by
  cases eh <;>
    simp [NegativePrimary.weights,owners,Paired.Source.owners,SignedCycle.edge,word,next,
      quarterProjection,r92na_bslot] <;>
    ring

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (hG : Real.cos (delta C.theta G)≠0)
    (hA : Real.cos (delta C.theta A)≠0) (hTD : delta C.theta T=0) :
    actualStress C hg ga ab de eh=
      reference C hg ga ab de eh+NegativePrimary.gains ga ab false C+tGain C+
        GlobalGA.Secondary.charge*cycleTotal C de eh+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) := by
  simp only [G,A,T] at hG hA hTD
  have hG' := r92na_edge_G hg ga ab de eh C hG
  have hA' := r92na_edge_A hg ga ab de eh C hA
  have hB' := r92na_edge_B hg ga ab de eh C
  have hT' := r92na_edge_T hg ga ab de eh C hTD
  have hD' := r92na_edge_D hg ga ab de eh C
  have hE' := r92na_edge_E hg ga ab de eh C
  have hs := r92na_delta_sum C
  have hDs : erase de (delta C.theta 5)+PairedE.selected de (delta C.theta 5)=delta C.theta 5 := by
    cases de <;> simp [PairedE.selected]
  have hEs : erase eh (delta C.theta 6)+PairedE.selected eh (delta C.theta 6)=delta C.theta 6 := by
    cases eh <;> simp [PairedE.selected]
  rcases hhg with rfl|rfl
  · have hH' := r92na_edge_H0 ga ab de eh C
    simp only [actualStress,Fin.sum_univ_seven,reference,NegativePrimary.gains,
      r92na_pair_split,r92na_one_split,r92na_d_split,Secondary.baseStress,cycleTotal,
      PairedE.total,primaryGain,Bool.false_eq_true,↓reduceIte,H,G,A,B,D,E]
    linear_combination hH'+hG'+hA'+hB'+hT'+hD'+hE'-Secondary.charge*hs+
      Secondary.charge*hTD-Secondary.charge*(hDs+hEs)
  · have hH' := r92na_edge_H2 ga ab de eh C
    simp only [actualStress,Fin.sum_univ_seven,reference,NegativePrimary.gains,
      r92na_pair_split,r92na_one_split,r92na_d_split,Secondary.baseStress,cycleTotal,
      PairedE.total,primaryGain,Bool.false_eq_true,↓reduceIte,show ((2:Fin 4)=0)=False by decide,
      H,G,A,B,D,E]
    linear_combination hH'+hG'+hA'+hB'+hT'+hD'+hE'-Secondary.charge*hs+
      Secondary.charge*hTD-Secondary.charge*(hDs+hEs)

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
    simp only [reference,↓reduceIte]
    linarith [baseStress_reserve]
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) false eh
    simp only [erase_false] at hhb
    have hH := actual_H_pair hHy (hc H) hq hhb.1 hhb.2
    have hG := actual_G_one (P:=(C.point G).reflect) (x:=erase ga (delta C.theta G))
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq (erase_abs_bound ga (original_error_bound hvar hn G))
    simp only [reference,show ((2:Fin 4)=0)=False by decide,↓reduceIte]
    linarith [baseStress_reserve]

theorem t_gain_lower {C : SignedCycle}
    (hs : (C.point T).Sorted) (hcore : (C.point T).AvoidsCore)
    (hb : delta C.theta B≤0) (hsmall : |delta C.theta B|≤frameCap) :
    (83/700)*(-delta C.theta B)≤tGain C := by
  have hsdom : -delta C.theta B∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hb,(neg_le_abs _).trans hsmall⟩
  have hw := Paired.aligned_work_weak hs hcore hsdom
  have hp := PairedE.phi_chord hsdom
  dsimp [tGain,PositiveAngularEnvelope.phi,GlobalGA.Secondary.charge] at *
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
  simp only [PairedE.Negative.tMagnitude,PairedE.selected,Bool.false_eq_true,↓reduceIte,
    neg_zero,mul_zero,add_zero] at hgain
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
  dsimp only [Secondary.charge] at hu
  have ha0' : 0≤PairedE.Negative.aMagnitude C ga ab := ha0
  linarith [hEmem.1]

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.NegativeA

