module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTNegativeASource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEExclusion

/-!
# Simultaneous negative A/E primaries at the negative-BT3 alignment

Uncompiled fixed-stress branch of the all-E nonpositive-T note. Both
negative E secants retain the original core-E cancellation. The actual
aligned T pair adds a nonnegative charged gain to the already proved
negative A/E reserve; no inherited marker is applied to the moved point.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.NegativeAE
open Candidate Secondary NegativeFlatE
open NegativePrimary (erase erase_positive_le erase_negative_le erase_abs_bound erased_pair_budgets)

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    3,2,if de then 3 else 2,if eh then 1 else 0]

abbrev weights := NegativeFlatE.weights

def stress (hg ga ab de eh : Bool) (C : SignedCycle) : ℝ :=
  ∑i,weights ga ab de eh C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))

abbrev dIncrement := NegativeFlatE.dIncrement

def reference (hg ga ab de eh : Bool) (C : SignedCycle) : ℝ :=
  lowBaseline+
    NegativeFlatE.pairIncrement lowK lowL (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    NegativeFlatE.pairIncrement lowK 1 (erase (!hg) (delta C.theta H))
      (erase eh (delta C.theta E)) (C.point H)+
    NegativeFlatE.pairIncrement lowL lowC (erase ab (delta C.theta A))
      0 (C.point B).reflect+
    dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) : ℝ :=
  lowC*PairedA.work (C.point T) (delta C.theta B) 0+NegativeFlatE.charge*delta C.theta B

def gains (ga ab de eh : Bool) (C : SignedCycle) : ℝ :=
  NegativeFlatE.gains ga ab false de eh C+tGain C

abbrev weights_nonneg := NegativeFlatE.weights_nonneg

theorem stress_nonpos {hg ga ab de eh : Bool} {C : SignedCycle}
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab de eh i)) :
    stress hg ga ab de eh C≤0 := by
  apply Finset.sum_nonpos
  intro i _
  have hi := hf i
  change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at hi
  exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab de eh C hsmall i) (by linarith)

private def r92ae_aslot (p x : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth x-1)-p*Real.sin x*P.a-p*Real.cos x*P.y+NegativeFlatE.charge*x

private def r92ae_bslot (q x : ℝ) (P : SignedPoint) : ℝ :=
  q*(edgeWidth x-1)-q*Real.cos x*P.a-q*Real.sin x*P.y+NegativeFlatE.charge*x

private def r92ae_zslot (x : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth x-lowC*Real.sin x*P.a-lowC*Real.cos x*P.y+NegativeFlatE.charge*x

private def r92ae_dslot (x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-Real.cos x*P.a-Real.sin x*P.y+NegativeFlatE.charge*x

private theorem r92ae_pair_split (p q a b : ℝ) (P : SignedPoint) :
    NegativeFlatE.pairIncrement p q a b P=r92ae_aslot p a P+r92ae_bslot q b P+fullSupport q p := by
  simp only [NegativeFlatE.pairIncrement,pairF,pairG,r92ae_aslot,r92ae_bslot]
  ring

private theorem r92ae_d_split (z d : ℝ) (P : SignedPoint) :
    NegativeFlatE.dIncrement z d P=
      r92ae_zslot z P+r92ae_dslot d P-(1+lowC)*(1-GlobalGA.Secondary.diagonal) := by
  simp only [NegativeFlatE.dIncrement,NegativeFlatE.dF,NegativeFlatE.dG,r92ae_zslot,r92ae_dslot]
  ring

private theorem r92ae_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private theorem r92ae_edge_H (hg ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 0*(edgeWidth (delta C.theta 0)-C.edge 0 (owners hg ga ab de eh 0))=
      r92ae_aslot lowK (erase hg (delta C.theta 0)) (C.point 1).reflect+
      r92ae_aslot lowK (erase (!hg) (delta C.theta 0)) (C.point 0)+lowK-NegativeFlatE.charge*delta C.theta 0 := by
  cases hg <;>
    simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_aslot,
      SignedPoint.reflect] <;> ring

private theorem r92ae_edge_G (hg ga ab de eh : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta 1)≠0) :
    weights ga ab de eh C 1*(edgeWidth (delta C.theta 1)-C.edge 1 (owners hg ga ab de eh 1))=
      r92ae_bslot lowL (erase ga (delta C.theta 1)) (C.point 1).reflect+
      (if ga then NegativeFlatE.primaryGain (delta C.theta 1) (C.point 2).a (C.point 1).a+
        NegativeFlatE.charge*delta C.theta 1 else 0)+lowL+lowL*(C.point 2).y-NegativeFlatE.charge*delta C.theta 1 := by
  cases ga
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
      SignedPoint.reflect]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
      SignedPoint.reflect,NegativeFlatE.primaryGain,G,A]
    field_simp
    ring

private theorem r92ae_edge_A (hg ga ab de eh : Bool) (C : SignedCycle)
    (hA : Real.cos (delta C.theta 2)≠0) :
    weights ga ab de eh C 2*(edgeWidth (delta C.theta 2)-C.edge 2 (owners hg ga ab de eh 2))=
      r92ae_aslot lowL (erase ab (delta C.theta 2)) (C.point 3).reflect+
      (if ab then NegativeFlatE.primaryGain (delta C.theta 2) (C.point 2).a (-(C.point 3).y)+
        NegativeFlatE.charge*delta C.theta 2 else 0)+lowL-lowL*(C.point 2).y-NegativeFlatE.charge*delta C.theta 2 := by
  cases ab
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_aslot,
      SignedPoint.reflect]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_aslot,
      SignedPoint.reflect,NegativeFlatE.primaryGain,G,A]
    field_simp
    ring

private theorem r92ae_edge_B (hg ga ab de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 3*(edgeWidth (delta C.theta 3)-C.edge 3 (owners hg ga ab de eh 3))=
      r92ae_bslot lowC 0 (C.point 3).reflect+tGain C+lowC+lowC*(C.point 4).y-
        NegativeFlatE.charge*delta C.theta 3 := by
  simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
    SignedPoint.reflect,tGain,PairedA.work,B,T]
  ring

private theorem r92ae_edge_T (hg ga ab de eh : Bool) (C : SignedCycle)
    (hT : delta C.theta 4=0) :
    weights ga ab de eh C 4*(edgeWidth (delta C.theta 4)-C.edge 4 (owners hg ga ab de eh 4))=
      r92ae_zslot 0 (C.point 5).reflect-lowC*(C.point 4).y := by
  simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,zeroProjection,r92ae_zslot,
    SignedPoint.reflect,hT]
  ring

private theorem r92ae_edge_D (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hD : Real.cos (delta C.theta 5)≠0) :
    weights ga ab de eh C 5*(edgeWidth (delta C.theta 5)-C.edge 5 (owners hg ga ab de eh 5))=
      r92ae_dslot (erase de (delta C.theta 5)) (C.point 5).reflect+
      (if de then NegativeFlatE.eGain (delta C.theta 5) (C.point 5).a+NegativeFlatE.charge*delta C.theta 5 else 0)+
        (C.point 6).y-NegativeFlatE.charge*delta C.theta 5 := by
  cases de
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_dslot,
      SignedPoint.reflect]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_dslot,
      SignedPoint.reflect,NegativeFlatE.eGain,hflat,D]
    field_simp
    ring

private theorem r92ae_edge_E (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hE : Real.cos (delta C.theta 6)≠0) :
    weights ga ab de eh C 6*(edgeWidth (delta C.theta 6)-C.edge 6 (owners hg ga ab de eh 6))=
      r92ae_bslot 1 (erase eh (delta C.theta 6)) (C.point 0)+
      (if eh then NegativeFlatE.eGain (delta C.theta 6) (C.point 0).a+NegativeFlatE.charge*delta C.theta 6 else 0)+
        1-(C.point 6).y-NegativeFlatE.charge*delta C.theta 6 := by
  cases eh
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot]
    ring
  · simp [NegativeFlatE.weights,owners,SignedCycle.edge,word,next,quarterProjection,r92ae_bslot,
      NegativeFlatE.eGain,hflat,E]
    field_simp
    ring

theorem decomposition (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point E).a=7/12)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) (hTD : delta C.theta T=0) :
    stress hg ga ab de eh C=reference hg ga ab de eh C+gains ga ab de eh C := by
  simp only [G,A,D,E,T] at hflat hG hA hD hE hTD
  have hH' := r92ae_edge_H hg ga ab de eh C
  have hG' := r92ae_edge_G hg ga ab de eh C hG
  have hA' := r92ae_edge_A hg ga ab de eh C hA
  have hB' := r92ae_edge_B hg ga ab de eh C
  have hT' := r92ae_edge_T hg ga ab de eh C hTD
  have hD' := r92ae_edge_D hg ga ab de eh C hflat hD
  have hE' := r92ae_edge_E hg ga ab de eh C hflat hE
  have hs := r92ae_delta_sum C
  simp only [stress,Fin.sum_univ_seven,reference,gains,NegativeFlatE.gains,r92ae_pair_split,
    dIncrement,r92ae_d_split,lowBaseline,Bool.false_eq_true,↓reduceIte,H,G,A,B,D,E]
  linear_combination hH'+hG'+hA'+hB'+hT'+hD'+hE'-NegativeFlatE.charge*hs+NegativeFlatE.charge*hTD

theorem reference_reserve {q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) : baseline<reference hg ga ab de eh C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) hg ga
  have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) (!hg) eh
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab true
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) true de
  simp only [NegativePrimary.erase_true] at hbb hdb
  have hG := actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G) hq hgb.1 hgb.2
  have hH := actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
  have hB := actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B) hq hbb.1 hbb.2
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := NegativeFlatE.actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  simp only [coefficientP,coefficientQ,Matrix.cons_val] at hG hH hB
  have hL := low_baseline_reserve
  dsimp only [reference,dIncrement,NegativeFlatE.dIncrement,baseline]
  have hsum := add_nonneg (add_nonneg (add_nonneg hG hH) hB) (sub_nonneg.mpr hD)
  exact lt_of_lt_of_le hL (le_of_le_of_eq (le_add_of_nonneg_right hsum) (by ring))

theorem t_gain_nonneg {C : SignedCycle} (hs : (C.point T).Sorted)
    (hcore : (C.point T).AvoidsCore) (hb : delta C.theta B≤0)
    (hsmall : |delta C.theta B|≤frameCap) : 0≤tGain C := by
  have hsdom : -delta C.theta B∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hb,(neg_le_abs _).trans hsmall⟩
  have hw := Paired.aligned_work_weak hs hcore hsdom
  have hp := td_arc_charge hsdom
  have hh := mul_le_mul_of_nonneg_left hw (show 0≤lowC by norm_num [lowC])
  dsimp [PositiveAngularEnvelope.phi] at hh
  simp only [neg_neg] at hh
  dsimp only [tGain]
  dsimp only [NegativeFlatE.charge,NegativeFlatE.lowC] at hp hh ⊢
  linarith [hsdom.1]

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcore : ∀i,(C.point i).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2)) (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2)) (hEH : C.Feasible E (if eh then 1 else 0))
    (hga : ga=true→delta C.theta G≤0) (hab : ab=true→delta C.theta A≤0)
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hde : de=true→delta C.theta D≤0) (heh : eh=true→delta C.theta E≤0) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu := stress_nonpos hsmall hf
  have hr := reference_reserve hg ga ab de eh hs hc hQ hHy hGy hBy hDy hvar
  have hgain := NegativeFlatE.gains_reserve ga ab false de eh hs hc hcore hQ hvar hga hab
    (by simp) hde heh
  have htg := t_gain_nonneg (hs T) (hcore T) hb (hsmall B)
  have hid := decomposition hg ga ab de eh C hflat
    (NegativePrimary.cos_pos (hsmall G)).ne' (NegativePrimary.cos_pos (hsmall A)).ne'
    (NegativePrimary.cos_pos (hsmall D)).ne' (NegativePrimary.cos_pos (hsmall E)).ne' htd
  rw [hid] at hu
  dsimp [gains] at hu
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.NegativeAE

