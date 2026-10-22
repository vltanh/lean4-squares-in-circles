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
    pairIncrement lowK lowL (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    pairIncrement lowK 1 (erase (!hg) (delta C.theta H))
      (erase eh (delta C.theta E)) (C.point H)+
    pairIncrement lowL lowC (erase ab (delta C.theta A))
      0 (C.point B).reflect+
    dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) : ℝ :=
  lowC*PairedA.work (C.point T) (delta C.theta B) 0+charge*delta C.theta B

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

theorem decomposition (hg ga ab de eh : Bool) (C : SignedCycle)
    (hflat : (C.point E).a=7/12)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) (hTD : delta C.theta T=0) :
    stress hg ga ab de eh C=reference hg ga ab de eh C+gains ga ab de eh C := by
  have hT : C.theta D-C.theta T=0 := by simpa [delta,next,T,D] using hTD
  cases hg <;> cases ga <;> cases ab <;> cases de <;> cases eh <;>
    simp [stress,weights,NegativeFlatE.weights,owners,reference,gains,NegativeFlatE.gains,tGain,PairedA.work,erase,hflat,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,lowBaseline,pairIncrement,pairF,pairG,
      dIncrement,NegativeFlatE.dIncrement,dF,dG,primaryGain,tdGain,eGain,edgeWidth,pairWidth,SignedPoint.reflect,
      lowK,lowL,lowC,charge,hT]
  all_goals
    have hG' : Real.cos (C.theta A-C.theta G)≠0 := hG
    have hA' : Real.cos (C.theta B-C.theta A)≠0 := hA
    have hD' : Real.cos (C.theta E-C.theta D)≠0 := hD
    have hE' : Real.cos (C.theta H-C.theta E)≠0 := hE
    have hflat' : (C.point E).a=7/12 := hflat
    dsimp [E] at hflat'
    simp only [hflat']
    field_simp [hG',hA',hD',hE']
    ring

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
  have hD := actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  simp only [coefficientP,coefficientQ,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ] at hG hH hB
  dsimp [reference,dIncrement,NegativeFlatE.dIncrement,baseline]
  linarith [low_baseline_reserve]

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
  dsimp [tGain]
  linarith

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
  have hg := NegativeFlatE.gains_reserve ga ab false de eh hs hc hcore hQ hvar hga hab
    (by simp) hde heh
  have htg := t_gain_nonneg (hs T) (hcore T) hb (hsmall B)
  have hid := decomposition hg ga ab de eh C hflat
    (NegativePrimary.cos_pos (hsmall G)).ne' (NegativePrimary.cos_pos (hsmall A)).ne'
    (NegativePrimary.cos_pos (hsmall D)).ne' (NegativePrimary.cos_pos (hsmall E)).ne' htd
  rw [hid] at hu
  dsimp [gains] at hu
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.NegativeAE

