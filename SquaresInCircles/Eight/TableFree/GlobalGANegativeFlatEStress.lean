module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEChargedPairs
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEDSupport
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEOtherGains
public import SquaresInCircles.Eight.TableFree.GlobalGANegativePrimaryReserve

/-!
# Exact simultaneous negative A, T, and flat-core-E force collection

Uncompiled transcription of Section 5 of the negative-flat-E note.
The five independent flags retain GA3, AB2, TD2, DE3, and EH1. Only
the comparison expression erases their arguments. Each E primary has
its own actual secant multiplier, and their signed E terms cancel.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
open Candidate Secondary
open NegativePrimary (erase erase_positive_le erase_negative_le erase_abs_bound erased_pair_budgets)

def owners (hg ga ab td de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    2,if td then 2 else 0,if de then 3 else 2,if eh then 1 else 0]

def weights (ga ab de eh : Bool) (C : SignedCycle) : Vertex→ℝ :=
  ![lowK,if ga then lowL/Real.cos (delta C.theta G) else lowL,
    if ab then lowL/Real.cos (delta C.theta A) else lowL,lowC,lowC,
    if de then 1/Real.cos (delta C.theta D) else 1,
    if eh then 1/Real.cos (delta C.theta E) else 1]

def stress (hg ga ab td de eh : Bool) (C : SignedCycle) : ℝ :=
  ∑i,weights ga ab de eh C i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab td de eh i))

def dIncrement (z d : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth z+edgeWidth d-(dF z d*P.a+dG z d*P.y)+charge*(z+d)-
    (1+lowC)*(1-diagonal)

def reference (hg ga ab td de eh : Bool) (C : SignedCycle) : ℝ :=
  lowBaseline+
    pairIncrement lowK lowL (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    pairIncrement lowK 1 (erase (!hg) (delta C.theta H))
      (erase eh (delta C.theta E)) (C.point H)+
    pairIncrement lowL lowC (erase ab (delta C.theta A))
      (delta C.theta B) (C.point B).reflect+
    dIncrement (erase td (delta C.theta T)) (erase de (delta C.theta D)) (C.point D).reflect

def gains (ga ab td de eh : Bool) (C : SignedCycle) : ℝ :=
  (if ga then primaryGain (delta C.theta G) (C.point A).a (C.point G).a+
    charge*delta C.theta G else 0)+
  (if ab then primaryGain (delta C.theta A) (C.point A).a (-(C.point B).y)+
    charge*delta C.theta A else 0)+
  (if td then tdGain (delta C.theta T) (C.point T)+charge*delta C.theta T else 0)+
  (if de then eGain (delta C.theta D) (C.point D).a+charge*delta C.theta D else 0)+
  (if eh then eGain (delta C.theta E) (C.point H).a+charge*delta C.theta E else 0)

theorem weights_nonneg (ga ab de eh : Bool) (C : SignedCycle)
    (hsmall : ∀i,|delta C.theta i|≤frameCap) : ∀i,0≤weights ga ab de eh C i := by
  have hG := NegativePrimary.cos_pos (hsmall G)
  have hA := NegativePrimary.cos_pos (hsmall A)
  have hD := NegativePrimary.cos_pos (hsmall D)
  have hE := NegativePrimary.cos_pos (hsmall E)
  intro i
  cases ga <;> cases ab <;> cases de <;> cases eh <;> fin_cases i <;>
    simp [weights,lowK,lowL,lowC] <;> positivity

theorem stress_nonpos {hg ga ab td de eh : Bool} {C : SignedCycle}
    (hsmall : ∀i,|delta C.theta i|≤frameCap)
    (hf : ∀i,C.Feasible i (owners hg ga ab td de eh i)) :
    stress hg ga ab td de eh C≤0 := by
  apply Finset.sum_nonpos
  intro i _
  have hi := hf i
  change 0≤C.edge i (owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hi
  exact mul_nonpos_of_nonneg_of_nonpos (weights_nonneg ga ab de eh C hsmall i) (by linarith)

theorem decomposition (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point E).a=7/12)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) :
    stress hg ga ab td de eh C=reference hg ga ab td de eh C+gains ga ab td de eh C := by
  cases hg <;> cases ga <;> cases ab <;> cases td <;> cases de <;> cases eh <;>
    simp [stress,weights,owners,reference,gains,erase,hflat,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,lowBaseline,pairIncrement,pairF,pairG,
      dIncrement,dF,dG,primaryGain,tdGain,eGain,edgeWidth,pairWidth,SignedPoint.reflect,
      lowK,lowL,lowC,charge]
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

theorem reference_reserve {q : ℝ} {C : SignedCycle} (hg ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) : baseline<reference hg ga ab td de eh C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [←variations_equal]
  have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) hg ga
  have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) (!hg) eh
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td de
  simp only [NegativePrimary.erase_false] at hbb
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
  dsimp [reference,dIncrement,baseline]
  linarith [low_baseline_reserve]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
