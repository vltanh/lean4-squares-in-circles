module

public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EChargedPairs
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EDSupport
public import SquaresInCircles.Eight.Owners.GA.Negative.Flat.EOtherGains
public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Reserve

/-!
# Eight squares: exact simultaneous negative A, T, and flat-core-E force collection

The five independent flags retain GA3, AB2, TD2, DE3, and EH1. Only
the comparison expression erases their arguments. Each E primary has
its own actual secant multiplier, and their signed E terms cancel.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeFlatE
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
    (1+lowC)*(1-GlobalGA.Secondary.diagonal)

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

/-! Edge-by-edge form of the collection.  Each original separator term
equals its own slots of the comparison expression, its own gain, and a
flag-free remainder; the remainders cancel around the cycle. -/

private def r43_aslot (p x : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth x-1)-p*Real.sin x*P.a-p*Real.cos x*P.y+charge*x

private def r43_bslot (q x : ℝ) (P : SignedPoint) : ℝ :=
  q*(edgeWidth x-1)-q*Real.cos x*P.a-q*Real.sin x*P.y+charge*x

private def r43_zslot (x : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth x-lowC*Real.sin x*P.a-lowC*Real.cos x*P.y+charge*x

private def r43_dslot (x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-Real.cos x*P.a-Real.sin x*P.y+charge*x

private theorem r43_pair_split (p q a b : ℝ) (P : SignedPoint) :
    pairIncrement p q a b P=r43_aslot p a P+r43_bslot q b P+fullSupport q p := by
  simp only [pairIncrement,pairF,pairG,r43_aslot,r43_bslot]
  ring

private theorem r43_d_split (z d : ℝ) (P : SignedPoint) :
    dIncrement z d P=r43_zslot z P+r43_dslot d P-(1+lowC)*(1-GlobalGA.Secondary.diagonal) := by
  simp only [dIncrement,dF,dG,r43_zslot,r43_dslot]
  ring

private theorem r43_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private theorem r43_edge_H (hg ga ab td de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 0*(edgeWidth (delta C.theta 0)-C.edge 0 (owners hg ga ab td de eh 0))=
      r43_aslot lowK (erase hg (delta C.theta 0)) (C.point 1).reflect+
      r43_aslot lowK (erase (!hg) (delta C.theta 0)) (C.point 0)+lowK-charge*delta C.theta 0 := by
  cases hg <;>
    simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_aslot,
      SignedPoint.reflect] <;> ring

private theorem r43_edge_G (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hG : Real.cos (delta C.theta 1)≠0) :
    weights ga ab de eh C 1*(edgeWidth (delta C.theta 1)-C.edge 1 (owners hg ga ab td de eh 1))=
      r43_bslot lowL (erase ga (delta C.theta 1)) (C.point 1).reflect+
      (if ga then primaryGain (delta C.theta 1) (C.point 2).a (C.point 1).a+
        charge*delta C.theta 1 else 0)+lowL+lowL*(C.point 2).y-charge*delta C.theta 1 := by
  cases ga
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,
      SignedPoint.reflect]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,
      SignedPoint.reflect,primaryGain,G,A]
    field_simp
    ring

private theorem r43_edge_A (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hA : Real.cos (delta C.theta 2)≠0) :
    weights ga ab de eh C 2*(edgeWidth (delta C.theta 2)-C.edge 2 (owners hg ga ab td de eh 2))=
      r43_aslot lowL (erase ab (delta C.theta 2)) (C.point 3).reflect+
      (if ab then primaryGain (delta C.theta 2) (C.point 2).a (-(C.point 3).y)+
        charge*delta C.theta 2 else 0)+lowL-lowL*(C.point 2).y-charge*delta C.theta 2 := by
  cases ab
  · simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_aslot,
      SignedPoint.reflect]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_aslot,
      SignedPoint.reflect,primaryGain,G,A]
    field_simp
    ring

private theorem r43_edge_B (hg ga ab td de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 3*(edgeWidth (delta C.theta 3)-C.edge 3 (owners hg ga ab td de eh 3))=
      r43_bslot lowC (delta C.theta 3) (C.point 3).reflect+lowC+lowC*(C.point 4).y-
        charge*delta C.theta 3 := by
  simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,
    SignedPoint.reflect]
  ring

private theorem r43_edge_T (hg ga ab td de eh : Bool) (C : SignedCycle) :
    weights ga ab de eh C 4*(edgeWidth (delta C.theta 4)-C.edge 4 (owners hg ga ab td de eh 4))=
      r43_zslot (erase td (delta C.theta 4)) (C.point 5).reflect+
      (if td then tdGain (delta C.theta 4) (C.point 4)+charge*delta C.theta 4 else 0)-
        lowC*(C.point 4).y-charge*delta C.theta 4 := by
  cases td <;>
    simp [weights,owners,SignedCycle.edge,word,next,zeroProjection,r43_zslot,
      SignedPoint.reflect,tdGain] <;> ring

private theorem r43_edge_D (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hD : Real.cos (delta C.theta 5)≠0) :
    weights ga ab de eh C 5*(edgeWidth (delta C.theta 5)-C.edge 5 (owners hg ga ab td de eh 5))=
      r43_dslot (erase de (delta C.theta 5)) (C.point 5).reflect+
      (if de then eGain (delta C.theta 5) (C.point 5).a+charge*delta C.theta 5 else 0)+
        (C.point 6).y-charge*delta C.theta 5 := by
  cases de
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_dslot,
      SignedPoint.reflect]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_dslot,
      SignedPoint.reflect,eGain,hflat,D]
    field_simp
    ring

private theorem r43_edge_E (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point 6).a=7/12) (hE : Real.cos (delta C.theta 6)≠0) :
    weights ga ab de eh C 6*(edgeWidth (delta C.theta 6)-C.edge 6 (owners hg ga ab td de eh 6))=
      r43_bslot 1 (erase eh (delta C.theta 6)) (C.point 0)+
      (if eh then eGain (delta C.theta 6) (C.point 0).a+charge*delta C.theta 6 else 0)+
        1-(C.point 6).y-charge*delta C.theta 6 := by
  cases eh
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot]
    ring
  · simp [weights,owners,SignedCycle.edge,word,next,quarterProjection,r43_bslot,eGain,hflat,E]
    field_simp
    ring

theorem decomposition (hg ga ab td de eh : Bool) (C : SignedCycle)
    (hflat : (C.point E).a=7/12)
    (hG : Real.cos (delta C.theta G)≠0) (hA : Real.cos (delta C.theta A)≠0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) :
    stress hg ga ab td de eh C=reference hg ga ab td de eh C+gains ga ab td de eh C := by
  simp only [G,A,D,E] at hflat hG hA hD hE
  have hH' := r43_edge_H hg ga ab td de eh C
  have hG' := r43_edge_G hg ga ab td de eh C hG
  have hA' := r43_edge_A hg ga ab td de eh C hA
  have hB' := r43_edge_B hg ga ab td de eh C
  have hT' := r43_edge_T hg ga ab td de eh C
  have hD' := r43_edge_D hg ga ab td de eh C hflat hD
  have hE' := r43_edge_E hg ga ab td de eh C hflat hE
  have hs := r43_delta_sum C
  simp only [stress,Fin.sum_univ_seven,reference,gains,r43_pair_split,r43_d_split,lowBaseline,
    H,G,A,B,T,D,E]
  linear_combination hH'+hG'+hA'+hB'+hT'+hD'+hE'-charge*hs

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
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] at hG hH hB
  have hL := low_baseline_reserve
  dsimp only [reference,dIncrement,baseline]
  have hsum := add_nonneg (add_nonneg (add_nonneg hG hH) hB) (sub_nonneg.mpr hD)
  exact lt_of_lt_of_le hL (le_of_le_of_eq (le_add_of_nonneg_right hsum) (by ring))

end SquaresInCircles.Eight.GlobalGA.NegativeFlatE
