module

public import SquaresInCircles.Eight.Owners.GA.Nonpositive.THighSource
public import SquaresInCircles.Eight.Owners.GA.Paired.ELowASource

/-!
# Eight squares: the small A-total fixed stress with an aligned negative BT3

The same charged four-circle
reference deletes both original T arguments analytically. Its actual
T gain dominates the complete angular charge on [0,h]. The original
signed A/E pair support comparisons retain every selected primary tie.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LowA
open Candidate Secondary NegativePrimary
open PairedE (cycleTotal primaryGain selected_charge cycle_total_bounds charge_linear)

abbrev aTotal := PairedE.LowA.aTotal
abbrev owners := Paired.Source.owners

def weights : Vertex→ℝ :=
  ![PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowL,PositiveATD0.lowC,
    PositiveATD0.lowC,1,1]
def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) : ℝ :=
  ∑i,weights i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))
def reference (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) : ℝ :=
  PositiveATD0.lowBaseline+
    (if hg=0 then
      PositiveATD0.pairIncrement PositiveATD0.lowK 1 0
        (erase eh (delta C.theta E)) (C.point H)+
      PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL (delta C.theta H)
        (erase ga (delta C.theta G)) (C.point G).reflect
    else
      PositiveATD0.pairIncrement PositiveATD0.lowK 1 (delta C.theta H)
        (erase eh (delta C.theta E)) (C.point H)+
      PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL 0
        (erase ga (delta C.theta G)) (C.point G).reflect)+
    PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
      (erase ab (delta C.theta A)) 0 (C.point B).reflect+
    PositiveATD0.Source.dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) : ℝ :=
  PositiveATD0.lowC*PairedA.work (C.point T) (delta C.theta B) 0

private theorem r92lo_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lo_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lo_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92lo_edge_zero C 0 j (by decide)
private theorem r92lo_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92lo_edge_quarter C 1 j (by decide)
private theorem r92lo_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92lo_edge_zero C 2 j (by decide)
private theorem r92lo_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92lo_edge_quarter C 3 j (by decide)
private theorem r92lo_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92lo_edge_zero C 4 j (by decide)
private theorem r92lo_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92lo_edge_quarter C 5 j (by decide)
private theorem r92lo_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92lo_edge_quarter C 6 j (by decide)

private theorem r92lo_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private def r92lo_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92lo_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92lo_pinc (p q a b : ℝ) (P : SignedPoint) :
    PositiveATD0.pairIncrement p q a b P=
      r92lo_u p a P+r92lo_v q b P+fullSupport q p+PositiveATD0.charge*a+PositiveATD0.charge*b := by
  simp only [PositiveATD0.pairIncrement,pairF,pairG,r92lo_u,r92lo_v]
  ring

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (hTD : delta C.theta T=0) :
    actualStress C hg ga ab de eh=
      reference C hg ga ab de eh+
        PositiveATD0.charge*(aTotal C ga ab+cycleTotal C de eh+delta C.theta B)+
        PositiveATD0.lowL*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E)+tGain C := by
  have hsum := r92lo_delta_sum C
  have hT4 : delta C.theta 4=0 := hTD
  have h1 : actualStress C hg ga ab de eh=
      PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H hg)+
      PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 3)+
      PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 2)+
      1*(edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [actualStress,Fin.sum_univ_seven,weights,owners,Paired.Source.owners,
      Matrix.cons_val,H,G,A,B,T,D,E]
  have hG : PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92lo_v PositiveATD0.lowL (erase ga (delta C.theta G)) (C.point G).reflect+
      PositiveATD0.lowL*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      PositiveATD0.lowL+PositiveATD0.lowL*(C.point A).y := by
    cases ga <;>
      simp only [r92lo_v,r92lo_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92lo_u PositiveATD0.lowL (erase ab (delta C.theta A)) (C.point B).reflect+
      PositiveATD0.lowL*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      PositiveATD0.lowL-PositiveATD0.lowL*(C.point A).y := by
    cases ab <;>
      simp only [r92lo_u,r92lo_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hB : PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92lo_v PositiveATD0.lowC 0 (C.point B).reflect+tGain C+PositiveATD0.lowC+
        PositiveATD0.lowC*(C.point T).y := by
    simp only [r92lo_v,r92lo_e3,B,T,quarterProjection,tGain,PairedA.work,
      SignedPoint.reflect,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hT : PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 2)=
      PositiveATD0.lowC*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92lo_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : 1*(edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      PositiveATD0.Source.dIncrement 0 (erase de (delta C.theta D)) (C.point D).reflect+
      (if de then edgeWidth (delta C.theta D)-1-((C.point E).a*Real.sin (delta C.theta D)+
        (C.point E).y*(1-Real.cos (delta C.theta D))) else 0)+
      (C.point E).y-PositiveATD0.lowC-PositiveATD0.lowC*(C.point D).y+
      (1+PositiveATD0.lowC)*(1-Secondary.diagonal)-
      PositiveATD0.charge*erase de (delta C.theta D) := by
    cases de <;>
      simp only [r92lo_e5,D,E,quarterProjection,PositiveATD0.Source.dIncrement,PositiveATD0.dF,
        PositiveATD0.dG,erase,SignedPoint.reflect,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero] <;>
      ring
  have hEv : 1*(edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      r92lo_v 1 (erase eh (delta C.theta E)) (C.point H)+
      (if eh then edgeWidth (delta C.theta E)-1-((C.point E).a*Real.sin (delta C.theta E)+
        (C.point E).y*(Real.cos (delta C.theta E)-1)) else 0)+1-(C.point E).y := by
    cases eh <;>
      simp only [r92lo_v,r92lo_e6,E,H,quarterProjection,erase,Bool.false_eq_true,↓reduceIte,
        Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero] <;>
      ring
  have hGs : erase ga (delta C.theta G)+PairedE.selected ga (delta C.theta G)=delta C.theta G := by
    cases ga <;> simp [PairedE.selected]
  have hAs : erase ab (delta C.theta A)+PairedE.selected ab (delta C.theta A)=delta C.theta A := by
    cases ab <;> simp [PairedE.selected]
  have hDs : erase de (delta C.theta D)+PairedE.selected de (delta C.theta D)=delta C.theta D := by
    cases de <;> simp [PairedE.selected]
  have hEs : erase eh (delta C.theta E)+PairedE.selected eh (delta C.theta E)=delta C.theta E := by
    cases eh <;> simp [PairedE.selected]
  rw [h1,hG,hA,hB,hT,hDv,hEv]
  rcases hhg with rfl|rfl
  · have hH : PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H 0)=
        r92lo_u PositiveATD0.lowK 0 (C.point H)+
        r92lo_u PositiveATD0.lowK (delta C.theta H) (C.point G).reflect+PositiveATD0.lowK := by
      simp only [r92lo_u,r92lo_e0,H,G,zeroProjection,SignedPoint.reflect,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
    rw [hH]
    simp only [reference,PositiveATD0.lowBaseline,r92lo_pinc,aTotal,PairedE.LowA.aTotal,
      cycleTotal,PairedE.total,primaryGain,↓reduceIte]
    simp only [H,G,A,B,T,D,E] at hGs hAs hDs hEs ⊢
    linear_combination (-PositiveATD0.charge)*(hGs+hAs+hDs+hEs+hsum)+PositiveATD0.charge*hT4
  · have hH : PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H 2)=
        r92lo_u PositiveATD0.lowK (delta C.theta H) (C.point H)+
        r92lo_u PositiveATD0.lowK 0 (C.point G).reflect+PositiveATD0.lowK := by
      simp only [r92lo_u,r92lo_e0,H,G,zeroProjection,SignedPoint.reflect,Matrix.cons_val,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
    rw [hH]
    simp only [reference,PositiveATD0.lowBaseline,r92lo_pinc,aTotal,PairedE.LowA.aTotal,
      cycleTotal,PairedE.total,primaryGain,show ((2:Fin 4)=0)=False by decide,↓reduceIte]
    simp only [H,G,A,B,T,D,E] at hGs hAs hDs hEs ⊢
    linear_combination (-PositiveATD0.charge)*(hGs+hAs+hDs+hEs+hsum)+PositiveATD0.charge*hT4

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg : Fin 4)
    (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    PositiveATD0.lowBaseline≤reference C hg ga ab de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab true
  simp only [erase_true] at hbb
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
    Matrix.cons_val] at hB
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) true de
  simp only [erase_true] at hdb
  have hde := pair_error_bounds hdb.1 hdb.2
  have hd := PositiveATD0.actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  have hD : 0≤PositiveATD0.Source.dIncrement 0
      (erase de (delta C.theta D)) (C.point D).reflect := by
    simpa [PositiveATD0.Source.dIncrement,sub_nonneg] using hd
  by_cases hhg : hg=0
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) true eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) false ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
      Matrix.cons_val] at hH hG
    simp only [reference,hhg,↓reduceIte]
    linarith
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) false eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) true ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
      Matrix.cons_val] at hH hG
    simp only [reference,hhg,↓reduceIte]
    linarith

theorem t_gain_lower {C : SignedCycle}
    (hs : (C.point T).Sorted) (hcore : (C.point T).AvoidsCore)
    (hB : delta C.theta B≤0) (hsmall : |delta C.theta B|≤frameCap) :
    (PositiveATD0.charge+19/875)*(-delta C.theta B)≤tGain C := by
  let s : ℝ := -delta C.theta B
  have hsdom : s∈Icc 0 frameCap := ⟨neg_nonneg.mpr hB,(neg_le_abs _).trans hsmall⟩
  have hw := Paired.aligned_work_weak hs hcore hsdom
  have hp := PairedE.phi_chord hsdom
  have hh := mul_le_mul_of_nonneg_left hw
    (show 0≤PositiveATD0.lowC by norm_num [PositiveATD0.lowC])
  dsimp [tGain,PositiveAngularEnvelope.phi,PositiveATD0.charge,PositiveATD0.lowC,s] at *
  simp only [neg_neg] at hh
  linarith

theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0) (he : 0≤cycleTotal C de eh) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hweights (i : Vertex) : 0≤weights i := by
    fin_cases i <;> norm_num [weights,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC]
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
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab de eh hs hc hQ hHy hGy hBy hDy hvar
  have hAmem : aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hAcharge := selected_charge ga ab (hs A) (hc A) hQ (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hAcharge
    (show 0≤PositiveATD0.lowL by norm_num [PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hEmem := cycle_total_bounds de eh hvar he
  have hEcharge := selected_charge de eh (hs E) (hc E) hQ (hsmall D) (hsmall E) hEmem
  have hElinear := charge_linear hEmem
  have hTgain := t_gain_lower (hs T) hcoreT hb (hsmall B)
  rw [decomposition C ga ab de eh hhg htd] at hu
  change PositiveATD0.lowL*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAweighted
  change TwoPositive.ASupport.charge (cycleTotal C de eh)≤_ at hEcharge
  dsimp only [PositiveATD0.charge,PositiveATD0.lowL] at hu hscalar hTgain hAweighted
  linarith [hEmem.1]

end LowA

namespace Paired.Source
open Candidate Secondary
open NonnegativeTotals.Source (aTotal eTotal)

/-- All selected nonnegative A/E totals at the actual negative-BT3
TD-alignment endpoint; the small and large scalar ranges are exhaustive. -/
theorem actual_false {Q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hsort : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained Q)
    (hcoreT : (C.point T).AvoidsCore) (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  by_cases hlow : total C ga ab de eh≤L
  · have hA : LowA.aTotal C ga ab=aTotal C ga ab := rfl
    have haLow : LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ) :=
      ⟨hA ▸ ha,by dsimp [total,L] at hlow; linarith⟩
    exact LowA.actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
      hvar hHG hGA hAB hBT hTD hDE hEH haLow hb htd he
  · exact high_actual_false ga ab de eh hsort hc hcoreT hQ hHy hGy hBy hDy
      hvar ha he hb htd (lt_of_not_ge hlow).le hHG hGA hAB hBT hTD hDE hEH

end Paired.Source
end SquaresInCircles.Eight.GlobalGA.NonpositiveT

