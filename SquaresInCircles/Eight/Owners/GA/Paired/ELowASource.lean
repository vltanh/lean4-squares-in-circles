module

public import SquaresInCircles.Eight.Owners.GA.Paired.ENegativeSource
public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0LowSource

/-!
# Eight squares: nonnegative E total with a small nonnegative A total

Both original primary pairs allow opposite individual signs. The
reference deletes only their selected angular arguments, retains an
arbitrary actual TD0 error, and uses the original TD2 secant multiplier
when that owner has nonpositive error. All points are unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PairedE.LowA
open Candidate Secondary NegativePrimary

def aTotal (C : SignedCycle) (ga ab : Bool) : ℝ :=
  total ga ab (delta C.theta G) (delta C.theta A)

def weights (C : SignedCycle) (td : Bool) : Vertex→ℝ :=
  ![PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowL,PositiveATD0.lowC,
    if td then PositiveATD0.lowC/Real.cos (delta C.theta T) else PositiveATD0.lowC,1,1]

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab td de eh : Bool) : ℝ :=
  ∑i,weights C td i*(edgeWidth (delta C.theta i)-C.edge i (Negative.owners hg ga ab td de eh i))

def reference (C : SignedCycle) (hg : Fin 4) (ga ab td de eh : Bool) : ℝ :=
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
      (erase ab (delta C.theta A)) (delta C.theta B) (C.point B).reflect+
    PositiveATD0.Source.dIncrement (erase td (delta C.theta T))
      (erase de (delta C.theta D)) (C.point D).reflect

def tGain (C : SignedCycle) (td : Bool) : ℝ :=
  if td then PositiveANegativeTD.gain PositiveATD0.lowC (-delta C.theta T)
    (C.point T).a (-(C.point D).y) else 0

private theorem r80_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r80_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r80_eH (C : SignedCycle) (j : Fin 4) :
    C.edge H j=zeroProjection (C.point H) (C.point G) (delta C.theta H) j :=
  r80_edge_zero C H j (by decide)
private theorem r80_eG (C : SignedCycle) (j : Fin 4) :
    C.edge G j=quarterProjection (C.point G) (C.point A) (delta C.theta G) j :=
  r80_edge_quarter C G j (by decide)
private theorem r80_eA (C : SignedCycle) (j : Fin 4) :
    C.edge A j=zeroProjection (C.point A) (C.point B) (delta C.theta A) j :=
  r80_edge_zero C A j (by decide)
private theorem r80_eB (C : SignedCycle) (j : Fin 4) :
    C.edge B j=quarterProjection (C.point B) (C.point T) (delta C.theta B) j :=
  r80_edge_quarter C B j (by decide)
private theorem r80_eT (C : SignedCycle) (j : Fin 4) :
    C.edge T j=zeroProjection (C.point T) (C.point D) (delta C.theta T) j :=
  r80_edge_zero C T j (by decide)
private theorem r80_eD (C : SignedCycle) (j : Fin 4) :
    C.edge D j=quarterProjection (C.point D) (C.point E) (delta C.theta D) j :=
  r80_edge_quarter C D j (by decide)
private theorem r80_eE (C : SignedCycle) (j : Fin 4) :
    C.edge E j=quarterProjection (C.point E) (C.point H) (delta C.theta E) j :=
  r80_edge_quarter C E j (by decide)

private theorem r80_delta_sum (C : SignedCycle) :
    delta C.theta H+delta C.theta G+delta C.theta A+delta C.theta B+
      delta C.theta T+delta C.theta D+delta C.theta E=0 := by
  simp only [delta,next,H,G,A,B,T,D,E]
  norm_num

/-- The selected T error must be nonpositive: for a positive selected T error the
secant weight leaves `lowC*tan (delta T)` unaccounted. -/
theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab td de eh : Bool)
    (hhg : hg=0∨hg=2) (hcos : Real.cos (delta C.theta T)≠0)
    (hsmall : |delta C.theta T|≤frameCap) (htd : td=true→delta C.theta T≤0) :
    actualStress C hg ga ab td de eh=
      reference C hg ga ab td de eh+
        PositiveATD0.charge*(aTotal C ga ab+cycleTotal C de eh-Negative.tMagnitude C td)+
        PositiveATD0.lowL*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
        primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E)+tGain C td := by
  have hsum := r80_delta_sum C
  have h1 : actualStress C hg ga ab td de eh=
      PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H hg)+
      PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 2)+
      (if td then PositiveATD0.lowC/Real.cos (delta C.theta T) else PositiveATD0.lowC)*
        (edgeWidth (delta C.theta T)-C.edge T (if td then 2 else 0))+
      (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [actualStress,Fin.sum_univ_seven,weights,Negative.owners,Matrix.cons_val,
      H,G,A,B,T,D,E]
    ring
  have hG (a : ℝ) : PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G 2)+
      (PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL a
          (erase ga (delta C.theta G)) (C.point G).reflect-
        PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL a
          (delta C.theta G) (C.point G).reflect)+
      PositiveATD0.charge*selected ga (delta C.theta G)+
      PositiveATD0.lowL*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0) := by
    cases ga
    · simp [erase,selected]
    · simp only [r80_eG,quarterProjection,PositiveATD0.pairIncrement,pairF,pairG,erase,selected,
        SignedPoint.reflect,Matrix.cons_val,↓reduceIte,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hA : PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A 0)+
      (PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
          (erase ab (delta C.theta A)) (delta C.theta B) (C.point B).reflect-
        PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
          (delta C.theta A) (delta C.theta B) (C.point B).reflect)+
      PositiveATD0.charge*selected ab (delta C.theta A)+
      PositiveATD0.lowL*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0) := by
    cases ab
    · simp [erase,selected]
    · simp only [r80_eA,zeroProjection,PositiveATD0.pairIncrement,pairF,pairG,erase,selected,
        SignedPoint.reflect,Matrix.cons_val,↓reduceIte,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hT (z : ℝ) : (if td then PositiveATD0.lowC/Real.cos (delta C.theta T) else PositiveATD0.lowC)*
        (edgeWidth (delta C.theta T)-C.edge T (if td then 2 else 0))=
      PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 0)+
      (PositiveATD0.Source.dIncrement (erase td (delta C.theta T)) z (C.point D).reflect-
        PositiveATD0.Source.dIncrement (delta C.theta T) z (C.point D).reflect)+
      PositiveATD0.charge*(-Negative.tMagnitude C td)+tGain C td := by
    cases htd' : td
    · simp [erase,Negative.tMagnitude,selected,tGain]
    · have hz := htd htd'
      have hc : 0<Real.cos (delta C.theta T) := NegativePrimary.cos_pos hsmall
      have hlow : -(7/10:ℝ)≤delta C.theta T := by
        have h1 := neg_abs_le (delta C.theta T)
        have h2 := hsmall
        simp only [frameCap] at h2
        linarith
      have hs : Real.sin (delta C.theta T)≤0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hz
        (by linarith [Real.pi_gt_three])
      have hw : edgeWidth (delta C.theta T)=
          (1-Real.sin (delta C.theta T)+Real.cos (delta C.theta T))/2 := by
        rw [edgeWidth,pairWidth,abs_of_nonpos hs,abs_of_pos hc]
        ring
      simp only [r80_eT,zeroProjection,PositiveATD0.Source.dIncrement,PositiveATD0.dF,
        PositiveATD0.dG,erase,Negative.tMagnitude,selected,tGain,PositiveANegativeTD.gain,
        SignedPoint.reflect,Matrix.cons_val,↓reduceIte,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero,Real.sin_neg,Real.cos_neg,hw]
      field_simp
      ring
  have hD (z : ℝ) : edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2)=
      (edgeWidth (delta C.theta D)-C.edge D 2)+
      (PositiveATD0.Source.dIncrement z (erase de (delta C.theta D)) (C.point D).reflect-
        PositiveATD0.Source.dIncrement z (delta C.theta D) (C.point D).reflect)+
      PositiveATD0.charge*selected de (delta C.theta D)+
      (if de then edgeWidth (delta C.theta D)-1-((C.point E).a*Real.sin (delta C.theta D)+
        (C.point E).y*(1-Real.cos (delta C.theta D))) else 0) := by
    cases de
    · simp [erase,selected]
    · simp only [r80_eD,quarterProjection,PositiveATD0.Source.dIncrement,PositiveATD0.dF,
        PositiveATD0.dG,erase,selected,SignedPoint.reflect,Matrix.cons_val,↓reduceIte,
        Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  have hE (b : ℝ) : edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)=
      (edgeWidth (delta C.theta E)-C.edge E 0)+
      (PositiveATD0.pairIncrement PositiveATD0.lowK 1 b (erase eh (delta C.theta E)) (C.point H)-
        PositiveATD0.pairIncrement PositiveATD0.lowK 1 b (delta C.theta E) (C.point H))+
      PositiveATD0.charge*selected eh (delta C.theta E)+
      (if eh then edgeWidth (delta C.theta E)-1-((C.point E).a*Real.sin (delta C.theta E)+
        (C.point E).y*(Real.cos (delta C.theta E)-1)) else 0) := by
    cases eh
    · simp [erase,selected]
    · simp only [r80_eE,quarterProjection,PositiveATD0.pairIncrement,pairF,pairG,erase,selected,
        Matrix.cons_val,↓reduceIte,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      ring
  rcases hhg with rfl|rfl
  · have hbase : PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H 0)+
        PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G 2)+
        PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A 0)+
        PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 2)+
        PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 0)+
        (edgeWidth (delta C.theta D)-C.edge D 2)+(edgeWidth (delta C.theta E)-C.edge E 0)=
        PositiveATD0.lowBaseline+
          (PositiveATD0.pairIncrement PositiveATD0.lowK 1 0 (delta C.theta E) (C.point H)+
            PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL (delta C.theta H)
              (delta C.theta G) (C.point G).reflect)+
          PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
            (delta C.theta A) (delta C.theta B) (C.point B).reflect+
          PositiveATD0.Source.dIncrement (delta C.theta T) (delta C.theta D) (C.point D).reflect := by
      simp only [r80_eH,r80_eG,r80_eA,r80_eB,r80_eT,r80_eD,r80_eE,zeroProjection,
        quarterProjection,PositiveATD0.pairIncrement,pairF,pairG,PositiveATD0.Source.dIncrement,
        PositiveATD0.dF,PositiveATD0.dG,PositiveATD0.lowBaseline,SignedPoint.reflect,
        Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      linear_combination (-PositiveATD0.charge)*hsum
    rw [h1,hG (delta C.theta H),hA,hT (erase de (delta C.theta D)),hD (delta C.theta T),hE 0]
    simp only [reference,↓reduceIte,aTotal,cycleTotal,total,primaryGain]
    linear_combination hbase
  · have hbase : PositiveATD0.lowK*(edgeWidth (delta C.theta H)-C.edge H 2)+
        PositiveATD0.lowL*(edgeWidth (delta C.theta G)-C.edge G 2)+
        PositiveATD0.lowL*(edgeWidth (delta C.theta A)-C.edge A 0)+
        PositiveATD0.lowC*(edgeWidth (delta C.theta B)-C.edge B 2)+
        PositiveATD0.lowC*(edgeWidth (delta C.theta T)-C.edge T 0)+
        (edgeWidth (delta C.theta D)-C.edge D 2)+(edgeWidth (delta C.theta E)-C.edge E 0)=
        PositiveATD0.lowBaseline+
          (PositiveATD0.pairIncrement PositiveATD0.lowK 1 (delta C.theta H) (delta C.theta E)
              (C.point H)+
            PositiveATD0.pairIncrement PositiveATD0.lowK PositiveATD0.lowL 0
              (delta C.theta G) (C.point G).reflect)+
          PositiveATD0.pairIncrement PositiveATD0.lowL PositiveATD0.lowC
            (delta C.theta A) (delta C.theta B) (C.point B).reflect+
          PositiveATD0.Source.dIncrement (delta C.theta T) (delta C.theta D) (C.point D).reflect := by
      simp only [r80_eH,r80_eG,r80_eA,r80_eB,r80_eT,r80_eD,r80_eE,zeroProjection,
        quarterProjection,PositiveATD0.pairIncrement,pairF,pairG,PositiveATD0.Source.dIncrement,
        PositiveATD0.dF,PositiveATD0.dG,PositiveATD0.lowBaseline,SignedPoint.reflect,
        Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      linear_combination (-PositiveATD0.charge)*hsum
    rw [h1,hG 0,hA,hT (erase de (delta C.theta D)),hD (delta C.theta T),hE (delta C.theta H)]
    simp only [reference,show ((2:Fin 4)=0)=False by decide,↓reduceIte,aTotal,cycleTotal,total,
      primaryGain]
    linear_combination hbase

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg : Fin 4)
    (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    PositiveATD0.lowBaseline≤reference C hg ga ab td de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hB
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td de
  have hde := pair_error_bounds hdb.1 hdb.2
  have hd := PositiveATD0.actual_D_lower (P:=(C.point D).reflect)
    (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  have hD : 0≤PositiveATD0.Source.dIncrement (erase td (delta C.theta T))
      (erase de (delta C.theta D)) (C.point D).reflect := by
    simp only [PositiveATD0.Source.dIncrement]
    linarith
  by_cases hhg : hg=0
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) true eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) false ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hH hG
    rw [reference,ite_eq_left hhg]
    linarith
  · have hhb := erased_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E]) false eh
    have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) true ga
    simp only [erase_true,erase_false] at hhb hgb
    have hH := PositiveATD0.actual_fixed_pair_nonneg 1 hHy (hc H) hq hhb.1 hhb.2
    have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq hgb.1 hgb.2
    simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hH hG
    rw [reference,ite_eq_right hhg]
    linarith

theorem t_gain_lower {q : ℝ} {C : SignedCycle} (td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcore : (C.point T).AvoidsCore) (hq : q≤qCap) (hDy : (C.point D).y≤0)
    (hsmall : |delta C.theta T|≤frameCap) (htd : td=true→delta C.theta T≤0) :
    (9/10)*PositiveATD0.lowC*Negative.tMagnitude C td≤tGain C td := by
  cases hh : td
  · simp [tGain,Negative.tMagnitude,selected]
  · have hz : -delta C.theta T∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr (htd hh),(neg_le_abs _).trans hsmall⟩
    simpa [tGain,Negative.tMagnitude,selected] using PositiveANegativeTD.actual_gain_lower
      (hs T) hcore (hc T) (hs D) hDy (hc D) hq
      (show 0≤PositiveATD0.lowC by norm_num [PositiveATD0.lowC]) hz

/-- The selected A and E totals include both original errors when both
primaries occur; neither individual sign is restricted. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab td de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T (if td then 2 else 0))
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (htd : td=true→delta C.theta T≤0) (he : 0≤cycleTotal C de eh) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos : 0<Real.cos (delta C.theta T) := NegativePrimary.cos_pos (hsmall T)
  have hweights (i : Vertex) : 0≤weights C td i := by
    have hs : 0≤PositiveATD0.lowC/Real.cos (delta C.theta T) :=
      div_nonneg (by norm_num [PositiveATD0.lowC]) hcos.le
    cases td <;> fin_cases i <;>
      simp [weights,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC,hs] <;> norm_num
  have hf (i : Vertex) : C.Feasible i (Negative.owners hg ga ab td de eh i) := by
    fin_cases i
    · simpa [Negative.owners,H] using hHG
    · simpa [Negative.owners,G] using hGA
    · simpa [Negative.owners,A] using hAB
    · simpa [Negative.owners,B] using hBT
    · simpa [Negative.owners,T] using hTD
    · simpa [Negative.owners,D] using hDE
    · simpa [Negative.owners,E] using hEH
  have hu : actualStress C hg ga ab td de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (Negative.owners hg ga ab td de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab td de eh hs hc hq hHy hGy hBy hDy hvar
  have hAmem : aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hAcharge := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hAcharge
    (show 0≤PositiveATD0.lowL by norm_num [PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hEmem := cycle_total_bounds de eh hvar he
  have hEcharge := selected_charge de eh (hs E) (hc E) hq (hsmall D) (hsmall E) hEmem
  have hElinear := charge_linear hEmem
  have hTgain := t_gain_lower td hs hc hcoreT hq hDy (hsmall T) htd
  have ht0 : 0≤Negative.tMagnitude C td := by
    cases hh : td
    · simp [Negative.tMagnitude,selected]
    · simpa [Negative.tMagnitude,selected] using neg_nonneg.mpr (htd hh)
  rw [decomposition C ga ab td de eh hhg hcos.ne' (hsmall T) htd] at hu
  change PositiveATD0.lowL*TwoPositive.ASupport.charge (aTotal C ga ab)≤_ at hAweighted
  change TwoPositive.ASupport.charge (cycleTotal C de eh)≤_ at hEcharge
  simp only [PositiveATD0.charge,PositiveATD0.lowC,PositiveATD0.lowL] at hu hscalar hTgain hAweighted
  linarith [hEmem.1]

end SquaresInCircles.Eight.GlobalGA.PairedE.LowA
