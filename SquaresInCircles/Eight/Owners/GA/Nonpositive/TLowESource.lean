module

public import SquaresInCircles.Eight.Owners.GA.Negative.ELowAStress
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TLowSource

/-!
# Eight squares: small nonnegative A and negative core E at the BT3 alignment

Independent negative
DE/EH secants retain their proved actual H/D corrections; the two aligned
T primaries supply the full removed angular charge. The scalar reserve
uses the original A signed total, including opposite individual signs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.LowE
open Candidate Secondary NegativePrimary PairedE
abbrev k := NegativeELowA.k
abbrev l := NegativeELowA.l
abbrev c := NegativeELowA.c
abbrev L := NegativeELowA.L
abbrev magnitude := NegativeELowA.magnitude
abbrev deGain := NegativeELowA.deGain
abbrev ehGain := NegativeELowA.ehGain
abbrev tGain := LowA.tGain

def owners (hg ga ab de eh : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,
    3,2,if de then 3 else 2,if eh then 1 else 0]
def weights (C : SignedCycle) (de eh : Bool) : Vertex→ℝ :=
  ![k,l,l,c,c,if de then 1/Real.cos (delta C.theta D) else 1,
    if eh then 1/Real.cos (delta C.theta E) else 1]
def stress (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  ∑i,weights C de eh i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab de eh i))
def reference (C : SignedCycle) (hg ga ab de eh : Bool) : ℝ :=
  PositiveATD0.lowBaseline+NegativeELowA.hIncrement C hg eh+
    PositiveATD0.pairIncrement k l (erase hg (delta C.theta H))
      (erase ga (delta C.theta G)) (C.point G).reflect+
    PositiveATD0.pairIncrement l c (erase ab (delta C.theta A))
      0 (C.point B).reflect+NegativeELowA.dIncrement C true de

private theorem r92lw_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lw_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92lw_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92lw_edge_zero C 0 j (by decide)
private theorem r92lw_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92lw_edge_quarter C 1 j (by decide)
private theorem r92lw_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92lw_edge_zero C 2 j (by decide)
private theorem r92lw_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92lw_edge_quarter C 3 j (by decide)
private theorem r92lw_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92lw_edge_zero C 4 j (by decide)
private theorem r92lw_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92lw_edge_quarter C 5 j (by decide)
private theorem r92lw_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92lw_edge_quarter C 6 j (by decide)

private theorem r92lw_delta_sum (C : SignedCycle) :
    delta C.theta 0+delta C.theta 1+delta C.theta 2+delta C.theta 3+
      delta C.theta 4+delta C.theta 5+delta C.theta 6=0 := by
  simp only [delta,next]
  norm_num

private def r92lw_u (α u : ℝ) (P : SignedPoint) : ℝ :=
  α*(edgeWidth u-1)-α*Real.sin u*P.a-α*Real.cos u*P.y
private def r92lw_v (β v : ℝ) (P : SignedPoint) : ℝ :=
  β*(edgeWidth v-1)-β*Real.cos v*P.a-β*Real.sin v*P.y

private theorem r92lw_pinc (p q a b : ℝ) (P : SignedPoint) :
    PositiveATD0.pairIncrement p q a b P=
      r92lw_u p a P+r92lw_v q b P+fullSupport q p+PositiveATD0.charge*a+PositiveATD0.charge*b := by
  simp only [PositiveATD0.pairIncrement,pairF,pairG,r92lw_u,r92lw_v]
  ring

theorem decomposition (C : SignedCycle) (hg ga ab de eh : Bool)
    (hflat : (C.point E).a=7/12) (hTD : delta C.theta T=0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) :
    stress C hg ga ab de eh=reference C hg ga ab de eh+
      L*(PairedE.LowA.aTotal C ga ab-magnitude C D de-magnitude C E eh+delta C.theta B)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C := by
  have hsum := r92lw_delta_sum C
  have hT4 : delta C.theta 4=0 := hTD
  have hE6 : (C.point 6).a=7/12 := hflat
  have hinvD : Real.cos (delta C.theta 5)*(Real.cos (delta C.theta 5))⁻¹=1 :=
    mul_inv_cancel₀ hD
  have hinvE : Real.cos (delta C.theta 6)*(Real.cos (delta C.theta 6))⁻¹=1 :=
    mul_inv_cancel₀ hE
  have h1 : stress C hg ga ab de eh=
      k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))+
      l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))+
      l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))+
      c*(edgeWidth (delta C.theta B)-C.edge B 3)+c*(edgeWidth (delta C.theta T)-C.edge T 2)+
      (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))+
      (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0)) := by
    simp only [stress,Fin.sum_univ_seven,weights,owners,Matrix.cons_val,H,G,A,B,T,D,E]
  have hH : k*(edgeWidth (delta C.theta H)-C.edge H (if hg then 2 else 0))=
      r92lw_u k (erase (!hg) (delta C.theta H)) (C.point H)+
      r92lw_u k (erase hg (delta C.theta H)) (C.point G).reflect+k := by
    cases hg <;>
      simp only [r92lw_u,r92lw_e0,H,G,zeroProjection,erase,SignedPoint.reflect,Bool.not_true,
        Bool.not_false,Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hG : l*(edgeWidth (delta C.theta G)-C.edge G (if ga then 3 else 2))=
      r92lw_v l (erase ga (delta C.theta G)) (C.point G).reflect+
      l*(if ga then edgeWidth (delta C.theta G)-1-((C.point A).a*
        Real.sin (delta C.theta G)+(C.point A).y*(1-Real.cos (delta C.theta G))) else 0)+
      l+l*(C.point A).y := by
    cases ga <;>
      simp only [r92lw_v,r92lw_e1,G,A,quarterProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hA : l*(edgeWidth (delta C.theta A)-C.edge A (if ab then 2 else 0))=
      r92lw_u l (erase ab (delta C.theta A)) (C.point B).reflect+
      l*(if ab then edgeWidth (delta C.theta A)-1-((C.point A).a*
        Real.sin (delta C.theta A)+(C.point A).y*(Real.cos (delta C.theta A)-1)) else 0)+
      l-l*(C.point A).y := by
    cases ab <;>
      simp only [r92lw_u,r92lw_e2,A,B,zeroProjection,erase,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero] <;>
      ring
  have hB : c*(edgeWidth (delta C.theta B)-C.edge B 3)=
      r92lw_v c 0 (C.point B).reflect+tGain C+c+c*(C.point T).y := by
    simp only [r92lw_v,r92lw_e3,B,T,quarterProjection,tGain,LowA.tGain,PairedA.work,
      SignedPoint.reflect,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
    ring
  have hT : c*(edgeWidth (delta C.theta T)-C.edge T 2)=
      c*(1-(C.point T).y+(C.point D).y) := by
    simp only [r92lw_e4,T,D,zeroProjection,hT4,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
      edgeWidth_zero]
    ring
  have hDv : (if de then 1/Real.cos (delta C.theta D) else 1)*
        (edgeWidth (delta C.theta D)-C.edge D (if de then 3 else 2))=
      NegativeELowA.dIncrement C true de+deGain C de-L*magnitude C D de+(C.point E).y-c-
        c*(C.point D).y-L*delta C.theta D+(1+c)*(1-Secondary.diagonal) := by
    cases de
    · simp only [r92lw_e5,D,E,quarterProjection,NegativeELowA.dIncrement,deGain,
        NegativeELowA.deGain,magnitude,NegativeELowA.magnitude,selected,erase_true,
        PositiveATD0.Source.dIncrement,PositiveATD0.dF,PositiveATD0.dG,SignedPoint.reflect,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,
        edgeWidth_zero]
      ring
    · simp only [r92lw_e5,D,E,quarterProjection,NegativeELowA.dIncrement,deGain,
        NegativeELowA.deGain,magnitude,NegativeELowA.magnitude,selected,erase_true,
        NegativeELowA.dSecantIncrement,NegativeELowA.rawE,SignedPoint.reflect,hE6,
        ↓reduceIte,Matrix.cons_val,Real.sin_zero,Real.cos_zero,edgeWidth_zero]
      linear_combination (C.point 6).y*hinvD
  have hEv : (if eh then 1/Real.cos (delta C.theta E) else 1)*
        (edgeWidth (delta C.theta E)-C.edge E (if eh then 1 else 0))=
      NegativeELowA.hIncrement C hg eh-r92lw_u k (erase (!hg) (delta C.theta H)) (C.point H)-
        fullSupport 1 k-L*erase (!hg) (delta C.theta H)-L*delta C.theta E+ehGain C eh-
        L*magnitude C E eh+1-(C.point E).y := by
    cases eh
    · simp only [r92lw_e6,E,H,quarterProjection,NegativeELowA.hIncrement,ehGain,
        NegativeELowA.ehGain,magnitude,NegativeELowA.magnitude,selected,r92lw_pinc,r92lw_v,
        Bool.false_eq_true,↓reduceIte,Matrix.cons_val]
      ring
    · simp only [r92lw_e6,E,H,quarterProjection,NegativeELowA.hIncrement,ehGain,
        NegativeELowA.ehGain,magnitude,NegativeELowA.magnitude,selected,
        NegativeELowA.hSecantIncrement,NegativeELowA.rawE,r92lw_u,hE6,↓reduceIte,Matrix.cons_val]
      linear_combination -(C.point 6).y*hinvE
  have hHs : erase (!hg) (delta C.theta H)+erase hg (delta C.theta H)=delta C.theta H := by
    cases hg <;> simp
  have hGs : erase ga (delta C.theta G)+selected ga (delta C.theta G)=delta C.theta G := by
    cases ga <;> simp [selected]
  have hAs : erase ab (delta C.theta A)+selected ab (delta C.theta A)=delta C.theta A := by
    cases ab <;> simp [selected]
  rw [h1,hH,hG,hA,hB,hT,hDv,hEv]
  simp only [reference,PositiveATD0.lowBaseline,r92lw_pinc,PairedE.LowA.aTotal,total,
    primaryGain]
  simp only [H,G,A,B,T,D,E] at hHs hGs hAs ⊢
  linear_combination (-L)*hHs+(-L)*hGs+(-L)*hAs+(-L)*hsum+L*hT4

theorem reference_lower {q : ℝ} {C : SignedCycle} (hg ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) :
    PositiveATD0.lowBaseline≤reference C hg ga ab de eh := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hgb := erased_pair_budgets (i := H) (j := G) hvar hn (by norm_num [H,G]) hg ga
  have hbb := erased_pair_budgets (i := A) (j := B) hvar hn (by norm_num [A,B]) ab true
  simp only [erase_true] at hbb
  have hG := PositiveATD0.actual_fixed_pair_nonneg 0 (P := (C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq hgb.1 hgb.2
  have hB := PositiveATD0.actual_fixed_pair_nonneg 2 (P := (C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hH := NegativeELowA.hIncrement_nonneg hg eh (hc H) hq hHy hvar heh
  have hD := NegativeELowA.dIncrement_nonneg true de (hs D) (hc D) hq hDy hvar hde
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,Matrix.cons_val] at hG hB
  dsimp [reference,k,l,c,NegativeELowA.k,NegativeELowA.l,NegativeELowA.c]
  linarith

theorem actual_false {q : ℝ} {C : SignedCycle} (ga ab de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hcoreT : (C.point T).AvoidsCore) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hflat : (C.point E).a=7/12) (hvar : positiveVariation C.theta≤frameCap)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (ha : PairedE.LowA.aTotal C ga ab∈Icc 0 (1/6:ℝ))
    (hb : delta C.theta B≤0) (htd : delta C.theta T=0)
    (hde : de=true→delta C.theta D≤0)
    (heh : eh=true→-delta C.theta E∈Icc 0 (1/4:ℝ)) : False := by
  obtain ⟨hg,hHG⟩ : ∃hg : Bool,C.Feasible H (if hg then 2 else 0) := by
    rcases hHG with hh|hh
    · exact ⟨false,hh⟩
    · exact ⟨true,hh⟩
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsmall (i : Vertex) := original_error_bound hvar hn i
  have hcos (i : Vertex) := NegativePrimary.cos_pos (hsmall i)
  have hTpos := hcos T
  have hDpos := hcos D
  have hEpos := hcos E
  have hweights (i : Vertex) : 0≤weights C de eh i := by
    cases de <;> cases eh <;> fin_cases i <;>
      simp [weights,k,l,c,NegativeELowA.k,NegativeELowA.l,NegativeELowA.c,PositiveATD0.lowK,PositiveATD0.lowL,PositiveATD0.lowC]
    all_goals positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  have hu : stress C hg ga ab de eh≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hh := hf i
    change 0≤C.edge i (owners hg ga ab de eh i)-edgeWidth (delta C.theta i) at hh
    exact mul_nonpos_of_nonneg_of_nonpos (hweights i) (by linarith)
  have hreference := reference_lower hg ga ab de eh hs hc hq hHy hGy hBy hDy hvar hde heh
  have hAmem : PairedE.LowA.aTotal C ga ab∈Icc 0 frameCap :=
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hA := selected_charge ga ab (hs A) (hc A) hq (hsmall G) (hsmall A) hAmem
  have hAweighted := mul_le_mul_of_nonneg_left hA (show 0≤l by norm_num [l,PositiveATD0.lowL])
  have hscalar := PositiveATD0.low_scalar_positive ha
  have hE := NegativeELowA.e_gain_lower de eh hsmall hde heh
  have hT := LowA.t_gain_lower (hs T) hcoreT hb (hsmall B)
  rw [decomposition C hg ga ab de eh hflat htd (hcos D).ne' (hcos E).ne'] at hu
  change l*TwoPositive.ASupport.charge (PairedE.LowA.aTotal C ga ab)≤_ at hAweighted
  dsimp only [L,c,l,NegativeELowA.L,NegativeELowA.c,NegativeELowA.l,magnitude,deGain,ehGain,
    tGain,PositiveATD0.charge,PositiveATD0.lowL] at hu hE hT hscalar hAweighted
  linarith


end SquaresInCircles.Eight.GlobalGA.NonpositiveT.LowE
