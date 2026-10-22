module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTNegativeAESource
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELowAStress

/-!
# Small nonnegative A and negative core E at the BT3 alignment

Uncompiled all-E nonpositive-T fixed-stress branch. Independent negative
DE/EH secants retain their proved actual H/D corrections; the two aligned
T primaries supply the full removed angular charge. The scalar reserve
uses the original A signed total, including opposite individual signs.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.LowE
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

theorem decomposition (C : SignedCycle) (hg ga ab de eh : Bool)
    (hflat : (C.point E).a=7/12) (hTD : delta C.theta T=0)
    (hD : Real.cos (delta C.theta D)≠0) (hE : Real.cos (delta C.theta E)≠0) :
    stress C hg ga ab de eh=reference C hg ga ab de eh+
      L*(PairedE.LowA.aTotal C ga ab-magnitude C D de-magnitude C E eh+delta C.theta B)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      deGain C de+ehGain C eh+tGain C := by
  have hT : C.theta D-C.theta T=0 := by simpa [delta,next,T,D] using hTD
  cases hg <;> cases ga <;> cases ab <;> cases de <;> cases eh <;>
    simp [stress,weights,owners,reference,NegativeELowA.hIncrement,NegativeELowA.dIncrement,
      NegativeELowA.hSecantIncrement,NegativeELowA.dSecantIncrement,deGain,ehGain,
      NegativeELowA.deGain,NegativeELowA.ehGain,tGain,LowA.tGain,PairedA.work,
      NegativeELowA.rawE,magnitude,NegativeELowA.magnitude,erase,selected,hflat,
      SignedCycle.edge,zeroProjection,quarterProjection,Fin.sum_univ_succ,
      word,delta,next,H,G,A,B,T,D,E,PositiveATD0.lowBaseline,
      PositiveATD0.pairIncrement,PositiveATD0.Source.dIncrement,pairF,pairG,
      PositiveATD0.dF,PositiveATD0.dG,PairedE.LowA.aTotal,total,primaryGain,
      edgeWidth,pairWidth,SignedPoint.reflect,k,l,c,L,NegativeELowA.k,NegativeELowA.l,
      NegativeELowA.c,NegativeELowA.L,PositiveATD0.lowK,PositiveATD0.lowL,
      PositiveATD0.lowC,PositiveATD0.charge,hT]
  all_goals
    have hD' : Real.cos (C.theta E-C.theta D)≠0 := hD
    have hE' : Real.cos (C.theta H-C.theta E)≠0 := hE
    have hf : (C.point E).a=7/12 := hflat
    dsimp [E] at hf
    simp only [hf]
    field_simp [hD',hE']
    ring

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
  simp only [PositiveATD0.coefficientP,PositiveATD0.coefficientQ,
    Matrix.cons_val_zero,Matrix.cons_val_succ] at hG hB
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
  dsimp [L,c,NegativeELowA.L,NegativeELowA.c,PositiveATD0.charge,PositiveATD0.lowC] at hu hE hT hscalar
  nlinarith


end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.LowE
