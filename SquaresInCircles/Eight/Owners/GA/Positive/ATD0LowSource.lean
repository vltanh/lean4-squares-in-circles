module

public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0ChargedPairs
public import SquaresInCircles.Eight.Owners.GA.Positive.ATD0DSupport
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveSource

/-!
# Eight squares: the positive-A/TD0 low-angle contradiction

The A-primary error is deleted only from the analytic circle block. All other signed errors and all
seven weak axes are kept (`low_actual_false`). The states of A, T and E need neither a sign nor an
outer radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PositiveATD0
namespace Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks SignedStress
open TwoPositive.Source (aError aWork aReserve a_reserve_nonneg)

def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,0,2,0]

def weights (k l c : ℝ) : Vertex→ℝ := ![k,l,l,c,c,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,l,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨l,c,if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨c,1,delta C.theta T,delta C.theta D⟩]

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : ℝ :=
  demand C (weights k l c)-
    ∑i,work (force C (owners hg atG) (weights k l c) i) (C.point i)

def dIncrement (z d : ℝ) (P : SignedPoint) : ℝ :=
  lowC*edgeWidth z+edgeWidth d-(dF z d*P.a+dG z d*P.y)+
    charge*(z+d)-(1+lowC)*(1-GlobalGA.Secondary.diagonal)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) : Fin 4→ℝ :=
  ![pairIncrement lowK lowL (blocks C hg atG lowK lowL lowC 0).u
      (blocks C hg atG lowK lowL lowC 0).v (C.point G).reflect,
    pairIncrement lowK 1 (blocks C hg atG lowK lowL lowC 1).u
      (blocks C hg atG lowK lowL lowC 1).v (C.point H),
    pairIncrement lowL lowC (blocks C hg atG lowK lowL lowC 2).u
      (blocks C hg atG lowK lowL lowC 2).v (C.point B).reflect,
    dIncrement (delta C.theta T) (delta C.theta D) (C.point D).reflect]

theorem weights_nonneg {k l c : ℝ} (hk : 0≤k) (hl : 0≤l) (hc : 0≤c)
    (i : Vertex) : 0≤weights k l c i := by
  fin_cases i <;> simp [weights,hk,hl,hc]

theorem stress_nonpos {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0≤c)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    actualStress C hg atG k l c≤0 := by
  have hf (i : Vertex) : C.Feasible i (owners hg atG i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation (weights_nonneg hk hl hc) hf)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool)
    (hhg : hg=0 ∨ hg=2) :
    actualStress C hg atG lowK lowL lowC=
      lowBaseline+charge*aError C atG+lowL*TwoPositive.ASupport.charge (aError C atG)+
        (∑i,actualBlocks C hg atG i)+aReserve C atG lowL := by
  cases atG <;> rcases hhg with rfl | rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,
      previous,owners,weights,blocks,actualBlocks,pairIncrement,dIncrement,
      pairF,pairG,dF,dG,lowBaseline,aReserve,aWork,aError,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth,lowK,lowL,lowC,charge] <;> ring

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG k l c i).u+f (blocks C hg atG k l c i).v))=
      (∑j,f (delta C.theta j))-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

/-- The primary error removes exactly its positive variation; every other error of the cycle stays
as it is, and none is concentrated. -/
theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG) :
    aError C atG∈Icc 0 frameCap ∧
      (∑i,(blocks C hg atG k l c i).P)≤frameCap-aError C atG ∧
      (∑i,(blocks C hg atG k l c i).N)=aError C atG+∑i,(blocks C hg atG k l c i).P := by
  have hp := sum_parts C hg atG k l c positivePart positivePart_zero
  have hn := sum_parts C hg atG k l c negativePart negativePart_zero
  have hpa : positivePart (aError C atG)=aError C atG := max_eq_left ha
  have hna : negativePart (aError C atG)=0 := max_eq_right (by linarith)
  have hp' : (∑i,(blocks C hg atG k l c i).P)=positiveVariation C.theta-aError C atG := by
    change (∑i,(positivePart (blocks C hg atG k l c i).u+
      positivePart (blocks C hg atG k l c i).v))=_
    simpa only [hpa,positiveVariation] using hp
  have hn' : (∑i,(blocks C hg atG k l c i).N)=negativeVariation C.theta := by
    change (∑i,(negativePart (blocks C hg atG k l c i).u+
      negativePart (blocks C hg atG k l c i).v))=_
    simpa only [hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨ha,by linarith⟩,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG) (i : Fin 4) :
    (blocks C hg atG k l c i).P≤frameCap ∧ (blocks C hg atG k l c i).N≤frameCap := by
  have hb := original_budgets hg atG k l c hvar ha
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith [hb.1.1,hb.2.1,hb.2.2]

theorem actual_blocks_nonneg {q : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aError C atG)
    (i : Fin 4) : 0≤actualBlocks C hg atG i := by
  have hb := block_budgets hg atG lowK lowL lowC hvar ha
  fin_cases i
  · have hh := actual_fixed_pair_nonneg 0 (P:=(C.point G).reflect)
      (a:=(blocks C hg atG lowK lowL lowC 0).u)
      (b:=(blocks C hg atG lowK lowL lowC 0).v)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G) hq (hb 0).1 (hb 0).2
    simpa [actualBlocks,coefficientP,coefficientQ] using hh
  · have hh := actual_fixed_pair_nonneg 1 (P:=C.point H)
      (a:=(blocks C hg atG lowK lowL lowC 1).u)
      (b:=(blocks C hg atG lowK lowL lowC 1).v)
      hHy (hc H) hq (hb 1).1 (hb 1).2
    simpa [actualBlocks,coefficientP,coefficientQ] using hh
  · have hh := actual_fixed_pair_nonneg 2 (P:=(C.point B).reflect)
      (a:=(blocks C hg atG lowK lowL lowC 2).u)
      (b:=(blocks C hg atG lowK lowL lowC 2).v)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B) hq (hb 2).1 (hb 2).2
    simpa [actualBlocks,coefficientP,coefficientQ] using hh
  · have he := pair_error_bounds (hb 3).1 (hb 3).2
    have hh := actual_D_lower (P:=(C.point D).reflect)
      (z:=delta C.theta T) (d:=delta C.theta D)
      (by simpa using hs D)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq he.1 he.2.1 he.2.2
    simpa [actualBlocks,dIncrement,sub_nonneg] using hh

/-- The low-angle exclusion on the cycle. The only hypotheses are the weak owners and the signed
variation of the cycle. -/
theorem low_actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aError C atG∈Icc 0 (1/6:ℝ))
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨hg,hhg,hHG⟩ : ∃hg : Fin 4,(hg=0 ∨ hg=2) ∧ C.Feasible H hg := by
    rcases hHG with hh | hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  have hu := stress_nonpos (k:=lowK) (l:=lowL) (c:=lowC) atG (by norm_num [lowK])
    (by norm_num [lowL]) (by norm_num [lowC]) hHG hGA hAB hBT hTD hDE hEH
  have hb := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => actual_blocks_nonneg atG hs hc hq hHy hGy hBy hDy hvar ha.1 i (hg:=hg))
  have hA := a_reserve_nonneg (l:=lowL) atG (hs A) (hc A) hq (by norm_num [lowL])
    ⟨ha.1,ha.2.trans (by norm_num [frameCap])⟩
  have hp := low_scalar_positive ha
  have he := decomposition C atG hhg
  simp only [lowL,charge] at hp he
  linarith

end Source
open Candidate

end SquaresInCircles.Eight.GlobalGA.PositiveATD0
