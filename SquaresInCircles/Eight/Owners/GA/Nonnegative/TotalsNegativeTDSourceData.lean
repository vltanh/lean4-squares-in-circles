module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDData
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsStress

/-!
# Eight squares: the original negative TD2 error and both selected primary totals

The
TD multiplier is its own secant. Deleting the negative TD argument
removes exactly s of negative variation; deleting either signed A/E
pair removes its actual positive and negative parts, not its absolute sum.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativePrimary (erase)
open NonnegativeTotals.Source (aTotal eTotal selectedSum)

abbrev owners := NonnegativeTotals.Source.owners

def total (C : SignedCycle) (ga ab de eh : Bool) : ℝ := aTotal C ga ab+eTotal C de eh

def weights (C : SignedCycle) (ε : ℝ) : Vertex→ℝ :=
  ![k ε,l ε,l ε,c,c/Real.cos (delta C.theta T),1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : Fin 4→ActualOrdinaryBlocks.Block :=
  ![⟨k ε,1,if hg=0 then 0 else delta C.theta H,erase eh (delta C.theta E)⟩,
    ⟨k ε,l ε,if hg=0 then delta C.theta H else 0,erase ga (delta C.theta G)⟩,
    ⟨l ε,c,erase ab (delta C.theta A),delta C.theta B⟩,
    ⟨k ε,1,erase de (delta C.theta D),0⟩]

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh ε 2) (C.point B).reflect,
    PositiveTD.actualDIncrement c (erase de (delta C.theta D)) (C.point D).reflect]

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) : ℝ :=
  demand C (weights C ε)-∑i,work (force C (owners hg ga ab de eh) (weights C ε) i) (C.point i)

private theorem r92nd_edge_zero (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i=0) :
    C.edge i j=zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92nd_edge_quarter (C : SignedCycle) (i : Vertex) (j : Fin 4) (h : word i≠0) :
    C.edge i j=quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j := by
  simp [SignedCycle.edge,h]

private theorem r92nd_e0 (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j :=
  r92nd_edge_zero C 0 j (by decide)
private theorem r92nd_e1 (C : SignedCycle) (j : Fin 4) :
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j :=
  r92nd_edge_quarter C 1 j (by decide)
private theorem r92nd_e2 (C : SignedCycle) (j : Fin 4) :
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j :=
  r92nd_edge_zero C 2 j (by decide)
private theorem r92nd_e3 (C : SignedCycle) (j : Fin 4) :
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j :=
  r92nd_edge_quarter C 3 j (by decide)
private theorem r92nd_e4 (C : SignedCycle) (j : Fin 4) :
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j :=
  r92nd_edge_zero C 4 j (by decide)
private theorem r92nd_e5 (C : SignedCycle) (j : Fin 4) :
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j :=
  r92nd_edge_quarter C 5 j (by decide)
private theorem r92nd_e6 (C : SignedCycle) (j : Fin 4) :
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j :=
  r92nd_edge_quarter C 6 j (by decide)

/-- The decomposition with the T term left in its general form: the secant weight
of T leaves the residual `c*((|sin s|-sin s)+(|cos s|-cos s))/(2*cos s)`, which vanishes
exactly when `sin s≥0` and `cos s>0`. -/
private theorem r92_decomposition_residual (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) {s ε : ℝ} (hd : delta C.theta T=-s)
    (hcos : Real.cos s≠0) :
    actualStress C hg ga ab de eh ε=base ε+
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,actualBlocks C hg ga ab de eh ε i)+PositiveANegativeTD.gain c s (C.point T).a (-(C.point D).y)+
      NonnegativeTotals.Source.aReserve C ga ab (l ε)+NonnegativeTotals.Source.eReserve C de eh+
      c*((|Real.sin s|-Real.sin s)+(|Real.cos s|-Real.cos s))/(2*Real.cos s) := by
  have hd4 : delta C.theta 4=-s := hd
  have hw : edgeWidth (-s)=(1+|Real.sin s|+|Real.cos s|)/2 := by
    rw [edgeWidth_neg,edgeWidth,pairWidth]
  have hinv : Real.cos s*(Real.cos s)⁻¹=1 := mul_inv_cancel₀ hcos
  have hclip : clippedSupport 1 c=(1+c)*Secondary.diagonal := by
    rw [clippedSupport,ite_eq_left (by norm_num [c]),diagonalSupport]
  rw [actualStress,demand,←sum_force_work]
  cases ga <;> cases ab <;> cases de <;> cases eh <;> rcases hhg with rfl|rfl <;>
    simp only [Fin.sum_univ_seven,Fin.sum_univ_four,weights,owners,
      NonnegativeTotals.Source.owners,Matrix.cons_val,r92nd_e0,r92nd_e1,r92nd_e2,r92nd_e3,r92nd_e4,r92nd_e5,
      r92nd_e6,zeroProjection,quarterProjection,actualBlocks,blocks,PositiveTD.actualPairIncrement,
      pairF,pairG,PositiveTD.actualDIncrement,base,NonnegativeTotals.Source.aReserve,
      NonnegativeTotals.Source.eReserve,PairedE.primaryGain,PositiveANegativeTD.gain,
      SignedPoint.reflect,erase,H,G,A,B,T,D,E,hw,hd4,hclip,Real.sin_neg,Real.cos_neg,
      Real.sin_zero,Real.cos_zero,edgeWidth_zero,Bool.false_eq_true,↓reduceIte,Fin.isValue,
      show ((2:Fin 4)=0)=False by decide] <;>
    linear_combination c*(1-(C.point 4).y+(C.point 5).y)*hinv

/-- The decomposition as used by the stress bound, with the sign of the T error
that it needs. -/
theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) {s ε : ℝ} (hd : delta C.theta T=-s)
    (hs : s∈Icc 0 frameCap) :
    actualStress C hg ga ab de eh ε=base ε+
      l ε*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,actualBlocks C hg ga ab de eh ε i)+PositiveANegativeTD.gain c s (C.point T).a (-(C.point D).y)+
      NonnegativeTotals.Source.aReserve C ga ab (l ε)+NonnegativeTotals.Source.eReserve C de eh := by
  have ht := transport_trig hs
  have hc : 0<Real.cos s := by linarith [ht.1]
  rw [r92_decomposition_residual C ga ab de eh hhg hd hc.ne',abs_of_nonneg ht.2.2.1,
    abs_of_pos hc]
  simp

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab de eh ε i).u+f (blocks C hg ga ab de eh ε i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta T)-selectedSum C ga ab de eh f := by
  cases ga <;> cases ab <;> cases de <;> cases eh <;> by_cases hhg : hg=0 <;>
    simp [blocks,erase,selectedSum,PairedE.selected,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) {s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta T=-s) :
    total C ga ab de eh∈Icc 0 frameCap ∧
    aTotal C ga ab∈Icc 0 frameCap ∧ eTotal C de eh∈Icc 0 frameCap ∧
    (∑i,(blocks C hg ga ab de eh ε i).P)≤frameCap-total C ga ab de eh ∧
    (∑i,(blocks C hg ga ab de eh ε i).N)≤frameCap-s ∧
    (∑i,(blocks C hg ga ab de eh ε i).N)=total C ga ab de eh-s+
      ∑i,(blocks C hg ga ab de eh ε i).P := by
  have hp := sum_parts C hg ga ab de eh ε positivePart positivePart_zero
  have hn := sum_parts C hg ga ab de eh ε negativePart negativePart_zero
  have hselected := NonnegativeTotals.Source.selected_signed C ga ab de eh
  have hnp := NonnegativeTotals.Source.selected_nonnegative C ga ab de eh negativePart negativePart_nonneg
  have hzero : positivePart (delta C.theta T)=0 := by
    rw [hd]
    exact max_eq_right (neg_nonpos.mpr hs.1)
  have hneg : negativePart (delta C.theta T)=s := by
    rw [hd]
    change max (-(-s)) 0=s
    rw [neg_neg,max_eq_left hs.1]
  have hP : (∑i,(blocks C hg ga ab de eh ε i).P)=
      positiveVariation C.theta-selectedSum C ga ab de eh positivePart := by
    simpa only [ActualOrdinaryBlocks.Block.P,hzero,positiveVariation,sub_zero] using hp
  have hN : (∑i,(blocks C hg ga ab de eh ε i).N)=
      negativeVariation C.theta-s-selectedSum C ga ab de eh negativePart := by
    simpa only [ActualOrdinaryBlocks.Block.N,hneg,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab de eh ε i).P_nonneg)
  have ht : total C ga ab de eh≤frameCap := by
    dsimp [total]
    linarith
  have ht0 : 0≤total C ga ab de eh := by dsimp [total]; linarith
  have ht' : aTotal C ga ab+eTotal C de eh≤frameCap := ht
  refine ⟨⟨ht0,ht⟩,⟨ha,by linarith⟩,⟨he,by linarith⟩,?_,?_,?_⟩
  · dsimp [total]
    linarith
  · linarith [variations_equal C.theta]
  · dsimp [total]
    linarith [variations_equal C.theta]

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (ga ab de eh : Bool) (ε : ℝ) {s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (he : 0≤eTotal C de eh)
    (hs : s∈Icc 0 frameCap) (hd : delta C.theta T=-s) (i : Fin 4) :
    (blocks C hg ga ab de eh ε i).P≤frameCap ∧ (blocks C hg ga ab de eh ε i).N≤frameCap := by
  have hb := budgets hg ga ab de eh ε hvar ha he hs hd
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh ε j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg ga ab de eh ε j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.1.1,hb.2.2.2.1],by linarith [hb.2.2.2.2.1,hs.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool) {ε : ℝ}
    (hε : ε∈Icc 0 frameCap) (i : Fin 4) :
    (blocks C hg ga ab de eh ε i).p=p ε i ∧ (blocks C hg ga ab de eh ε i).q=q ε i := by
  have hr := ranges hε
  have hk : k ε≤1 := by linarith [hr.2.1]
  have hl : k ε≤l ε := hr.2.2.2.2.1.le
  have hc : l ε≤c := hr.2.2.2.2.2.1.le
  fin_cases i <;> simp [blocks,ActualOrdinaryBlocks.Block.p,ActualOrdinaryBlocks.Block.q,p,q,
    min_eq_left hk,max_eq_right hk,min_eq_left hl,max_eq_right hl,min_eq_left hc,max_eq_right hc]

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.NegativeTD.Source
