module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3SourceData
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3SortedSupport

/-!
# The unchanged original positive-BT3 stress

Uncompiled equations (4)--(10). The actual T force is supported in
direction (1,eta), using its original shifted containment inequality.
All four full blocks retain their own original points. The low-total
version changes only the D support baseline to its exact diagonal value.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

def actualStress (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l m : ℝ) : ℝ :=
  demand C (weights k l m (delta C.theta B))-
    ∑i,work (force C (owners hg ga ab de eh) (weights k l m (delta C.theta B)) i) (C.point i)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l m : ℝ) : Fin 4→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l m 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l m 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l m 2) (C.point B).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l m 3) (C.point Candidate.D).reflect]

def tReserve (C : SignedCycle) (m : ℝ) : ℝ :=
  m*Real.sin (delta C.theta B)*
    (PositiveTD.sigma-((C.point T).a+PositiveTD.eta*(C.point T).y))

abbrev aReserve := NonnegativeTotals.Source.aReserve
abbrev eReserve := NonnegativeTotals.Source.eReserve

theorem actual_T_support {q : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap) :
    P.a+PositiveTD.eta*P.y≤PositiveTD.sigma := by
  have hh := PositiveTD.actual_T_support (P:=P.reflect) (by simpa using hs)
    (by simpa using hc) hq
  simpa [SignedPoint.reflect] using hh

theorem tReserve_nonnegative {q m : ℝ} {C : SignedCycle}
    (hs : (C.point T).Sorted) (hc : (C.point T).Contained q) (hq : q≤qCap)
    (hm : 0≤ m) (hu : delta C.theta B∈Icc 0 frameCap) : 0≤tReserve C m := by
  exact mul_nonneg (mul_nonneg hm (transport_trig hu).2.2.1)
    (sub_nonneg.mpr (actual_T_support hs hc hq))

private theorem r81_stress_sum (C : SignedCycle) (owner : Vertex → Fin 4) (w : Vertex → ℝ) :
    demand C w-∑ i,work (force C owner w i) (C.point i)=
      ∑ i,w i*(edgeWidth (delta C.theta i)-C.edge i (owner i)) := by
  rw [←sum_force_work,demand,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem r81_edges (C : SignedCycle) (j : Fin 4) :
    C.edge 0 j=zeroProjection (C.point 0) (C.point 1) (delta C.theta 0) j ∧
    C.edge 1 j=quarterProjection (C.point 1) (C.point 2) (delta C.theta 1) j ∧
    C.edge 2 j=zeroProjection (C.point 2) (C.point 3) (delta C.theta 2) j ∧
    C.edge 3 j=quarterProjection (C.point 3) (C.point 4) (delta C.theta 3) j ∧
    C.edge 4 j=zeroProjection (C.point 4) (C.point 5) (delta C.theta 4) j ∧
    C.edge 5 j=quarterProjection (C.point 5) (C.point 6) (delta C.theta 5) j ∧
    C.edge 6 j=quarterProjection (C.point 6) (C.point 0) (delta C.theta 6) j := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> rfl

theorem decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (k l m : ℝ) :
    actualStress C hg ga ab de eh k l m=
      Analytic.fullBaseline k l m (delta C.theta B)+
        l*TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,actualBlocks C hg ga ab de eh k l m i)+
        tReserve C m+aReserve C ga ab l+eReserve C de eh := by
  rw [actualStress,r81_stress_sum]
  simp only [Fin.sum_univ_seven,weights,owners,Matrix.cons_val]
  rw [(r81_edges C _).1,(r81_edges C _).2.1,(r81_edges C _).2.2.1,(r81_edges C _).2.2.2.1,
    (r81_edges C _).2.2.2.2.1,(r81_edges C _).2.2.2.2.2.1,(r81_edges C _).2.2.2.2.2.2]
  simp only [aReserve,eReserve,NonnegativeTotals.Source.aReserve,NonnegativeTotals.Source.eReserve,
    actualBlocks,Fin.sum_univ_four,blocks,Matrix.cons_val,PositiveTD.actualPairIncrement,
    pairF,pairG,tReserve,Analytic.fullBaseline,PairedE.primaryGain,SignedPoint.reflect,
    H,G,A,B,T,Candidate.D,E]
  simp only [aTotal,eTotal,NonnegativeTotals.Source.aTotal,NonnegativeTotals.Source.eTotal,tilted,
    PositiveTD.eta,G,A,Candidate.D,E]
  rcases hhg with rfl|rfl <;> cases ga <;> cases ab <;> cases de <;> cases eh <;>
    simp only [↓reduceIte,Bool.false_eq_true,erase,quarterProjection,zeroProjection,Matrix.cons_val,
      edgeWidth_zero,Real.sin_zero,Real.cos_zero,Fin.isValue,Fin.reduceEq] <;> ring

def sortedD (C : SignedCycle) (de : Bool) (m : ℝ) : ℝ :=
  let c := tilted m (delta C.theta B)
  let x := delta C.theta T
  let y := erase de (delta C.theta Candidate.D)
  c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
    (forceA c x y*(C.point Candidate.D).a+forceB c x y*(-(C.point Candidate.D).y))

def sortedBlocks (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k m : ℝ) : Fin 4→ℝ :=
  ![actualBlocks C hg ga ab de eh k 1 m 0,actualBlocks C hg ga ab de eh k 1 m 1,
    actualBlocks C hg ga ab de eh k 1 m 2,sortedD C de m]

theorem sortedD_identity (C : SignedCycle) (hg : Fin 4) (ga ab de eh : Bool) (k l m : ℝ) :
    sortedD C de m=actualBlocks C hg ga ab de eh k l m 3+
      (1+tilted m (delta C.theta B))*GlobalGA.Secondary.diagonal-fullSupport 1 (tilted m (delta C.theta B)) := by
  simp [sortedD,actualBlocks,blocks,PositiveTD.actualPairIncrement,pairF,pairG,forceA,forceB,
    SignedPoint.reflect]
  ring

theorem sorted_decomposition (C : SignedCycle) {hg : Fin 4} (ga ab de eh : Bool)
    (hhg : hg=0∨hg=2) (k m : ℝ) :
    actualStress C hg ga ab de eh k 1 m=
      Analytic.lowBaseline k m (delta C.theta B)+
        TwoPositive.ASupport.charge (aTotal C ga ab)+TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,sortedBlocks C hg ga ab de eh k m i)+
        tReserve C m+aReserve C ga ab 1+eReserve C de eh := by
  rw [decomposition C ga ab de eh hhg]
  simp only [sortedBlocks,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.reduceFinMk,Fin.sum_univ_zero,add_zero]
  rw [sortedD_identity C hg ga ab de eh k 1 m]
  have hsupport : fullSupport 1 k=fullSupport k 1 := by simp [fullSupport,add_comm]
  have hsupportM : fullSupport m 1=fullSupport 1 m := by simp [fullSupport,add_comm]
  dsimp [Analytic.fullBaseline,Analytic.lowBaseline]
  rw [hsupport,hsupportM]
  ring

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (ga ab de eh : Bool) {k l m : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0< m) (hu : delta C.theta B∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible Candidate.D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg ga ab de eh k l m≤0 := by
  have hrot : 0≤tilted m (delta C.theta B) := (PositiveTD.tilted_pos hm hu).le
  have hw (i : Vertex) : 0≤weights k l m (delta C.theta B) i := by
    fin_cases i <;> simp [weights] <;> positivity
  have hf (i : Vertex) : C.Feasible i (owners hg ga ab de eh i) := by
    fin_cases i
    · simpa [owners,H] using hHG
    · simpa [owners,G] using hGA
    · simpa [owners,A] using hAB
    · simpa [owners,B] using hBT
    · simpa [owners,T] using hTD
    · simpa [owners,Candidate.D] using hDE
    · simpa [owners,E] using hEH
  exact sub_nonpos.mpr (weighted_separation hw hf)

theorem full_blocks_lower {q k l m : ℝ} {C : SignedCycle} {hg : Fin 4}
    (ga ab de eh : Bool) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point Candidate.D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aTotal C ga ab) (hu : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (hk : k≤1) (hl : k≤l)
    (hp : ∀i,0<pWeights k l m (tilted m (delta C.theta B)) i) (i : Fin 4) :
    mixedBlock R (pWeights k l m (tilted m (delta C.theta B)) i)
      (qWeights k l m (tilted m (delta C.theta B)) i)
      (blocks C hg ga ab de eh k l m i).P (blocks C hg ga ab de eh k l m i).N≤
        actualBlocks C hg ga ab de eh k l m i := by
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights k l m (tilted m (delta C.theta B)) j)
        (qWeights k l m (tilted m (delta C.theta B)) j)
        (blocks C hg ga ab de eh k l m j).P (blocks C hg ga ab de eh k l m j).N≤
          PositiveTD.actualPairIncrement (blocks C hg ga ab de eh k l m j) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (m:=m) ga ab de eh hk hl j
    have hpn : 0≤(blocks C hg ga ab de eh k l m j).p := by rw [hd.1]; exact (hp j).le
    have hb := block_budgets hg ga ab de eh k l m hvar ha hu he j
    have hh := PositiveTD.actual_block_minorant hy hP hq hpn hb.1 hb.2
    rwa [hd.1,hd.2] at hh
  fin_cases i
  · simpa [actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [actualBlocks] using hordinary 1 (P:=(C.point G).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G)
  · simpa [actualBlocks] using hordinary 2 (P:=(C.point B).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B)
  · simpa [actualBlocks] using hordinary 3 (P:=(C.point Candidate.D).reflect)
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hc Candidate.D)

theorem sortedD_lower {q m : ℝ} {C : SignedCycle} (de : Bool)
    (hs : (C.point Candidate.D).Sorted) (hc : (C.point Candidate.D).Contained q) (hq : q≤qCap)
    (hy : (C.point Candidate.D).y≤0)
    (hcoef : tilted m (delta C.theta B)∈Icc 1 Cmax)
    (hdom : SignedDomain (delta C.theta T) (erase de (delta C.theta Candidate.D))) :
    PositiveBT3.D (tilted m (delta C.theta B)) (delta C.theta T)
      (erase de (delta C.theta Candidate.D))≤ sortedD C de m := by
  have hangles := signed_domain_angles hdom
  have hforce := force_positive hcoef hangles.1 hangles.2
  have hh := actual_sorted_support hs hy hc hq hforce.1.le hforce.2.le
  dsimp [PositiveBT3.D,sortedD]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.Source
