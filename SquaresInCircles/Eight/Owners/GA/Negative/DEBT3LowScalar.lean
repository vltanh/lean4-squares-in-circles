module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSeparatedPolynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Polynomial
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3PositivePure
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeAConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2EndpointData
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowEnvelope
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSecants
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSplit
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Stress
public import SquaresInCircles.Eight.Owners.GA.TD2LowEnvelope
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveScalar

/-!
# Eight squares: the complete low-total scalar with its original three angles

The whole negative-DE interval below the total
is concave and retains both original endpoints. At zero DE magnitude
the stress is the already proved ordinary positive-BT3 scalar. At equal
angles the original split is concave and both new sorted-D endpoints
have been proved. Positive surplus is reduced to that same equal-angle
value. The final theorem consumes the complete actual four-block mass
allocation, not a selected scalar alternative as a hypothesis.
-/

section
/-!
## Original signed budgets for a negative A primary and positive BT3

The original BT error and single negative A
argument are deleted only from the analytic ordinary blocks. Both
signed E errors are kept until their exact selected total is formed.
Their positive and negative parts give the two original variation
budgets and the enlarged nonnegative remaining total.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks

abbrev aError := NegativeAPositiveTD.Source.aError
abbrev eTotal := PairedE.cycleTotal
def effective (C : SignedCycle) (de eh : Bool) (s : ℝ) : ℝ :=
  delta C.theta B+eTotal C de eh-s
def blocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → Block :=
  PositiveBT3.Source.blocks C hg atG (!atG) de eh k l c
def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : Fin 4 → ℝ :=
  PositiveBT3.Source.actualBlocks C hg atG (!atG) de eh k l c
def actualStress (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ) : ℝ :=
  PositiveBT3.Source.actualStress C hg atG (!atG) de eh k l c
def eParts (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ) : ℝ :=
  f (PairedE.selected de (delta C.theta D))+f (PairedE.selected eh (delta C.theta E))

theorem eParts_nonnegative (C : SignedCycle) (de eh : Bool) (f : ℝ → ℝ)
    (hf : ∀u,0≤f u) : 0≤eParts C de eh f := by
  exact add_nonneg (hf _) (hf _)

theorem eParts_signed (C : SignedCycle) (de eh : Bool) :
    eParts C de eh positivePart-eParts C de eh negativePart=eTotal C de eh := by
  have hD := positive_sub_negative (PairedE.selected de (delta C.theta D))
  have hE := positive_sub_negative (PairedE.selected eh (delta C.theta E))
  dsimp [eParts,eTotal,PairedE.cycleTotal,PairedE.total]
  linarith

theorem selected_parts {C : SignedCycle} {s : ℝ} (atG de eh : Bool)
    (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    PositiveBT3.Source.selectedSum C atG (!atG) de eh f=f (-s)+eParts C de eh f := by
  cases atG <;>
    simp only [aError,NegativeAPositiveTD.Source.aError,Bool.false_eq_true,ite_false,ite_true] at ha <;>
    simp [PositiveBT3.Source.selectedSum,PairedE.selected,eParts,ha,hf,add_assoc]

theorem block_parts {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool)
    (k l c : ℝ) (ha : aError C atG= -s) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG de eh k l c i).u+f (blocks C hg atG de eh k l c i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta B)-f (-s)-eParts C de eh f := by
  have hh := PositiveBT3.Source.sum_parts C hg atG (!atG) de eh k l c f hf
  rw [selected_parts atG de eh ha f hf] at hh
  dsimp [blocks]
  linarith

structure Budget (C : SignedCycle) (hg : Fin 4) (atG de eh : Bool) (k l c s : ℝ) : Prop where
  bt_domain : delta C.theta B∈Icc 0 frameCap
  e_domain : eTotal C de eh∈Icc 0 frameCap
  total_upper : delta C.theta B+eTotal C de eh≤frameCap
  residual_domain : effective C de eh s∈Icc 0 frameCap
  positive_original : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta B-eTotal C de eh
  positive_bound : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-effective C de eh s
  negative_original : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s
  negative_bound : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap
  balance : (∑i,(blocks C hg atG de eh k l c i).N)=
    effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P

theorem budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh) :
    Budget C hg atG de eh k l c s := by
  have hp := block_parts hg atG de eh k l c ha positivePart positivePart_zero
  have hn := block_parts hg atG de eh k l c ha negativePart negativePart_zero
  have hpz : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hnz : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hps : positivePart (-s)=0 := max_eq_right (by linarith)
  have hns : negativePart (-s)=s := by simp [negativePart,hs]
  have hP : (∑i,(blocks C hg atG de eh k l c i).P)=
      positiveVariation C.theta-delta C.theta B-eParts C de eh positivePart := by
    simpa only [Block.P,hpz,hps,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg atG de eh k l c i).N)=
      negativeVariation C.theta-s-eParts C de eh negativePart := by
    simpa only [Block.N,hnz,hns,sub_zero,negativeVariation] using hn
  have heq := eParts_signed C de eh
  have hEneg := eParts_nonnegative C de eh negativePart negativePart_nonneg
  have hP0 : 0≤∑i,(blocks C hg atG de eh k l c i).P :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).P_nonneg)
  have hN0 : 0≤∑i,(blocks C hg atG de eh k l c i).N :=
    Finset.sum_nonneg (fun i _ => (blocks C hg atG de eh k l c i).N_nonneg)
  have hPcap : (∑i,(blocks C hg atG de eh k l c i).P)≤frameCap-delta C.theta B-eTotal C de eh := by
    linarith
  have hNcap : (∑i,(blocks C hg atG de eh k l c i).N)≤frameCap-s := by
    linarith [variations_equal C.theta]
  have hbalance : (∑i,(blocks C hg atG de eh k l c i).N)=
      effective C de eh s+∑i,(blocks C hg atG de eh k l c i).P := by
    dsimp [effective]
    linarith [variations_equal C.theta]
  have htotal : delta C.theta B+eTotal C de eh≤frameCap := by linarith
  refine ⟨⟨hz,by linarith⟩,⟨by linarith,by linarith⟩,htotal,
    ?_,hPcap,?_,hNcap,by linarith,hbalance⟩
  · dsimp [effective]; constructor <;> linarith
  · dsimp [effective]; linarith

theorem block_budgets {C : SignedCycle} {s : ℝ} (hg : Fin 4) (atG de eh : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh) (i : Fin 4) :
    (blocks C hg atG de eh k l c i).P≤frameCap ∧ (blocks C hg atG de eh k l c i).N≤frameCap := by
  have hb := budgets hg atG de eh k l c hvar hs ha hz he
  have hP := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).P_nonneg) (Finset.mem_univ i)
  have hN := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG de eh k l c j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound,hb.residual_domain.1],hN.trans hb.negative_bound⟩

abbrev gain_lower := @NegativeA.LongE.Source.gain_lower

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
end
end
end

section
/-!
## Original BT3 stress with the common negative-A gain

The equal A multipliers keep the original
primary gain exactly. The actual T support is valid for both tangent
signs. Each full or sorted-D block is bounded on its own original
point, after both signed budgets have been proved from the cycle.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG de eh : Bool)
    (hhg : hg=0∨hg=2) (k l m s : ℝ) :
    actualStress C hg atG de eh k l m=
      PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+l*gain s+
        TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,actualBlocks C hg atG de eh k l m i)+PositiveBT3.Source.tReserve C m+
        l*(PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s)+
        NonnegativeTotals.Source.eReserve C de eh := by
  have hh := PositiveBT3.Source.decomposition C atG (!atG) de eh hhg k l m
  dsimp [actualStress,actualBlocks,eTotal,PairedE.cycleTotal,
    PositiveBT3.Source.aReserve,PositiveBT3.Source.eReserve,
    NonnegativeTotals.Source.aReserve,PositiveBT3.Source.aTotal,
    NonnegativeTotals.Source.aTotal,PositiveBT3.Source.eTotal] at ⊢ hh
  linarith

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool) {k l m : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0< m) (hz : delta C.theta B∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg atG de eh k l m≤0 := by
  have hAB' : C.Feasible A (if !atG then 2 else 0) := by
    cases atG <;> simpa using hAB
  exact PositiveBT3.Source.stress_nonpositive atG (!atG) de eh
    hk hl hm hz hHG hGA hAB' hBT hTD hDE hEH

theorem full_blocks_lower {q k l m s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hc : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hk : k≤1) (hl : k≤l)
    (hp : ∀i,0<PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
    (i : Fin 4) :
    mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
      (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
      (blocks C hg atG de eh k l m i).P (blocks C hg atG de eh k l m i).N≤
        actualBlocks C hg atG de eh k l m i := by
  have hordinary (j : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) j)
        (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) j)
        (blocks C hg atG de eh k l m j).P (blocks C hg atG de eh k l m j).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG de eh k l m j) P := by
    have hd := PositiveBT3.Source.block_coefficients (C:=C) (hg:=hg) (m:=m)
      atG (!atG) de eh hk hl j
    change (blocks C hg atG de eh k l m j).p=_ ∧
      (blocks C hg atG de eh k l m j).q=_ at hd
    have hpn : 0≤(blocks C hg atG de eh k l m j).p := by rw [hd.1]; exact (hp j).le
    have hb := block_budgets hg atG de eh k l m hvar hs ha hz he j
    have hh := PositiveTD.actual_block_minorant hy hP hq hpn hb.1 hb.2
    rwa [hd.1,hd.2] at hh
  fin_cases i
  · exact hordinary 0 hHy (hc H)
  · exact hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G)
  · exact hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B)
  · exact hordinary 3 (P:=(C.point D).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy) (by simpa using hc D)

theorem reserves_nonnegative {q l m s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hvar : positiveVariation C.theta≤frameCap) (hs : 0≤ s)
    (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hl : 0≤l) (hm : 0≤ m)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)) :
    0≤PositiveBT3.Source.tReserve C m ∧
    0≤l*(PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s) ∧
    0≤NonnegativeTotals.Source.eReserve C de eh := by
  have hb := budgets hg atG de eh 1 l m hvar hs ha hz he
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hT := PositiveBT3.Source.tReserve_nonnegative (hsorted T) (hcontained T) hq hm hb.bt_domain
  have hE := PairedE.selected_charge de eh (hsorted E) (hcontained E) hq
    (original_error_bound hvar hn D) (original_error_bound hvar hn E) hb.e_domain
  exact ⟨hT,mul_nonneg hl (sub_nonneg.mpr hgain),sub_nonneg.mpr hE⟩

theorem full_stress_lower {q k l m s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (hk : k≤1) (hl : k≤l) (hl0 : 0≤l) (hm : 0≤ m)
    (hp : ∀i,0<PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i) :
    PositiveBT3.Analytic.fullBaseline k l m (delta C.theta B)+l*gain s+
      TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,mixedBlock R (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
        (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)) i)
        (blocks C hg atG de eh k l m i).P (blocks C hg atG de eh k l m i).N)≤
      actualStress C hg atG de eh k l m := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    full_blocks_lower (hg:=hg) atG de eh hcontained hq hHy hGy hBy hDy hvar hs ha hz he hk hl hp i)
  have hres := reserves_nonnegative atG de eh hsorted hcontained hq
    hvar hs ha hz he hl0 hm hgain (hg:=hg)
  rw [decomposition C atG de eh hhg k l m s]
  linarith [hres.1,hres.2.1,hres.2.2]

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
end
end
end

section
/-!
## The small-total longer-E comparison on the original BT3 cycle

The low family is evaluated at
z+e-s. Both A multipliers are one. The full signed sorted-D bound
is applied to the original TD0 and unselected DE arguments, and the
common negative-A gain pays the virtual reduction of E from e to e-s.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

theorem sorted_decomposition (C : SignedCycle) {hg : Fin 4} (atG de eh : Bool)
    (hhg : hg=0∨hg=2) (k m s : ℝ) :
    actualStress C hg atG de eh k 1 m=
      PositiveBT3.Analytic.lowBaseline k m (delta C.theta B)+gain s+
        TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,PositiveBT3.Source.sortedBlocks C hg atG (!atG) de eh k m i)+
        PositiveBT3.Source.tReserve C m+
        (PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s)+
        NonnegativeTotals.Source.eReserve C de eh := by
  have hh := PositiveBT3.Source.sorted_decomposition C atG (!atG) de eh hhg k m
  dsimp [actualStress,eTotal,PairedE.cycleTotal,
    PositiveBT3.Source.aReserve,PositiveBT3.Source.eReserve,
    NonnegativeTotals.Source.aReserve,PositiveBT3.Source.aTotal,
    NonnegativeTotals.Source.aTotal,PositiveBT3.Source.eTotal] at ⊢ hh
  linarith

theorem low_blocks_lower {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (ht : effective C de eh s∈Icc 0 (1/6:ℝ)) (i : Fin 4) :
    PositiveBT3.LowEnvelope.block (effective C de eh s) i
      (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
        (PositiveBT3.lowM (effective C de eh s)) i).P
      (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
        (PositiveBT3.lowM (effective C de eh s)) i).N≤
      PositiveBT3.Source.sortedBlocks C hg atG (!atG) de eh
        (PositiveBT3.lowK (effective C de eh s)) (PositiveBT3.lowM (effective C de eh s)) i := by
  let t := effective C de eh s
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hzT : delta C.theta B∈Icc 0 t := ⟨hz,by dsimp [t,effective]; linarith⟩
  have hrot := PositiveBT3.Analytic.low_tilted_ranges ht hzT
  have hk : 0<PositiveBT3.lowK t := by dsimp [t]; linarith [hr.1.1]
  have hk1 : PositiveBT3.lowK t≤1 := by dsimp [t,PositiveBT3.K] at *; linarith [hr.1.2]
  have hm1 : 1≤PositiveBT3.lowM t := by dsimp [t] at *; linarith [hr.2.1]
  have hc1 : 1≤PositiveBT3.tilted (PositiveBT3.lowM t) (delta C.theta B) := hm1.trans hrot.1
  have hp (j : Fin 4) : 0<PositiveBT3.pWeights (PositiveBT3.lowK t) 1 (PositiveBT3.lowM t)
      (PositiveBT3.tilted (PositiveBT3.lowM t) (delta C.theta B)) j := by
    fin_cases j <;> simp [PositiveBT3.pWeights,min_eq_left hm1,min_eq_left hc1] <;> linarith
  have hfull (j : Fin 4) := full_blocks_lower atG de eh hcontained hq hHy hGy hBy hDy
    hvar hs ha hz he hk1 hk1 hp j (hg:=hg)
  fin_cases i
  · simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
      PositiveBT3.Source.sortedBlocks,actualBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,t]
      using hfull 0
  · simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
      PositiveBT3.Source.sortedBlocks,actualBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,t]
      using hfull 1
  · simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.LowEnvelope.p,PositiveBT3.LowEnvelope.q,
      PositiveBT3.Source.sortedBlocks,actualBlocks,PositiveBT3.pWeights,PositiveBT3.qWeights,
      min_eq_left hm1,max_eq_right hm1,t] using hfull 2
  · have hb := block_budgets hg atG de eh (PositiveBT3.lowK t) 1 (PositiveBT3.lowM t)
      hvar hs ha hz he 3
    have hdom : PositiveBT3.SignedDomain (delta C.theta T) (erase de (delta C.theta D)) := by
      simpa [blocks,PositiveBT3.Source.blocks,Block.P,Block.N,PositiveBT3.SignedDomain,
        PositiveBT3.positiveTotal,PositiveBT3.negativeTotal] using hb
    have hcoef : PositiveBT3.tilted (PositiveBT3.lowM t) (delta C.theta B)∈Icc 1 PositiveBT3.Cmax :=
      ⟨hc1,hrot.2⟩
    have hD := PositiveBT3.signed_minorant hcoef hdom
    have hactual := PositiveBT3.Source.sortedD_lower de (hsorted D) (hcontained D) hq hDy hcoef hdom
    simpa [PositiveBT3.LowEnvelope.block,PositiveBT3.Source.sortedBlocks,blocks,
      PositiveBT3.Source.blocks,Block.P,Block.N,PositiveBT3.positiveTotal,PositiveBT3.negativeTotal,t]
      using hD.trans hactual

theorem low_stress_lower {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (ht : effective C de eh s∈Icc 0 (1/6:ℝ)) :
    PositiveBT3.Analytic.lowBaseline (PositiveBT3.lowK (effective C de eh s))
      (PositiveBT3.lowM (effective C de eh s)) (delta C.theta B)+gain s+
      TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,PositiveBT3.LowEnvelope.block (effective C de eh s) i
        (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
          (PositiveBT3.lowM (effective C de eh s)) i).P
        (blocks C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
          (PositiveBT3.lowM (effective C de eh s)) i).N)≤
      actualStress C hg atG de eh (PositiveBT3.lowK (effective C de eh s)) 1
        (PositiveBT3.lowM (effective C de eh s)) := by
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    low_blocks_lower atG de eh hsorted hcontained hq hHy hGy hBy hDy hvar hs ha hz he ht i (hg:=hg))
  have hm : 0≤PositiveBT3.lowM (effective C de eh s) :=
    by linarith [(PositiveBT3.Analytic.low_ranges ht).2.1]
  have hres := reserves_nonnegative atG de eh hsorted hcontained hq hvar hs ha hz he
    (by norm_num : (0:ℝ)≤1) hm hgain (hg:=hg)
  rw [sorted_decomposition C atG de eh hhg _ _ s]
  simp only [one_mul] at hres
  linarith [hres.1,hres.2.1,hres.2.2]

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE.Source
end
end
end

section
/-!
## Low-total concentration when the negative mass is larger

The secant is bounded before the positive cost of D is compared with an ordinary positive
allocation. The negative B block is dominated by H on the whole angular interval (`H_le_B`).
Concavity carries the H secant to the shifted interval with both masses kept (`negative_shift`).
All pure, same-block and separated alternatives, the distinguished D block included, then have the
one lower bound `V_H(θ - s)` (`sum_to_H`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowNegative
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope

lemma short_secant {s : ℝ} (hs : s∈Icc (0:ℝ) (1/6)) :
    Explicit.sec s≤(203/200:ℝ) := by
  have hsf : s∈Icc 0 frameCap :=
    ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hc := NegativeESecant.cos_pos hsf
  have hl := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  change 1/Real.cos s≤(203/200:ℝ)
  apply (div_le_iff₀ hc).2
  norm_num at hs2
  nlinarith

lemma secant_le_c {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) :
    Explicit.sec s≤Explicit.c .low θ z := by
  have hsec := short_secant (show s∈Icc (0:ℝ) (1/6) from ⟨hs.1,hs.2.trans hθ.2⟩)
  have hm := (Explicit.low_bounds hθ).2.1
  have hc := (Explicit.low_c hθ hz).1
  linarith

lemma gamma_upper {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) :
    Explicit.gamma .low θ z s≤(13/20:ℝ) := by
  have hc := (Explicit.low_c hθ hz).2
  rw [Explicit.gamma,max_eq_right (secant_le_c hθ hz hs)]
  dsimp [SecantD.slope]
  linarith

lemma positive_lower {θ z s t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    -(13/20)*t≤Blocks.positive .low θ z s t i := by
  by_cases hi : i=3
  · subst i
    rw [Blocks.positive_D]
    have hh := mul_le_mul_of_nonneg_right (gamma_upper hθ hz hs) ht.1
    linarith
  · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
    obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i :=
      ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
    subst i
    rw [Blocks.positive_ordinary]
    have hh := PositivePure.ordinary_lower .low hθ ht j
    linarith [ht.1]

lemma H_upper {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low θ) 1 t≤(1101/1000)*t := by
  have hk := (PositiveBT3.Analytic.low_ranges hθ).1
  have hh := PositiveTD.V_first_coefficient (by norm_num : (0:ℝ)<1)
    (by linarith [hk.1]) hk.2 (by norm_num [PositiveBT3.K]) ht
  exact hh.trans (PositiveBT3.vstar_linear_upper ht)

lemma H_le_B {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) :
    V R (Explicit.k .low θ) 1 t≤V R 1 (Explicit.m .low θ) t := by
  have hm := (Explicit.low_bounds hθ).2
  have hb := V_chord_lower (p:=(1:ℝ)) (q:=Explicit.m .low θ)
    (by norm_num) (by linarith [hm.1]) (by linarith [hm.2]) ht
  have hh := H_upper hθ ht
  nlinarith only [hb,hh,ht.1]

lemma negative_comparison {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) (i : Fin 4) :
    V R (Explicit.k .low θ) 1 t≤Blocks.negative .low θ t i := by
  have hm : 1≤Explicit.m .low θ := by linarith [(Explicit.low_bounds hθ).2.1]
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  · exact le_rfl
  · exact le_rfl
  · show V R (Explicit.k .low θ) 1 t≤
      V R (min (Explicit.l .low θ) (Explicit.m .low θ)) (max (Explicit.l .low θ) (Explicit.m .low θ)) t
    have hl : Explicit.l .low θ=1 := rfl
    rw [hl,min_eq_left hm,max_eq_right hm]
    exact H_le_B hθ ht
  · exact le_rfl

/-- A concave V has no smaller increment when both endpoints shift left. -/
lemma negative_shift {p q θ s : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 θ) :
    V R p q frameCap-V R p q θ≤V R p q (frameCap-s)-V R p q (θ-s) := by
  have hq := hp.trans_le hpq
  have hd (u : ℝ) (hu : u∈Icc 0 θ) :
      HasDerivAt (fun u => V R p q (frameCap-u)-V R p q (θ-u))
        (Vd R p q (θ-u)-Vd R p q (frameCap-u)) u := by
    have h1 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) u := (hasDerivAt_id' u).const_sub frameCap
    have h2 : HasDerivAt (fun x : ℝ => θ-x) (-1) u := (hasDerivAt_id' u).const_sub θ
    have hleft : HasDerivAt (fun x => V R p q (frameCap-x)) (Vd R p q (frameCap-u)*-1) u :=
      (V_hasDerivAt (R:=R) (t:=frameCap-u) hp hq
        ⟨by linarith [hu.2,hθ.2],by linarith [hu.1]⟩).comp u h1
    have hright : HasDerivAt (fun x => V R p q (θ-x)) (Vd R p q (θ-u)*-1) u :=
      (V_hasDerivAt (R:=R) (t:=θ-u) hp hq
        ⟨by linarith [hu.2],by linarith [hu.1,hθ.2]⟩).comp u h2
    exact (hleft.fun_sub hright).congr_deriv (by ring)
  have hm : MonotoneOn (fun u => V R p q (frameCap-u)-V R p q (θ-u))
      (Icc 0 θ) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => hd u (Ioo_subset_Icc_self hu))
    intro u hu
    have hh := Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hp hpq hqp
      (show θ-u∈Icc 0 frameCap from
        ⟨by linarith [hu.2],by linarith [hu.1,hθ.2]⟩)
      (show frameCap-u∈Icc 0 frameCap from
        ⟨by linarith [hu.2,hθ.2],by linarith [hu.1]⟩)
      (by linarith [hθ.2] : θ-u≤frameCap-u)
    exact sub_nonneg.mpr hh
  simpa only [sub_zero] using hm ⟨le_rfl,hθ.1⟩ hs hs.1

lemma separated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (i j : Fin 4) :
    V R (Explicit.k .low θ) 1 (θ-s)≤
      Blocks.positive .low θ z s (frameCap-θ) i+
        Blocks.negative .low θ (frameCap-s) j := by
  have ht := Explicit.frame_domain .low hθ
  have hp := Explicit.family_pairs .low hθ 0
  have hP : frameCap-θ∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by linarith [hs.2,ht.2],by linarith [hs.1]⟩
  have hu := positive_lower hθ hz hs hP i
  have hv := negative_comparison hθ hN j
  have hshift : V R (Explicit.k .low θ) 1 frameCap-V R (Explicit.k .low θ) 1 θ≤
      V R (Explicit.k .low θ) 1 (frameCap-s)-V R (Explicit.k .low θ) 1 (θ-s) :=
    negative_shift hp.1 hp.2.1 hp.2.2 ht hs
  have hsec := PositiveBT3.LowSecants.H_secant hθ
  change V R (Explicit.k .low θ) 1 θ+(3/4)*(frameCap-θ)<
    V R (Explicit.k .low θ) 1 frameCap at hsec
  have h0 : (0:ℝ)≤frameCap-θ := hP.1
  generalize frameCap=F at hu hv hshift hsec h0 ⊢
  linarith only [hu,hv,hshift,hsec,h0]

lemma pure_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 θ) (i j : Fin 4) :
    V R (Explicit.k .low θ) 1 (θ-s)≤Blocks.pure .low θ z s i j := by
  have ht := Explicit.frame_domain .low hθ
  have hh := negative_comparison hθ
    (show θ-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1,ht.2]⟩) j
  simpa only [Blocks.pure,ChargedHybridConcentration.pure,hs.2,↓reduceIte,Blocks.negative] using hh

lemma saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ) (i j : Fin 4) :
    V R (Explicit.k .low θ) 1 (θ-s)≤Blocks.saturated .low θ z s i j := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (Explicit.frame_domain .low hθ).2⟩
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .low θ z s 3 3=
          Blocks.block .low θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,Blocks.block,
          ↓reduceIte]
      rw [he,Blocks.block_D]
      exact separated_lower hθ hz hs 3 3
    · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
      obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
        ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
      subst i
      exact (pure_lower hθ hs r.castSucc r.castSucc).trans
        (SameBlock.ordinary_saturated_lower .low hθ hsf r)
  · have he : Blocks.saturated .low θ z s i j=
        Blocks.positive .low θ z s (frameCap-θ) i+Blocks.negative .low θ (frameCap-s) j := by
      simp only [Blocks.saturated,ChargedHybridConcentration.saturated,hij,↓reduceIte]
      rfl
    rw [he]
    exact separated_lower hθ hz hs i j

/-- The whole four-block allocation, not only an endpoint sample. -/
theorem sum_to_H {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (hs : s∈Icc 0 θ)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    V R (Explicit.k .low θ) 1 (θ-s)≤∑i,Blocks.block .low θ z s (P i) (N i) i := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (Explicit.frame_domain .low hθ).2⟩
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .low P N hθ hsf hP hN hPb hNb hbalance
  exact (le_min (pure_lower hθ hs i j) (saturated_lower hθ hz hs i j)).trans hij

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowNegative
end
end
end

section
/-!
## The two low-total equal-angle endpoints

The sorted D support is kept: `sec θ` is below the D coefficient on the whole low interval. Its
diagonal correction is multiplied by the positive cosine before the three circle norms are bounded.
The polynomial masses are used only once they are known to be positive on the whole interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowEndpoints
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveTD.Certificate (C10 C12 S9 S11 taylor_bounds num3_transfer)

abbrev k (θ : ℝ) := Explicit.k .low θ
abbrev m (θ : ℝ) := Explicit.m .low θ

def base (ep : Split) (θ : ℝ) : ℝ := match ep with
  | .atA => 2*k θ+11/2-GlobalGA.Secondary.diagonal+m θ*(5/2-GlobalGA.Secondary.diagonal)+TwoPositive.ASupport.charge θ
  | .atT => 2*k θ+11/2-GlobalGA.Secondary.diagonal+m θ*
      (1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos θ+
        (1/2+Explicit.eta .low θ*(1-GlobalGA.Secondary.diagonal)-Explicit.sigma .low θ)*Real.sin θ)

def norms (θ : ℝ) : Fin 3→ℝ := ![pairNorm (k θ) 1 0,pairNorm (k θ) 1 0,pairNorm 1 (m θ) 0]
def nonradical (ep : Split) (θ : ℝ) : ℝ :=
  Real.cos θ*base ep θ+Explicit.K*Real.sin θ+(GlobalGA.Secondary.diagonal-1/2)*(Real.cos θ-1)

private lemma r72_diag : GlobalGA.Secondary.diagonal≤(449607033/500000000:ℝ) := by
  have h := PositiveTD.Certificate.diagonal_le_cbar
  simp only [PositiveTD.Certificate.cbar] at h
  push_cast at h
  linarith

private lemma r72_sigma (θ : ℝ) : Explicit.sigma .low θ≤(1415477291/1000000000:ℝ) := by
  have h := NonnegativeTotals.Charges.sigma_upper
  simp only [PositiveTD.sigma,PositiveTD.eta,NonnegativeTotals.Certificate.sigmabar] at h
  push_cast at h
  simp only [Explicit.sigma,Explicit.eta]
  linarith

theorem base_lower (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (Certificate.lowBase ep)≤base ep θ := by
  have ht := taylor_bounds (Explicit.frame_domain .low hθ)
  have hm : 0 ≤ m θ := by linarith [(Explicit.low_bounds hθ).2.1]
  have hs := (transport_trig (Explicit.frame_domain .low hθ)).2.2.1
  have hc0 : 0≤Real.cos θ := by linarith [(transport_trig (Explicit.frame_domain .low hθ)).1]
  have hD := r72_diag
  have hS := r72_sigma θ
  cases ep with
  | atA =>
    have hj := PositiveBT3.Analytic.low_J_lower hθ
    have hab : Certificate.abar=NonnegativeTotals.Certificate.abar := by
      norm_num [Certificate.abar,NonnegativeTotals.Certificate.abar]
    have hJ : Certificate.J=PositiveBT3.LowCertificate.J := by
      simp only [Certificate.J,PositiveBT3.LowCertificate.J,PositiveBT3.LowCertificate.C10,
        PositiveBT3.LowCertificate.S9,PositiveBT3.LowCertificate.abar,hab]
    have hprod := mul_le_mul_of_nonneg_left
      (sub_le_sub_left hD (5/2:ℝ)) hm
    simp only [Certificate.lowBase,map_add,map_mul,aeval_C,Certificate.lowK_eval,
      Certificate.lowM_eval,hJ,eq_ratCast,Certificate.cbar]
    push_cast
    simp only [base]
    linarith
  | atT =>
    have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1
      (show (0:ℝ)≤3/2-449607033/500000000 by norm_num)
    have hsin := mul_le_mul_of_nonpos_left ht.2.2.1
      (show (1/2:ℝ)+(293/1000)*(1-449607033/500000000)-1415477291/1000000000≤0 by norm_num)
    have hdc := mul_le_mul_of_nonneg_right hD hc0
    have hds := mul_le_mul_of_nonneg_right hD hs
    have hss := mul_le_mul_of_nonneg_right hS hs
    have he : Explicit.eta .low θ=293/1000 := rfl
    have hinner : 1+(3/2-449607033/500000000)*aeval θ C10+
        ((1/2:ℝ)+(293/1000)*(1-449607033/500000000)-1415477291/1000000000)*aeval θ S9≤
      1+(3/2-GlobalGA.Secondary.diagonal)*Real.cos θ+
        (1/2+Explicit.eta .low θ*(1-GlobalGA.Secondary.diagonal)-Explicit.sigma .low θ)*
          Real.sin θ := by
      rw [he]
      linarith
    have hprod := mul_le_mul_of_nonneg_left hinner hm
    simp only [Certificate.lowBase,map_add,map_mul,map_sub,map_one,aeval_C,Certificate.lowK_eval,
      Certificate.lowM_eval,eq_ratCast,Certificate.cbar,Certificate.eta0,Certificate.sigmabar]
    push_cast
    simp only [base]
    linarith

theorem zero_identity (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) 0=
      base ep θ-R*(norms θ 0+norms θ 1+norms θ 2) := by
  have hz := (NegativeDEPositiveTD.Certificate.split_angles ep (Explicit.frame_domain .low hθ)).2.1
  have hc : 1≤Explicit.c .low θ (Explicit.splitT ep θ) := by
    linarith [(Explicit.low_c hθ hz).1,(Explicit.low_bounds hθ).2.1]
  simp only [Explicit.baseline,NegativeDEPositiveTD.Certificate.split_sum,
    Explicit.sec,NegativeELargeA.secant,Real.cos_zero,Real.tan_zero,div_one,
    sub_self,mul_zero,sub_zero,add_zero,zero_div,Explicit.l]
  rw [PositiveBT3.sortedSupport_diagonal hc]
  rw [fullSupport_pair (k θ) 1,fullSupport_pair 1 (k θ),fullSupport_pair (m θ) 1,
    pairNorm_symm 1 (k θ) 0,pairNorm_symm (m θ) 1 0]
  cases ep with
  | atA =>
    simp only [base,norms,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,Explicit.c,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,edgeWidth_zero,Real.cos_zero,
      Real.sin_zero,mul_zero,mul_one,add_zero,diagonalSupport]
    ring
  | atT =>
    simp only [base,norms,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,Explicit.c,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,TwoPositive.ASupport.charge_zero,
      mul_zero,add_zero,diagonalSupport]
    rw [edgeWidth_positive_formula (Explicit.frame_domain .low hθ)]
    ring

theorem equal_identity (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Real.cos θ*Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) θ=
      nonradical ep θ-R*(Real.cos θ*norms θ 0+Real.cos θ*norms θ 1+Real.cos θ*norms θ 2) := by
  have hf := Explicit.frame_domain .low hθ
  have hz := (NegativeDEPositiveTD.Certificate.split_angles ep hf).2.1
  have hc := (Explicit.source_coefficients .low hθ hz).2.2.2.2.1
  have hsc := LowNegative.secant_le_c hθ hz ⟨hθ.1,le_rfl⟩
  have hcos := NegativeESecant.cos_pos hf
  rw [Explicit.baseline_correction,NegativeDEPositiveTD.Certificate.split_sum,
    SecantD.PositiveEndpoint.correction_diagonal hc hf hsc,
    zero_identity ep hθ,NegativeESecant.gain_secant _ hf]
  dsimp [nonradical,NegativeESecant.K,Explicit.K,NegativeELargeA.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos.ne']
  ring

theorem nonradical_lower (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    aeval θ (Certificate.lowA ep)≤nonradical ep θ := by
  have ht := taylor_bounds (Explicit.frame_domain .low hθ)
  have hcos : 0≤Real.cos θ := (NegativeESecant.cos_pos (Explicit.frame_domain .low hθ)).le
  have hbase := mul_le_mul ht.2.2.2.2.1 (base_lower ep hθ)
    (Certificate.low_base_positive ep hθ).le hcos
  have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hD := r72_diag
  have hcoef := mul_le_mul_of_nonpos_right (sub_le_sub_right hD (1/2))
    (sub_nonpos.mpr (Real.cos_le_one θ))
  have hlower := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2.2.2.1 1)
    (show (0:ℝ)≤449607033/500000000-1/2 by norm_num)
  simp only [Certificate.lowA,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast,
    Certificate.K,Certificate.cbar]
  push_cast
  simp only [nonradical,Explicit.K]
  linarith

theorem norm_bound {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (i : Fin 3) :
    (Real.cos θ*norms θ i)^2≤aeval θ (Certificate.lowP i) := by
  have hf := Explicit.frame_domain .low hθ
  have hK : (pairNorm (k θ) 1 0)^2≤aeval θ (1+Certificate.lowK^2) := by
    rw [NonnegativeTotals.Analytic.norm_zero_square]
    simp only [map_add,map_one,map_pow,Certificate.lowK_eval]
    linarith
  have hM : (pairNorm 1 (m θ) 0)^2≤aeval θ (1+Certificate.lowM^2) := by
    rw [NonnegativeTotals.Analytic.norm_zero_square]
    simp only [map_add,map_one,map_pow,Certificate.lowM_eval]
    linarith
  obtain rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 := by revert i; decide
  · exact NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hK
  · exact NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hK
  · exact NegativeDEPositiveTD.Certificate.scaled_norm_bound hf hM

/-- Both split endpoints are positive for the sorted-D stress. -/
theorem equal_positive (ep : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<Explicit.baseline .low (Explicit.splitA ep θ) (Explicit.splitT ep θ) θ := by
  have hcos := NegativeESecant.cos_pos (Explicit.frame_domain .low hθ)
  have hn (i : Fin 3) : 0≤Real.cos θ*norms θ i :=
    mul_nonneg hcos.le (by fin_cases i <;> exact Real.sqrt_nonneg _)
  have hp := num3_transfer
    (Certificate.low_mass_positive 0 hθ) (Certificate.low_mass_positive 1 hθ)
    (Certificate.low_mass_positive 2 hθ) (hn 0) (hn 1) (hn 2)
    (norm_bound hθ 0) (norm_bound hθ 1) (norm_bound hθ 2)
    (nonradical_lower ep hθ) (Certificate.low_numerator_positive ep hθ)
  rw [←equal_identity ep hθ] at hp
  exact (mul_pos_iff_of_pos_left hcos).mp hp

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowEndpoints
end
end
end

section
/-!
## The complete low-total positive-B / negative-H rectangle

Curvature concavity and the six intrinsic
reference inequalities control the entire signed rectangle. First the
fixed worst coefficient corner is integrated. Concavity in the upper
positive angle and monotonicity in the larger coefficient then transfer
the result to every original low-family coefficient and both original
signed masses. No interior angle or coefficient sample is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowRectangle
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryNegativeSlope NegativeAPositiveTD.PositiveSlope NegativeAPositiveTD.Curvature

lemma phi_quadratic_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    PositiveAngularEnvelope.phi t≤1+t-t^2/2 := by
  have hc := cos_upper_four ht.1
  have hs := sin_upper_five ht.1
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hpoly : t/24-1/6+t^2/120≤0 := by
    dsimp [frameCap] at ht ht2
    nlinarith [ht.2]
  have hp := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1 3) hpoly
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith only [hc,hs,hp]

lemma B_curvature_line {t : ℝ} (ht : t∈Icc 0 frameCap) :
    741/1000+(63/200)*t<curvature R 1 M t := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => curvature R 1 M t-(741/1000+(63/200)*t)) := by
    apply concave_of_deriv2
      (f':=fun t => curvatureD R 1 M t-63/200)
      (f'':=fun t => -R*normD4 1 M t)
    · intro t ht
      have h1 := curvature_hasDerivAt (R:=R) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : (0:ℝ)<M) (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)
      have h2 : HasDerivAt (fun t : ℝ => 741/1000+(63/200)*t) ((63/200)*1) t :=
        ((hasDerivAt_id' t).const_mul (63/200)).const_add (741/1000)
      exact (h1.fun_sub h2).congr_deriv (by ring)
    · intro t ht
      exact (curvatureD_hasDerivAt (R:=R) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : (0:ℝ)<M)
        (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)).sub_const (63/200)
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
        (normD4_nonneg (by norm_num : (0:ℝ)<1) (by norm_num [M] : (1:ℝ)≤M)
          (by norm_num [M] : M≤2*(1:ℝ)) ht)
  have h0 : 0<curvature R 1 M 0-(741/1000+(63/200)*0) := by
    rw [curvature_zero]
    linarith [B_zero_curvature]
  have h1 : 0<curvature R 1 M frameCap-(741/1000+(63/200)*frameCap) := by
    have hb := B_cap_curvature
    rw [show (741/1000:ℝ)+(63/200)*frameCap=1923/2000 by norm_num [frameCap]]
    linarith
  have hh := concave_gt_of_endpoints hc ht h0 h1
  linarith

lemma B_second_lower {t : ℝ} (ht : t∈Icc 0 frameCap) :
    -(1/2:ℝ)<curvature R 1 M t-PositiveAngularEnvelope.phi t := by
  have hc := B_curvature_line ht
  have hp := phi_quadratic_upper ht
  nlinarith [sq_nonneg (t-137/200)]

lemma H_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature R k0 1 (-t)-Real.cos t< -(563/1000:ℝ) := by
  have hc := curvature_signed_tangent
    (by norm_num [k0] : (0:ℝ)<k0) (by norm_num [k0] : k0≤(1:ℝ))
    (by norm_num [k0] : (1:ℝ)≤2*k0)
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)
  have hC1 := mul_le_mul_of_nonneg_right H_zero_curvature_slope.le ht.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=t)
  have hquad := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hz := H_zero_curvature
  simp only [frameCap] at hquad
  nlinarith

def excess (N : ℝ) : ℝ := U R 1 M frameCap-U R 1 M (frameCap-N)+V R k0 1 N
def excessD (N : ℝ) : ℝ := Ud 1 M (frameCap-N)+Vd R k0 1 N

theorem excess_derivative {N : ℝ} (hN : N∈Icc 0 frameCap) :
    HasDerivAt excess (excessD N) N := by
  have h1 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) N := (hasDerivAt_id' N).const_sub frameCap
  have hd : HasDerivAt (fun x => U R 1 M (frameCap-x)) (Ud 1 M (frameCap-N)*-1) N :=
    (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt (t:=frameCap-N) (by norm_num : (0:ℝ)<1)
      (by norm_num [M] : (0:ℝ)<M) ⟨by linarith [hN.2],by linarith [hN.1]⟩).comp N h1
  have hv := OrdinaryNegativeSlope.V_hasDerivAt (R:=R) (by norm_num [k0] : (0:ℝ)<k0)
    (by norm_num : (0:ℝ)<1) hN
  exact ((hd.const_sub (U R 1 M frameCap)).fun_add hv).congr_deriv (by simp only [excessD]; ring)

theorem excessD_derivative {N : ℝ} (hN : N∈Icc 0 frameCap) :
    HasDerivAt excessD
      (-(curvature R 1 M (frameCap-N)-PositiveAngularEnvelope.phi (frameCap-N))+
        (curvature R k0 1 (-N)-Real.cos N)) N := by
  have h1 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) N := (hasDerivAt_id' N).const_sub frameCap
  have hd : HasDerivAt (fun x => Ud 1 M (frameCap-x))
      ((curvature R 1 M (frameCap-N)-1*PositiveAngularEnvelope.phi (frameCap-N))*-1) N :=
    (NegativeAPositiveTD.PositiveSlope.Ud_hasDerivAt (t:=frameCap-N) (by norm_num : (0:ℝ)<1)
      (by norm_num [M] : (0:ℝ)<M) ⟨by linarith [hN.2],by linarith [hN.1]⟩).comp N h1
  have hv := OrdinaryNegativeSlope.Vd_hasDerivAt (R:=R) (by norm_num [k0] : (0:ℝ)<k0)
    (by norm_num : (0:ℝ)<1) hN
  exact (hd.fun_add hv).congr_deriv (by ring)

theorem excessD_antitone : AntitoneOn excessD (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun N hN => (excessD_derivative hN).continuousAt.continuousWithinAt)
    (fun N hN => excessD_derivative (Ioo_subset_Icc_self hN))
  intro N hN
  have hb := B_second_lower
    (show frameCap-N∈Icc 0 frameCap from ⟨by linarith [hN.2],by linarith [hN.1]⟩)
  have hh := H_second_upper (Ioo_subset_Icc_self hN)
  linarith

theorem excessD_positive {N : ℝ} (hN : N∈Icc 0 frameCap) : 0<excessD N := by
  have hh := excessD_antitone hN
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hN.2
  have he : 0<excessD frameCap := by
    simp only [excessD,sub_self]
    linarith [B_positive_initial_slope,H_negative_cap_slope]
  exact he.trans_le hh

theorem corner_rectangle {N : ℝ} (hN : N∈Icc 0 frameCap) :
    U R 1 M (frameCap-N)≤U R 1 M frameCap+V R k0 1 N := by
  have hm : MonotoneOn excess (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun N hN => (excess_derivative hN).continuousAt.continuousWithinAt)
      (fun N hN => excess_derivative (Ioo_subset_Icc_self hN))
    intro N hN
    exact (excessD_positive (Ioo_subset_Icc_self hN)).le
  have hh := hm (by norm_num [frameCap]) hN hN.1
  simp only [excess,sub_zero,sub_self,V_zero,zero_add] at hh
  linarith

/-- Concavity moves only the scalar positive interval, not the source point. -/
lemma positive_increment_lower {m P N : ℝ} (hm : m∈Icc (1:ℝ) M)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    U R 1 M frameCap-U R 1 M (frameCap-N)≤U R 1 m P-U R 1 m (P-N) := by
  have hm0 : 0 < m := by linarith [hm.1]
  have hd (t : ℝ) (ht : t∈Icc 0 P) : HasDerivAt
      (fun t => (U R 1 m P-U R 1 m (P-t))-(U R 1 M frameCap-U R 1 M (frameCap-t)))
      (Ud 1 m (P-t)-Ud 1 M (frameCap-t)) t := by
    have h1 : HasDerivAt (fun x : ℝ => P-x) (-1) t := (hasDerivAt_id' t).const_sub P
    have h2 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) t :=
      (hasDerivAt_id' t).const_sub frameCap
    have hsmall : HasDerivAt (fun x => U R 1 m (P-x)) (Ud 1 m (P-t)*-1) t :=
      (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt (t:=P-t) (by norm_num : (0:ℝ)<1) hm0
        ⟨by linarith [ht.2],by linarith [ht.1]⟩).comp t h1
    have hlarge : HasDerivAt (fun x => U R 1 M (frameCap-x)) (Ud 1 M (frameCap-t)*-1) t :=
      (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt (t:=frameCap-t) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : (0:ℝ)<M) ⟨by linarith [ht.2],by linarith [ht.1]⟩).comp t h2
    exact ((hsmall.const_sub (U R 1 m P)).fun_sub
      (hlarge.const_sub (U R 1 M frameCap))).congr_deriv (by ring)
  have hmono : MonotoneOn
      (fun t => (U R 1 m P-U R 1 m (P-t))-(U R 1 M frameCap-U R 1 M (frameCap-t)))
      (Icc 0 P) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
    intro t ht
    have hx : P-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hy : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have ha := Ud_antitone (p:=(1:ℝ)) (q:=M) (by norm_num) (by norm_num [M])
      (by norm_num [M]) hx hy (by linarith)
    have hc := NegativeDEPositiveTD.LowPositive.larger_comparison
      (by norm_num : (0:ℝ)<1) hm0 hm.2 hx
    exact sub_nonneg.mpr (ha.trans hc)
  have hh := hmono (show (0:ℝ)∈Icc 0 P from ⟨le_rfl,hN.trans hNP⟩) ⟨hN,hNP⟩ hN
  simp only [sub_zero,sub_self] at hh
  linarith

/-- Full coefficient and signed-mass rectangle used by the low family. -/
theorem original_rectangle {k m P N : ℝ}
    (hk : k∈Icc k0 1) (hm : m∈Icc (1:ℝ) M)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    U R 1 m (P-N)≤U R 1 m P+V R k 1 N := by
  have hn : N∈Icc 0 frameCap := ⟨hN,hNP.trans hP⟩
  have hc := corner_rectangle hn
  have hp := positive_increment_lower hm hN hNP hP
  have hv := PositiveTD.V_first_coefficient (q:=(1:ℝ)) (by norm_num)
    (by norm_num [k0] : (1:ℝ)/2≤k0) hk.1 (by linarith [hk.2]) hn
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowRectangle
end
end
end

section
/-!
## Complete low-total concentration when the positive mass is larger

H/G positive allocations use the whole-angle
slope reserve. The original D singleton uses its secant-dependent cost,
not an ordinary substitute. The only remaining B/H allocation is the
proved whole rectangle. Negative B and D are compared with H at their
actual angle, and all weak zero-mass and same-block ties are included.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open NegativeAPositiveTD.PositiveSlope

lemma H_linear_lower {θ t : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (ht : t∈Icc 0 frameCap) : (77/100)*t≤V R (Explicit.k .low θ) 1 t := by
  have hr := Explicit.low_bounds hθ
  have hk0 : 0<Explicit.k .low θ := by linarith [hr.1.1]
  have hk1 : Explicit.k .low θ≤1 := by linarith [hr.1.2]
  have h1k : (1:ℝ)≤2*Explicit.k .low θ := by linarith [hr.1.1]
  have hcap := PositiveBT3.LowSecants.J_linear_lower (k:=Explicit.k .low θ) hr.1
  simp only [PositiveBT3.LowSecants.J] at hcap
  have hc := V_concave (R:=R) (p:=Explicit.k .low θ) (q:=1) (Real.sqrt_nonneg qCap)
    radius_sq.le hk0 hk1 h1k
  have hlinear : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => V R (Explicit.k .low θ) 1 t-(77/100)*t) := by
    refine ⟨hc.1,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    linarith
  have he : 0≤V R (Explicit.k .low θ) 1 frameCap-(77/100)*frameCap := by
    rw [show (77/100:ℝ)*frameCap=539/1000 by norm_num [frameCap]]
    simp only [PositiveBT3.LowSecants.k0] at hcap
    linarith [hr.1.1]
  have hh := hlinear.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  simp only [V_zero,mul_zero,sub_zero,min_eq_left he] at hh
  linarith

lemma H_positive_increment {θ P N : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    -(18/25)*N≤U R (Explicit.k .low θ) 1 P-U R (Explicit.k .low θ) 1 (P-N) := by
  have hr := Explicit.low_bounds hθ
  have hk0 : 0<Explicit.k .low θ := by linarith [hr.1.1]
  have hk1 : Explicit.k .low θ≤1 := by linarith [hr.1.2]
  have h1k : (1:ℝ)≤2*Explicit.k .low θ := by linarith [hr.1.1]
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :
      HasDerivAt (U R (Explicit.k .low θ) 1) (Ud (Explicit.k .low θ) 1 t) t :=
    U_hasDerivAt hk0 (by norm_num : (0:ℝ)<1) ht
  have hh := derivative_reserve
    (f:=U R (Explicit.k .low θ) 1) (df:=Ud (Explicit.k .low θ) 1) (k:=-(18/25:ℝ))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have h := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole
        (p:=Explicit.k .low θ) (q:=1) hk0 hk1 h1k (Ioo_subset_Icc_self ht)
      linarith)
    (show P-N∈Icc 0 frameCap from ⟨by linarith,by linarith⟩)
    (show P∈Icc 0 frameCap from ⟨hN.trans hNP,hP⟩) (by linarith)
  rw [show P-(P-N)=N by ring] at hh
  exact hh

lemma gamma_upper {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) :
    Explicit.gamma .low θ z s≤77/100 := by
  have hsec := (NegativeELargeA.secant_range hs).2
  have hc := (Explicit.low_c hθ hz).2
  have hmax : max (Explicit.sec s) (Explicit.c .low θ z)≤(327/250:ℝ) :=
    max_le (by simpa [SecantD.qUpper] using hsec) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hmax (by norm_num [SecantD.slope] : 0≤SecantD.slope)
  dsimp [Explicit.gamma,SecantD.slope] at hh ⊢
  linarith

lemma separated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i j : Fin 4) :
    Blocks.positive .low θ z s (s-θ) i≤
      Blocks.positive .low θ z s (frameCap-θ) i+
        Blocks.negative .low θ (frameCap-s) j := by
  have ht := Explicit.frame_domain .low hθ
  have hsf : s∈Icc 0 frameCap := ⟨ht.1.trans hs.1,hs.2⟩
  have hP : 0≤frameCap-θ := sub_nonneg.mpr ht.2
  have hN : 0≤frameCap-s := sub_nonneg.mpr hs.2
  have hNP : frameCap-s≤frameCap-θ := by linarith [hs.1]
  have hPcap : frameCap-θ≤frameCap := by linarith [ht.1]
  have hn : frameCap-s∈Icc 0 frameCap := ⟨hN,by linarith [hsf.1]⟩
  have hH := LowNegative.negative_comparison hθ hn j
  have hlinear := H_linear_lower hθ hn
  have hr := Explicit.low_bounds hθ
  have hm : 1≤Explicit.m .low θ := by linarith [hr.2.1]
  have hdiff : frameCap-θ-(frameCap-s)=s-θ := by ring
  obtain rfl|rfl|rfl|rfl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by revert i; decide
  · have hh := H_positive_increment hθ hN hNP hPcap
    rw [hdiff] at hh
    rw [show (0:Fin 4)=Fin.castSucc (0:Fin 3) from rfl,Blocks.positive_ordinary,
      Blocks.positive_ordinary]
    change U R (Explicit.k .low θ) 1 (s-θ)≤
      U R (Explicit.k .low θ) 1 (frameCap-θ)+_
    generalize frameCap=F at hh hH hlinear hN ⊢
    linarith
  · have hh := H_positive_increment hθ hN hNP hPcap
    rw [hdiff] at hh
    rw [show (1:Fin 4)=Fin.castSucc (1:Fin 3) from rfl,Blocks.positive_ordinary,
      Blocks.positive_ordinary]
    change U R (Explicit.k .low θ) 1 (s-θ)≤
      U R (Explicit.k .low θ) 1 (frameCap-θ)+_
    generalize frameCap=F at hh hH hlinear hN ⊢
    linarith
  · have hh := LowRectangle.original_rectangle
      (k:=Explicit.k .low θ) (m:=Explicit.m .low θ)
      (show Explicit.k .low θ∈Icc LowRectangle.k0 1 from
        ⟨hr.1.1,by linarith [hr.1.2]⟩)
      (show Explicit.m .low θ∈Icc (1:ℝ) LowRectangle.M from ⟨hm,hr.2.2⟩)
      hN hNP hPcap
    rw [hdiff] at hh
    rw [show (2:Fin 4)=Fin.castSucc (2:Fin 3) from rfl,Blocks.positive_ordinary,
      Blocks.positive_ordinary]
    change U R (min (Explicit.l .low θ) (Explicit.m .low θ))
        (max (Explicit.l .low θ) (Explicit.m .low θ)) (s-θ)≤
      U R (min (Explicit.l .low θ) (Explicit.m .low θ))
        (max (Explicit.l .low θ) (Explicit.m .low θ)) (frameCap-θ)+_
    have hl : Explicit.l .low θ=1 := rfl
    rw [hl,min_eq_left hm,max_eq_right hm]
    linarith
  · rw [Blocks.positive_D,Blocks.positive_D]
    have hgamma := mul_le_mul_of_nonneg_right (gamma_upper hθ hz hsf) hN
    generalize frameCap=F at hgamma hH hlinear ⊢
    linarith

theorem saturated_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap) (i j : Fin 4) :
    Blocks.pure .low θ z s i j≤Blocks.saturated .low θ z s i j := by
  have hsf : s∈Icc 0 frameCap := ⟨(Explicit.frame_domain .low hθ).1.trans hs.1,hs.2⟩
  have hpure (i j : Fin 4) :
      Blocks.pure .low θ z s i j=Blocks.positive .low θ z s (s-θ) i := by
    by_cases hst : s≤θ
    · have he : s=θ := le_antisymm hst hs.1
      subst he
      simp only [Blocks.pure,ChargedHybridConcentration.pure,le_refl,↓reduceIte,sub_self,
        V_zero,Blocks.positive_zero]
    · show (if s≤θ then _ else _)=_
      rw [ite_eq_right hst]
      rfl
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have he : Blocks.saturated .low θ z s 3 3=
          Blocks.block .low θ z s (frameCap-θ) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,Blocks.block,
          ↓reduceIte]
      rw [he,Blocks.block_D,hpure]
      exact separated_lower hθ hz hs 3 3
    · have hi3 : i.val≠3 := fun h => hi (Fin.ext h)
      obtain ⟨r,hr⟩ : ∃r : Fin 3,r.castSucc=i :=
        ⟨⟨i.val,by have := i.isLt; omega⟩,Fin.ext rfl⟩
      subst i
      exact SameBlock.ordinary_saturated_lower .low hθ hsf r
  · have he : Blocks.saturated .low θ z s i j=
        Blocks.positive .low θ z s (frameCap-θ) i+Blocks.negative .low θ (frameCap-s) j := by
      simp only [Blocks.saturated,ChargedHybridConcentration.saturated,hij,↓reduceIte]
      rfl
    rw [he,hpure]
    exact separated_lower hθ hz hs i j

theorem sum_to_pure {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (hs : s∈Icc θ frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,Blocks.pure .low θ z s i j≤∑k,Blocks.block .low θ z s (P k) (N k) k := by
  have hsf : s∈Icc 0 frameCap := ⟨(Explicit.frame_domain .low hθ).1.trans hs.1,hs.2⟩
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .low P N hθ hsf hP hN hPb hNb hbalance
  rw [min_eq_left (saturated_lower hθ hz hs i j)] at hij
  exact ⟨i,j,hij⟩

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.LowPositive
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Low
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev gain := NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2)

lemma zero_scalar_identity {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) :
    Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) 1 (a+z)=
      PositiveBT3.Analytic.lowScalar (a+z) a := by
  have hc := (Explicit.low_c hθ ⟨hz,by linarith⟩).1
  have hm := (Explicit.low_bounds hθ).2.1
  have hc1 : 1≤Explicit.c .low (a+z) z := by linarith
  have hs (k : ℝ) : fullSupport 1 k=fullSupport k 1 := by
    unfold fullSupport; rw [add_comm ((1:ℝ)^2) (k^2),add_comm (1:ℝ) k]
  simp only [Explicit.baseline,Explicit.sec,NegativeELargeA.secant,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,add_zero]
  rw [PositiveBT3.sortedSupport_diagonal hc1]
  simp only [PositiveBT3.Analytic.lowScalar,PositiveBT3.Analytic.lowBaseline,
    show a+z-a=z by ring,Explicit.c,Explicit.eta,Explicit.sigma,PositiveBT3.tilted,
    PositiveTD.sigma,PositiveTD.eta,Explicit.k,Explicit.l,Explicit.m,one_mul,diagonalSupport]
  rw [hs (PositiveBT3.lowK (a+z))]
  ring

lemma diagonal_correction {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 (a+z)) :
    Explicit.baseline .low a z s=Explicit.baseline .low a z 0+gain s := by
  have hc := (Explicit.source_coefficients .low hθ ⟨hz,by linarith⟩).2.2.2.2.1
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans (Explicit.frame_domain .low hθ).2⟩
  rw [Explicit.baseline_correction,
    SecantD.PositiveEndpoint.correction_diagonal hc hsf (LowNegative.secant_le_c hθ ⟨hz,by linarith⟩ hs)]

lemma gain_concave : ConcaveOn ℝ (Icc (0:ℝ) (1/6)) gain := by
  apply concave_of_deriv2
    (fun s hs => NegativeESecant.gain_hasDerivAt (GlobalGA.Secondary.diagonal-1/2)
      (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩))
    (fun s hs => NegativeESecant.gainD_hasDerivAt (GlobalGA.Secondary.diagonal-1/2)
      (show s∈Icc 0 frameCap from ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩))
  intro s hs
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  have hsin : Real.sin s≤1/6 := (Real.sin_le hs.1).trans hs.2
  have hcoef : 0≤GlobalGA.Secondary.diagonal-1/2 := by linarith [diagonal_bounds.1]
  have hsquare := mul_nonneg hcoef (sq_nonneg (Real.sin s))
  have hnum : 2*NegativeESecant.K*Real.sin s-(GlobalGA.Secondary.diagonal-1/2)*(1+Real.sin s^2)≤0 := by
    dsimp [NegativeESecant.K]
    nlinarith [diagonal_bounds.1]
  exact div_nonpos_of_nonpos_of_nonneg hnum
    (pow_nonneg (NegativeESecant.cos_pos hsf).le 3)

lemma equal_split_concave {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    ConcaveOn ℝ (Icc 0 θ) (fun a => Explicit.baseline .low a (θ-a) θ) := by
  have hc := TwoPositive.Split.add_constant (PositiveBT3.Analytic.lowScalar_concave hθ)
    (gain θ-V R (Explicit.k .low θ) 1 θ)
  apply TwoPositive.Split.congr_on hc
  intro a ha
  have ht : a+(θ-a)∈Icc (0:ℝ) (1/6) := by simpa only [add_sub_cancel] using hθ
  have hz : 0≤θ-a := sub_nonneg.mpr ha.2
  have hzero := zero_scalar_identity ht ha.1 hz
  have hcor := diagonal_correction ht ha.1 hz
    (show θ∈Icc 0 (a+(θ-a)) by simpa only [add_sub_cancel] using ⟨hθ.1,le_rfl⟩)
  simp only [add_sub_cancel] at hzero hcor
  linarith

theorem equal_positive {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) : 0<Explicit.baseline .low a z (a+z) := by
  have hc := equal_split_concave hθ
  have h0 := LowEndpoints.equal_positive .atT hθ
  have h1 := LowEndpoints.equal_positive .atA hθ
  have hh := concave_gt_of_endpoints hc
    (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    (by simpa only [NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      sub_zero] using h0)
    (by simpa only [NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      sub_self] using h1)
  simpa only [show a+z-a=z by ring] using hh

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/6))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 (a+z)) :
    0<Explicit.baseline .low a z s+V R (Explicit.k .low (a+z)) 1 (a+z-s) := by
  have hr := Explicit.low_bounds hθ
  have hk0 : 0<Explicit.k .low (a+z) := by linarith [hr.1.1]
  have hk1 : Explicit.k .low (a+z)≤1 := by linarith [hr.1.2]
  have h1k : (1:ℝ)≤2*Explicit.k .low (a+z) := by linarith [hr.1.1]
  have hg := gain_concave.subset (Icc_subset_Icc le_rfl hθ.2) (convex_Icc 0 (a+z))
  have hV := V_concave (R:=R) (p:=Explicit.k .low (a+z)) (q:=1) (Real.sqrt_nonneg qCap)
    radius_sq.le hk0 hk1 h1k
  have hv := concave_affine_argument hV (a:=-1) (b:=a+z) (l:=0) (u:=a+z)
    (fun s hs => ⟨by linarith [hs.2],by norm_num [frameCap]; linarith [hs.1,hθ.2]⟩)
  have hc := TwoPositive.Split.add_constant (hg.add hv) (Explicit.baseline .low a z 0)
  have hcF : ConcaveOn ℝ (Icc 0 (a+z))
      (fun s => gain s+V R (Explicit.k .low (a+z)) 1 (a+z-s)+Explicit.baseline .low a z 0) := by
    apply TwoPositive.Split.congr_on hc
    intro x _
    simp only [Pi.add_apply]
    rw [show -1*x+(a+z)=a+z-x by ring]
  have h0 : 0<gain 0+V R (Explicit.k .low (a+z)) 1 (a+z-0)+Explicit.baseline .low a z 0 := by
    have hh := PositiveBT3.Analytic.low_scalar_positive hθ
      (show a∈Icc 0 (a+z) from ⟨ha,by linarith⟩)
    rw [←zero_scalar_identity hθ ha hz] at hh
    simp only [gain,NegativeESecant.gain_zero,sub_zero]
    linarith
  have h1 : 0<gain (a+z)+V R (Explicit.k .low (a+z)) 1 (a+z-(a+z))+
      Explicit.baseline .low a z 0 := by
    have hh := equal_positive hθ ha hz
    rw [diagonal_correction hθ ha hz ⟨hθ.1,le_rfl⟩] at hh
    simp only [sub_self,V_zero,add_zero]
    linarith
  have hh := concave_gt_of_endpoints hcF hs h0 h1
  rw [diagonal_correction hθ ha hz hs]
  linarith

/-- Complete closed low-total scalar domain, including both surplus signs. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline .low a z s+
      ∑i,Blocks.block .low (a+z) z s (P i) (N i) i := by
  have hzd : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  by_cases hst : s≤a+z
  · have hb := LowNegative.sum_to_H P N hθ hzd ⟨hs.1,hst⟩ hP hN hPb hNb hbalance
    have hp := negative_positive hθ ha hz ⟨hs.1,hst⟩
    linarith
  · have hsf : s∈Icc (a+z) frameCap := ⟨(lt_of_not_ge hst).le,hs.2⟩
    obtain ⟨i,j,hij⟩ := LowPositive.sum_to_pure P N hθ hzd hsf hP hN hPb hNb hbalance
    have hp := equal_positive hθ ha hz
    have hc := PositivePure.pure_intrinsic_lower .low hθ ha hz hsf i j
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Low
end
end
end
