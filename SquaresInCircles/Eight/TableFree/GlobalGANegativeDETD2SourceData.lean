module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2HighSplit
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeASourceData

/-!
# The original negative-DE3 / positive-TD2 stress data

Uncompiled transcription of equations (5)--(10).  DE carries its own
secant, EH keeps multiplier one, and both selected A primaries retain
their original signs.  Only the selected A arguments, TD and DE are
deleted from the three actual H/G/B circle blocks.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
open Candidate Secondary PositiveAngularEnvelope ActualOrdinaryBlocks PairedE
open NegativePrimary (erase)

abbrev aTotal := LowA.aTotal
abbrev selectedA := NegativeELargeA.Source.selectedA

def total (C : SignedCycle) (ga ab : Bool) : ℝ := aTotal C ga ab+delta C.theta T
def magnitude (C : SignedCycle) : ℝ := -delta C.theta D

def owners (hg ga ab : Bool) : Vertex→Fin 4 :=
  ![if hg then 2 else 0,if ga then 3 else 2,if ab then 2 else 0,2,2,3,0]
def weights (C : SignedCycle) (k l c : ℝ) : Vertex→ℝ :=
  ![k,l,l,PositiveTD.tilted c (delta C.theta T),c,1/Real.cos (delta C.theta D),1]
def stress (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : ℝ :=
  ∑i,weights C k l c i*(edgeWidth (delta C.theta i)-C.edge i (owners hg ga ab i))

def blocks (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Fin 3→Block :=
  ![⟨k,1,erase (!hg) (delta C.theta H),delta C.theta E⟩,
    ⟨k,l,erase hg (delta C.theta H),erase ga (delta C.theta G)⟩,
    ⟨l,PositiveTD.tilted c (delta C.theta T),erase ab (delta C.theta A),delta C.theta B⟩]
def actualBlocks (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Fin 3→ℝ :=
  ![PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 0) (C.point H),
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 1) (C.point G).reflect,
    PositiveTD.actualPairIncrement (blocks C hg ga ab k l c 2) (C.point B).reflect]

def deCorrection (C : SignedCycle) : ℝ :=
  (edgeWidth (delta C.theta D)-(7/12)*Real.sin (delta C.theta D))/
    Real.cos (delta C.theta D)-1/Real.cos (delta C.theta D)
def base (C : SignedCycle) (k l c : ℝ) : ℝ :=
  k+2*l+PositiveTD.tilted c (delta C.theta T)+c*edgeWidth (delta C.theta T)+
    1/Real.cos (delta C.theta D)+1-c*PositiveTD.sigma*Real.sin (delta C.theta T)-
    fullSupport 1 k-fullSupport l k-fullSupport (PositiveTD.tilted c (delta C.theta T)) l-
    clippedSupport (1/Real.cos (delta C.theta D)) c+deCorrection C
def dReserve (C : SignedCycle) (c : ℝ) : ℝ :=
  clippedSupport (1/Real.cos (delta C.theta D)) c-
    ((C.point D).a/Real.cos (delta C.theta D)+c*(-(C.point D).y))

theorem decomposition (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ)
    (hflat : (C.point E).a=7/12) (hcos : Real.cos (delta C.theta D)≠0) :
    stress C hg ga ab k l c=base C k l c+(∑i,actualBlocks C hg ga ab k l c i)+
      l*primaryGain (C.point A) ga ab (delta C.theta G) (delta C.theta A)+
      PositiveTD.tReserve C c+dReserve C c := by
  have hf : (C.point 6).a=7/12 := hflat
  have hu : Real.cos (C.theta 6-C.theta 5)*(Real.cos (C.theta 6-C.theta 5))⁻¹=1 :=
    mul_inv_cancel₀ hcos
  cases hg <;> cases ga <;> cases ab <;>
    simp [stress,weights,owners,blocks,actualBlocks,base,deCorrection,dReserve,
      PositiveTD.actualPairIncrement,PositiveTD.tReserve,PositiveTD.tilted,pairF,pairG,
      primaryGain,erase,hf,SignedCycle.edge,zeroProjection,quarterProjection,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,SignedPoint.reflect] <;>
    linear_combination (C.point 6).y*hu

theorem sum_parts (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg ga ab k l c i).u+f (blocks C hg ga ab k l c i).v))=
      (∑i,f (delta C.theta i))-selectedA C ga ab f-
        f (delta C.theta T)-f (delta C.theta D) := by
  cases hg <;> cases ga <;> cases ab <;>
    simp [blocks,erase,selectedA,NegativeELargeA.Source.selectedA,selected,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budgets (C : SignedCycle) (hg ga ab : Bool) (k l c : ℝ) : Prop where
  total_domain : total C ga ab∈Icc 0 frameCap
  a_domain : aTotal C ga ab∈Icc 0 (total C ga ab)
  td_domain : delta C.theta T∈Icc 0 (total C ga ab)
  de_domain : magnitude C∈Icc 0 frameCap
  positive_bound : (∑i,(blocks C hg ga ab k l c i).P)≤frameCap-total C ga ab
  negative_bound : (∑i,(blocks C hg ga ab k l c i).N)≤frameCap-magnitude C
  balance : (∑i,(blocks C hg ga ab k l c i).N)-(∑i,(blocks C hg ga ab k l c i).P)=
    total C ga ab-magnitude C

theorem budgets {C : SignedCycle} (hg ga ab : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap) (ha : 0≤aTotal C ga ab)
    (hz : 0≤delta C.theta T) (hs : delta C.theta D≤0) : Budgets C hg ga ab k l c := by
  have hp := sum_parts C hg ga ab k l c positivePart positivePart_zero
  have hn := sum_parts C hg ga ab k l c negativePart negativePart_zero
  have hA := NegativeELargeA.Source.selectedA_signed C ga ab
  have hAP := NegativeELargeA.Source.selectedA_nonnegative C ga ab positivePart positivePart_nonneg
  have hAN := NegativeELargeA.Source.selectedA_nonnegative C ga ab negativePart negativePart_nonneg
  have hzP : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hzN : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hsP : positivePart (delta C.theta D)=0 := max_eq_right hs
  have hsN : negativePart (delta C.theta D)=magnitude C := max_eq_left (neg_nonneg.mpr hs)
  have hP : (∑i,(blocks C hg ga ab k l c i).P)=
      positiveVariation C.theta-selectedA C ga ab positivePart-delta C.theta T := by
    simpa only [Block.P,hzP,hsP,sub_zero,positiveVariation] using hp
  have hN : (∑i,(blocks C hg ga ab k l c i).N)=
      negativeVariation C.theta-selectedA C ga ab negativePart-magnitude C := by
    simpa only [Block.N,hzN,hsN,sub_zero,negativeVariation] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg ga ab k l c i).N_nonneg)
  have heq := variations_equal C.theta
  have hs0 : 0≤ magnitude C := neg_nonneg.mpr hs
  change selectedA C ga ab positivePart-selectedA C ga ab negativePart=aTotal C ga ab at hA
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [total]; exact ⟨add_nonneg ha hz,by linarith⟩
  · dsimp [total]; exact ⟨ha,by linarith⟩
  · dsimp [total]; exact ⟨hz,by linarith⟩
  · exact ⟨hs0,by linarith⟩
  · dsimp [total]; linarith
  · linarith
  · dsimp [total]; linarith

theorem block_coefficients {C : SignedCycle} (hg ga ab : Bool) {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 3) :
    (blocks C hg ga ab k l c i).p=(![k,k,min l (PositiveTD.tilted c (delta C.theta T))] : Fin 3→ℝ) i ∧
    (blocks C hg ga ab k l c i).q=(![1,l,max l (PositiveTD.tilted c (delta C.theta T))] : Fin 3→ℝ) i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,min_eq_left hk,max_eq_right hk,
    min_eq_left hl,max_eq_right hl]

theorem family_coefficients (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (hz : z∈Icc 0 θ) :
    Explicit.k f θ≤1 ∧ Explicit.k f θ≤Explicit.l f θ ∧
      (∀i,0<Explicit.p f θ z i ∧ Explicit.p f θ z i≤Explicit.q f θ z i ∧
        Explicit.q f θ z i≤2*Explicit.p f θ z i) := by
  cases f
  · have hr := Explicit.low_ranges hθ
    have hm := Explicit.low_tilted hθ hz
    have hk : 0<Explicit.k .low θ := by linarith [hr.1]
    have hl : 0<Explicit.l .low θ := by linarith [hr.2.2.1]
    have hlm : Explicit.l .low θ≤Explicit.m .low θ z := hr.2.2.2.2.2.2.1.trans hm.1
    refine ⟨by linarith [hr.2.1],by linarith [hr.2.1,hr.2.2.1],?_⟩
    intro i
    fin_cases i
    · show 0<Explicit.k .low θ ∧ Explicit.k .low θ≤1 ∧ 1≤2*Explicit.k .low θ
      exact ⟨hk,by linarith [hr.2.1],by linarith [hr.1]⟩
    · show 0<Explicit.k .low θ ∧ Explicit.k .low θ≤Explicit.l .low θ ∧
        Explicit.l .low θ≤2*Explicit.k .low θ
      exact ⟨hk,by linarith [hr.2.1,hr.2.2.1],hr.2.2.2.2.2.2.2.le⟩
    · show 0 < min (Explicit.l .low θ) (Explicit.m .low θ z) ∧
        min (Explicit.l .low θ) (Explicit.m .low θ z) ≤ max (Explicit.l .low θ) (Explicit.m .low θ z) ∧
        max (Explicit.l .low θ) (Explicit.m .low θ z) ≤ 2*min (Explicit.l .low θ) (Explicit.m .low θ z)
      rw [min_eq_left hlm,max_eq_right hlm]
      exact ⟨hl,hlm,by linarith [hm.2]⟩
  · have hr := Explicit.high_ranges hθ
    refine ⟨by linarith [hr.2.1],by linarith [hr.2.1,hr.2.2.1],?_⟩
    intro i
    have hh := Explicit.high_pairs hθ hz i
    exact ⟨hh.1,hh.2.1,by linarith [hh.2.2.1]⟩

theorem family_block_coefficients {C : SignedCycle} (hg ga ab : Bool) (f : Family)
    (hθ : total C ga ab∈Icc (Explicit.left f) (Explicit.right f))
    (hz : delta C.theta T∈Icc 0 (total C ga ab)) (i : Fin 3) :
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.c f (total C ga ab)) i).p=Explicit.p f (total C ga ab) (delta C.theta T) i ∧
    (blocks C hg ga ab (Explicit.k f (total C ga ab)) (Explicit.l f (total C ga ab))
      (Explicit.c f (total C ga ab)) i).q=Explicit.q f (total C ga ab) (delta C.theta T) i := by
  have hh := family_coefficients f hθ hz
  simpa only [Explicit.p,Explicit.q,Explicit.m,Explicit.eta,PositiveTD.tilted,PositiveTD.eta]
    using block_coefficients hg ga ab (c:=Explicit.c f (total C ga ab)) hh.1 hh.2.1 i

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.Source
