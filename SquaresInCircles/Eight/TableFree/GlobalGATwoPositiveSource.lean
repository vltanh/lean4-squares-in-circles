module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveScalar
public import SquaresInCircles.Eight.TableFree.GlobalGASource

/-!
# The two-positive contradiction on the original weak axes

Uncompiled transcription of the force collection and final application
in the two-positive intermediate-error hand theorem.  The A-primary
flag selects GA3/AB0 or GA2/AB2.  Its actual nonnegative error and the
actual TD2 error are deleted only from the analytic norm blocks.  All
seven physical inequalities, original points and signs remain unchanged.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive
namespace Source
open Candidate Secondary PositiveTD PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks SignedStress

def aError (C : SignedCycle) (atG : Bool) : ℝ :=
  if atG then delta C.theta G else delta C.theta A

def total (C : SignedCycle) (atG : Bool) : ℝ := aError C atG+delta C.theta T

def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,2,0]

def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,l,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨l,tilted c (delta C.theta T),if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

def actualStress (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : ℝ :=
  demand C (weights k l c (delta C.theta T))-
    ∑i,work (force C (owners hg atG) (weights k l c (delta C.theta T)) i) (C.point i)

def actualBlocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ) : Fin 4→ℝ :=
  ![actualPairIncrement (blocks C hg atG k l c 0) (C.point H),
    actualPairIncrement (blocks C hg atG k l c 1) (C.point G).reflect,
    actualPairIncrement (blocks C hg atG k l c 2) (C.point B).reflect,
    actualDIncrement c (delta C.theta D) (C.point D).reflect]

def aWork (C : SignedCycle) (atG : Bool) : ℝ :=
  (C.point A).a*Real.sin (aError C atG)+(C.point A).y*
    (if atG then 1-Real.cos (aError C atG) else Real.cos (aError C atG)-1)

def aReserve (C : SignedCycle) (atG : Bool) (l : ℝ) : ℝ :=
  l*(edgeWidth (aError C atG)-1-aWork C atG-ASupport.charge (aError C atG))

theorem a_reserve_nonneg {q l : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : (C.point A).Sorted) (hc : (C.point A).Contained q) (hq : q≤qCap)
    (hl : 0≤l) (ha : aError C atG∈Icc 0 frameCap) : 0≤aReserve C atG l := by
  have hh := ASupport.actual_charge hs hc hq ha atG
  exact mul_nonneg hl (by dsimp [aWork] at *; linarith)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG : Bool)
    (hhg : hg=0 ∨ hg=2) (k l c : ℝ) :
    actualStress C hg atG k l c=
      baseline k l c (delta C.theta T)+l*ASupport.charge (aError C atG)+
        (∑i,actualBlocks C hg atG k l c i)+tReserve C c+aReserve C atG l := by
  cases atG <;> rcases hhg with rfl | rfl <;>
    simp [actualStress,demand,force,source,target,work,add,scale,
      previous,owners,weights,blocks,actualBlocks,actualPairIncrement,
      actualDIncrement,pairF,pairG,tReserve,baseline,tilted,aReserve,aWork,aError,
      Fin.sum_univ_succ,word,delta,next,H,G,A,B,T,D,E,
      SignedPoint.reflect,edgeWidth,pairWidth] <;> ring

theorem stress_nonpos {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
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
  exact sub_nonpos.mpr (weighted_separation (weights_nonneg hk hl hc hz) hf)

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (atG : Bool) {k l c : ℝ}
    (hk : k≤1) (hl : k≤l) (i : Fin 4) :
    (blocks C hg atG k l c i).p=pWeights k l (tilted c (delta C.theta T)) i ∧
      (blocks C hg atG k l c i).q=qWeights k l (tilted c (delta C.theta T)) i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,pWeights,qWeights,min_eq_left hk,max_eq_right hk,
      min_eq_left hl,max_eq_right hl]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG k l c i).u+f (blocks C hg atG k l c i).v))=
      (∑j,f (delta C.theta j))-f (delta C.theta T)-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : 0≤delta C.theta T) :
    total C atG∈Icc 0 frameCap ∧ aError C atG∈Icc 0 (total C atG) ∧
      delta C.theta T∈Icc 0 frameCap ∧
      (∑i,(blocks C hg atG k l c i).P)≤frameCap-total C atG ∧
      (∑i,(blocks C hg atG k l c i).N)=total C atG+∑i,(blocks C hg atG k l c i).P := by
  have hp := sum_parts C hg atG k l c positivePart positivePart_zero
  have hn := sum_parts C hg atG k l c negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hpa : positivePart (aError C atG)=aError C atG := max_eq_left ha
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=0 := max_eq_right (by linarith)
  have hp' : (∑i,(blocks C hg atG k l c i).P)=positiveVariation C.theta-total C atG := by
    change (∑i,(positivePart (blocks C hg atG k l c i).u+
      positivePart (blocks C hg atG k l c i).v))=_
    simp only [hpz,hpa] at hp
    simp only [positiveVariation]
    dsimp [total]
    linarith
  have hn' : (∑i,(blocks C hg atG k l c i).N)=negativeVariation C.theta := by
    change (∑i,(negativePart (blocks C hg atG k l c i).u+
      negativePart (blocks C hg atG k l c i).v))=_
    simpa only [hnz,hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c i).P_nonneg)
  have heq := variations_equal C.theta
  have ht0 : 0≤total C atG := add_nonneg ha hz
  have htotal : total C atG≤frameCap := by linarith
  have hat : aError C atG≤total C atG := by dsimp [total]; linarith
  have hzt : delta C.theta T≤total C atG := by dsimp [total]; linarith
  exact ⟨⟨ht0,htotal⟩,⟨ha,hat⟩,⟨hz,hzt.trans htotal⟩,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : 0≤delta C.theta T) (i : Fin 4) :
    (blocks C hg atG k l c i).P≤frameCap ∧ (blocks C hg atG k l c i).N≤frameCap := by
  have hb := original_budgets hg atG k l c hvar ha hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c j).N_nonneg) (Finset.mem_univ i)
  constructor <;> linarith [hb.1.1,hb.2.2.2.1,hb.2.2.2.2]

theorem block_family_lower {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : 0≤delta C.theta T)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*tilted c (delta C.theta T) ∧ tilted c (delta C.theta T)≤2*l)
    (i : Fin 4) :
    Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (pWeights k l (tilted c (delta C.theta T)))
      (qWeights k l (tilted c (delta C.theta T))) 3 i
      (blocks C hg atG k l c i).P (blocks C hg atG k l c i).N≤
        actualBlocks C hg atG k l c i := by
  have hb := original_budgets hg atG k l c hvar ha hz
  have hw := coefficient_domain hk hl hcoef hb.2.2.1 hratio
  have hordinary (i : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R (pWeights k l (tilted c (delta C.theta T)) i)
        (qWeights k l (tilted c (delta C.theta T)) i)
        (blocks C hg atG k l c i).P (blocks C hg atG k l c i).N≤
          actualPairIncrement (blocks C hg atG k l c i) P := by
    have hd := block_coefficients (C:=C) (hg:=hg) (c:=c) atG
      (show k≤1 by linarith [hk.2]) hl.1 i
    have hpn : 0≤(blocks C hg atG k l c i).p := by rw [hd.1]; exact (hw i).1.le
    have hp := block_budgets hg atG k l c hvar ha hz i
    have hh := actual_block_minorant hy hP hq hpn hp.1 hp.2
    rw [hd.1,hd.2] at hh
    exact hh
  fin_cases i
  · simpa [Hybrid.block,actualBlocks] using hordinary 0 hHy (hc H)
  · simpa [Hybrid.block,actualBlocks] using hordinary 1
      (P:=(C.point G).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (by simpa using hc G)
  · simpa [Hybrid.block,actualBlocks] using hordinary 2
      (P:=(C.point B).reflect) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
      (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
    have hh := actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq hk hcoef (original_error_bound hvar hn D)
    simpa [Hybrid.block,actualBlocks,blocks,Block.P,Block.N,pWeights,qWeights] using hh

theorem original_concentration {q k l c : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : 0≤delta C.theta T) (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D 2) (hEH : C.Feasible E 0)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*tilted c (delta C.theta T) ∧ tilted c (delta C.theta T)≤2*l) :
    ∃i j : Fin 4,splitScalar k l c (total C atG) (aError C atG) i j≤0 := by
  have hb := original_budgets hg atG k l c hvar ha hz
  have hw := coefficient_domain hk hl hcoef hb.2.2.1 hratio
  obtain ⟨i,j,he⟩ := Hybrid.concentrate R (GlobalGA.Secondary.diagonal-1/2)
    (pWeights k l (tilted c (delta C.theta T)))
    (qWeights k l (tilted c (delta C.theta T)))
    (fun i => (blocks C hg atG k l c i).P)
    (fun i => (blocks C hg atG k l c i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hw i).1) (fun i => (hw i).2.1) (fun i => (hw i).2.2)
    (fun i => (blocks C hg atG k l c i).P_nonneg)
    (fun i => (blocks C hg atG k l c i).N_nonneg)
    hb.1 hb.2.2.2.1 hb.2.2.2.2
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_family_lower (hg:=hg) atG hs hc hq hHy hGy hBy hDy hvar ha hz
      hk hl hcoef hratio i)
  have hT := tReserve_nonneg (hs T) (hc T) hq
    (show 0≤c by linarith [hk.1,hcoef.1]) hb.2.2.1
  have hA := a_reserve_nonneg atG (hs A) (hc A) hq
    (show 0≤l by linarith [hk.1,hl.1]) ⟨ha,hb.2.1.2.trans hb.1.2⟩
  have hu := stress_nonpos atG (show 0≤k by linarith [hk.1])
    (show 0≤l by linarith [hk.1,hl.1]) (show 0<c by linarith [hk.1,hcoef.1])
    hb.2.2.1 hHG hGA hAB hBT hTD hDE hEH
  rw [decomposition C atG hhg k l c] at hu
  change TwoPositive.endpoint k l (tilted c (delta C.theta T)) (total C atG) i j≤_ at he
  refine ⟨i,j,?_⟩
  have hsplit : total C atG-aError C atG=delta C.theta T := by dsimp [total]; ring
  simp only [splitScalar,splitBase,hsplit]
  linarith

/-- Both original owner patterns of the two-positive theorem, including
their weak zero-error endpoints, with no scalar or frame-order premise. -/
theorem actual_false {q : ℝ} {C : SignedCycle} (atG : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : 0≤aError C atG) (hz : 0≤delta C.theta T)
    (hHG : C.Feasible H 0 ∨ C.Feasible H 2)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  have hb := original_budgets 0 atG 1 1 1 hvar ha hz
  obtain ⟨k,l,c,hk,hl,hcoef,hratio,hpositive⟩ := explicit_split_positive hb.1 hb.2.1
  have hsplit : total C atG-aError C atG=delta C.theta T := by dsimp [total]; ring
  rw [hsplit] at hratio
  have finish (hg : Fin 4) (hhg : hg=0 ∨ hg=2) (hHG : C.Feasible H hg) : False := by
    obtain ⟨i,j,hnecessary⟩ := original_concentration atG hs hc hq hHy hGy hBy hDy
      hvar ha hz hhg hHG hGA hAB hBT hTD hDE hEH hk hl hcoef hratio
    exact (not_lt_of_ge hnecessary) (hpositive i j)
  rcases hHG with hHG | hHG
  · exact finish 0 (Or.inl rfl) hHG
  · exact finish 2 (Or.inr rfl) hHG

end Source

open Source Candidate

/-- Original-radius form: the anchor signs and the full signed variation
are derived from the actual frame, and every supplied witness is weak. -/
theorem frame_one_positive_TD2_false {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (atG : Bool)
    (hGA : (forwardAxis (if atG then 3 else 2)).Feasible (C.square G) (C.square A))
    (hAB : (forwardAxis (if atG then 0 else 2)).Feasible (C.square A) (C.square B))
    (hBT : (forwardAxis 2).Feasible (C.square B) (C.square T))
    (hTD : (forwardAxis 2).Feasible (C.square T) (C.square D))
    (hDE : (forwardAxis 2).Feasible (C.square D) (C.square E))
    (hEH : (forwardAxis 0).Feasible (C.square E) (C.square H))
    (ha : 0≤Source.aError (SignedCycle.atFrame F) atG) (hz : 0≤delta F.theta T) : False := by
  have hn := SignedCycle.atFrame_necessary F
  have hanchors := GlobalOriginalOwners.atFrame_anchors F hq hE
  have hhigh : (if atG then (3:Fin 4) else 2)=2 ∨
      (if atG then (3:Fin 4) else 2)=3 := by cases atG <;> simp
  have hG := GlobalQuarterOuter.frame_high_anchor F hq G (by norm_num [word,G])
    (if atG then 3 else 2) hhigh (by simpa [G,A,next] using hGA)
  let j := SignedCycle.retainedOwner F H
  have hHGactual := (SignedCycle.atFrame_feasible F H j).1
    (SignedCycle.retainedOwner_feasible F H)
  have hHG : (SignedCycle.atFrame F).Feasible H 0 ∨ (SignedCycle.atFrame F).Feasible H 2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) j hHGactual with hh | hh
    · have h0 : SignedCycle.retainedOwner F H=0 := hh.1
      exact Or.inl (h0 ▸ SignedCycle.retainedOwner_feasible F H)
    · have h2 : SignedCycle.retainedOwner F H=2 := hh.1
      exact Or.inr (h2 ▸ SignedCycle.retainedOwner_feasible F H)
  apply Source.actual_false atG hn.sorted hn.contained hq.2
    hanchors.2.1.le ((SignedCycle.atFrame_y_neg_iff F G).2 hG.2).le
    hanchors.2.2.2.1.le hanchors.2.2.2.2.2.le
    (FramePhysicalTransport.candidate_variations F hq).1.le ha hz hHG
  · exact (SignedCycle.atFrame_feasible F G _).2 (by simpa [G,A,next] using hGA)
  · exact (SignedCycle.atFrame_feasible F A _).2 (by simpa [A,B,next] using hAB)
  · exact (SignedCycle.atFrame_feasible F B 2).2 (by simpa [B,T,next] using hBT)
  · exact (SignedCycle.atFrame_feasible F T 2).2 (by simpa [T,D,next] using hTD)
  · exact (SignedCycle.atFrame_feasible F D 2).2 (by simpa [D,E,next] using hDE)
  · exact (SignedCycle.atFrame_feasible F E 0).2 (by simpa [E,H,next] using hEH)

end SquaresInCircles.Eight.TableFree.GlobalGA.TwoPositive
