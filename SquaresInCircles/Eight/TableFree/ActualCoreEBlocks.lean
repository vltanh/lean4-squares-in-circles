module

public import SquaresInCircles.Eight.TableFree.CoreECharge
public import SquaresInCircles.Eight.TableFree.ActualOrdinaryBlocks

/-!
# Original ordinary blocks with either actual E owner

Uncompiled source draft. A primary E error is removed from its incident
ordinary block and retained in the exact E charge. The original signed
angles are never changed. In particular opposite signs on the two E
primaries are permitted: dropping their common extra variation gives the
closed budget used in the angular estimate.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ActualCoreEBlocks
open Candidate PositiveAngularEnvelope ActualOrdinaryBlocks

def primaryDE (C : SignedCycle) (de : Fin 4) : ℝ :=
  if de=3 then delta C.theta D else 0
def primaryEH (C : SignedCycle) (eh : Fin 4) : ℝ :=
  if eh=1 then delta C.theta E else 0
def ordinaryDE (C : SignedCycle) (de : Fin 4) : ℝ :=
  if de=2 then delta C.theta D else 0
def ordinaryEH (C : SignedCycle) (eh : Fin 4) : ℝ :=
  if eh=0 then delta C.theta E else 0
def eTotal (C : SignedCycle) (de eh : Fin 4) : ℝ :=
  primaryDE C de+primaryEH C eh

def blocks (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) : Fin 4 → Block :=
  ![⟨n,1,delta C.theta H,ordinaryEH C eh⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,b,if ab=0 then delta C.theta A else 0,if bt=2 then delta C.theta B else 0⟩,
    ⟨1,t,ordinaryDE C de,if td=0 then delta C.theta T else 0⟩]

def charge (C : SignedCycle) (de eh : Fin 4) : ℝ :=
  CoreECharge.pairDeficit (C.point E).a (-(C.point E).y)
    (primaryDE C de) (primaryEH C eh)

theorem block_coefficients (C : SignedCycle) (ab bt td de eh : Fin 4)
    (n k l b t : ℝ) (i : Fin 4) :
    (blocks C ab bt td de eh n k l b t i).p=
        (ActualOrdinaryBlocks.blocks C ab bt td n k l b t i).p ∧
      (blocks C ab bt td de eh n k l b t i).q=
        (ActualOrdinaryBlocks.blocks C ab bt td n k l b t i).q := by
  fin_cases i <;> simp [blocks,ActualOrdinaryBlocks.blocks,Block.p,Block.q]

theorem primary_small {C : SignedCycle} {de eh : Fin 4}
    (hs : ∀ i,|delta C.theta i|≤frameCap) :
    |primaryDE C de|≤frameCap ∧ |primaryEH C eh|≤frameCap := by
  constructor
  · by_cases hd : de=3
    · simpa [primaryDE,hd] using hs D
    · simp [primaryDE,hd,frameCap]; norm_num
  · by_cases he : eh=1
    · simpa [primaryEH,he] using hs E
    · simp [primaryEH,he,frameCap]; norm_num

theorem ordinary_small {C : SignedCycle} {de eh : Fin 4}
    (hs : ∀ i,|delta C.theta i|≤frameCap) :
    |ordinaryDE C de|≤frameCap ∧ |ordinaryEH C eh|≤frameCap := by
  constructor
  · by_cases hd : de=2
    · simpa [ordinaryDE,hd] using hs D
    · simp [ordinaryDE,hd,frameCap]; norm_num
  · by_cases he : eh=0
    · simpa [ordinaryEH,he] using hs E
    · simp [ordinaryEH,he,frameCap]; norm_num

theorem charge_lower {C : SignedCycle} {q : ℝ} {de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (he : eTotal C de eh∈Icc 0 frameCap) :
    PositiveScalarTransfer.J (eTotal C de eh)≤charge C de eh := by
  have hs := primary_small (C := C) (de := de) (eh := eh)
    (fun i => hC.spread (next i) i)
  exact CoreECharge.actual_core_pair_signed (hC.sorted E) hcore hs.1 hs.2 he

theorem sum_parts (C : SignedCycle) {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (f : ℝ → ℝ) (hf0 : f 0=0) :
    (∑ i,(f (blocks C ab bt td de eh n k l b t i).u+
      f (blocks C ab bt td de eh n k l b t i).v))=
      (∑ j,f (delta C.theta j))-f (delta C.theta G)-
        (if bt=3 then f (delta C.theta B) else 0)-
        (if td=2 then f (delta C.theta T) else 0)-
        f (primaryDE C de)-f (primaryEH C eh) := by
  rcases hab with rfl | rfl <;> rcases hbt with rfl | rfl <;>
    rcases htd with rfl | rfl <;> rcases hde with rfl | rfl <;>
    rcases heh with rfl | rfl <;>
    simp [blocks,ordinaryDE,ordinaryEH,primaryDE,primaryEH,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf0] <;> ring

/-- The sign of the sum is sufficient. The two individual E-primary
errors may have opposite signs, and their discarded extra variation
only enlarges the analytic domain. -/
theorem block_budgets {C : SignedCycle} {ab bt td de eh : Fin 4}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (n k l b t : ℝ) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G)
    (hBT : bt=3 → 0≤delta C.theta B) (hTD : td=2 → 0≤delta C.theta T)
    (he : 0≤eTotal C de eh) :
    removed C bt td∈Icc 0 frameCap ∧
      eTotal C de eh∈Icc 0 (frameCap-removed C bt td) ∧
      (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤
        frameCap-removed C bt td-eTotal C de eh ∧
      (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
        removed C bt td+eTotal C de eh+
          ∑ i,(blocks C ab bt td de eh n k l b t i).P := by
  let Bs := blocks C ab bt td de eh n k l b t
  have hp := sum_parts C hab hbt htd hde heh n k l b t
    positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd hde heh n k l b t
    negativePart negativePart_zero
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith : -delta C.theta G≤0)
  have hPB : (if bt=3 then positivePart (delta C.theta B) else 0)=
      (if bt=3 then delta C.theta B else 0) := by
    by_cases hb : bt=3
    · simp [hb,positivePart,max_eq_left (hBT hb)]
    · simp [hb]
  have hPT : (if td=2 then positivePart (delta C.theta T) else 0)=
      (if td=2 then delta C.theta T else 0) := by
    by_cases ht : td=2
    · simp [ht,positivePart,max_eq_left (hTD ht)]
    · simp [ht]
  have hNB : (if bt=3 then negativePart (delta C.theta B) else 0)=0 := by
    by_cases hb : bt=3
    · simp [hb,negativePart,max_eq_right (by linarith [hBT hb] : -delta C.theta B≤0)]
    · simp [hb]
  have hNT : (if td=2 then negativePart (delta C.theta T) else 0)=0 := by
    by_cases ht : td=2
    · simp [ht,negativePart,max_eq_right (by linarith [hTD ht] : -delta C.theta T≤0)]
    · simp [ht]
  have hd : 0≤removed C bt td := by
    have hb : 0≤(if bt=3 then delta C.theta B else 0) := by
      split_ifs with h
      · exact hBT h
      · rfl
    have ht : 0≤(if td=2 then delta C.theta T else 0) := by
      split_ifs with h
      · exact hTD h
      · rfl
    dsimp [removed]
    linarith
  have hp' : (∑ i,(Bs i).P)=positiveVariation C.theta-removed C bt td-
      positivePart (primaryDE C de)-positivePart (primaryEH C eh) := by
    change (∑ i,(positivePart (Bs i).u+positivePart (Bs i).v))=_
    rw [hp,hPG,hPB,hPT]
    dsimp [positiveVariation,removed]
    ring
  have hn' : (∑ i,(Bs i).N)=negativeVariation C.theta-
      negativePart (primaryDE C de)-negativePart (primaryEH C eh) := by
    change (∑ i,(negativePart (Bs i).u+negativePart (Bs i).v))=_
    rw [hn,hNG,hNB,hNT]
    simp [negativeVariation]
  have hde := positive_sub_negative (primaryDE C de)
  have heh := positive_sub_negative (primaryEH C eh)
  have hnd := negativePart_nonneg (primaryDE C de)
  have hnh := negativePart_nonneg (primaryEH C eh)
  have htotal := variations_equal C.theta
  have hP0 : 0≤∑ i,(Bs i).P := Finset.sum_nonneg fun i _ => (Bs i).P_nonneg
  have hbound : (∑ i,(Bs i).P)≤frameCap-removed C bt td-eTotal C de eh := by
    dsimp [eTotal]
    linarith
  refine ⟨⟨hd,by linarith⟩,⟨he,by linarith⟩,hbound,?_⟩
  dsimp [eTotal]
  linarith

end SquaresInCircles.Eight.TableFree.ActualCoreEBlocks
