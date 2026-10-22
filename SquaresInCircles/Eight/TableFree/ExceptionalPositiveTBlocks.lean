module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTSupport
public import SquaresInCircles.Eight.TableFree.SoleOriginalBlocks

/-!
# Original ordinary blocks for arbitrary EH0 contact and positive T

Uncompiled source. The actual EH angle stays in H. The D block is
written with its sole ordinary coefficient first. This is the same
signed block with its two arguments exchanged, and changes no owner.
The common concentration theorem accepts the concrete angular endpoint
inequalities proved in the critical and outside-strip hand arguments.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTBlocks
open Candidate ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope
open SingleAngleConcavity ExceptionalPositiveTStress

structure Weights where
  n : ℝ
  k : ℝ
  ell : ℝ
  b : ℝ
  d : ℝ
  p : ℝ

def first (w : Weights) : Fin 4 → ℝ := ![w.p,w.k,w.ell,1]
def second (w : Weights) : Fin 4 → ℝ := ![w.n,w.ell,w.b,w.d]
def small (w : Weights) (i : Fin 4) : ℝ := min (first w i) (second w i)
def large (w : Weights) (i : Fin 4) : ℝ := max (first w i) (second w i)
def single (td : Bool) : Fin 4 → Bool := ![false,true,!td,true]
def negative (w : Weights) (td : Bool) : Fin 4 → ℝ :=
  ![max w.p w.n,w.ell,if td then max w.ell w.b else w.ell,w.d]
def rawBlocks (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) : Fin 4 → Block :=
  SoleEStress.blocks C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d 1 w.p
def swap (B : Block) : Block := ⟨B.beta,B.alpha,B.v,B.u⟩
def blocks (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (i : Fin 4) : Block :=
  if i=3 then swap (rawBlocks C ab td w i) else rawBlocks C ab td w i
def increment (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (R : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d 1 w.p R

theorem small_le_large (w : Weights) (i : Fin 4) : small w i≤large w i := min_le_max
theorem negative_between (w : Weights) (td : Bool) (i : Fin 4) :
    small w i≤negative w td i ∧ negative w td i≤large w i := by
  fin_cases i <;> cases td <;>
    simp [small,large,negative,first,second,min_le_left,min_le_right,le_max_left,le_max_right]
theorem mixed_negative (w : Weights) (td : Bool) (i : Fin 4) (hi : single td i=false) :
    negative w td i=large w i := by
  fin_cases i <;> cases td <;> simp_all [single,negative,large,first,second]
theorem pure_eq (w : Weights) (td : Bool) (R u : ℝ) (i : Fin 4) :
    pure (single td i) R (small w i) (large w i) (negative w td i) u=
      Vnu R (small w i) (large w i) (negative w td i) u := by
  cases hi : single td i
  · rw [mixed_negative w td i hi]
    rfl
  · rfl
theorem norm_eq (w : Weights) (u : ℝ) (i : Fin 4) :
    pairNorm (small w i) (large w i) u=pairNorm (first w i) (second w i) u := by
  rcases le_total (first w i) (second w i) with h | h
  · simp [small,large,min_eq_left h,max_eq_right h]
  · simp [small,large,min_eq_right h,max_eq_left h,pairNorm_symm]
theorem swap_data (B : Block) (R : ℝ) :
    (swap B).p=B.p ∧ (swap B).q=B.q ∧ (swap B).P=B.P ∧
    (swap B).N=B.N ∧ (swap B).increment R=B.increment R := by
  simp [swap,Block.p,Block.q,Block.P,Block.N,Block.increment,min_comm,max_comm,
    pairNorm_symm,add_comm,add_left_comm,add_assoc]
theorem coefficients (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (i : Fin 4) :
    (blocks C ab td w i).p=small w i ∧ (blocks C ab td w i).q=large w i := by
  fin_cases i <;> simp [blocks,rawBlocks,swap,SoleEStress.blocks,Block.p,Block.q,
    small,large,first,second,min_comm,max_comm]
theorem single_data (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights)
    (i : Fin 4) (hi : single td i=true) :
    (blocks C ab td w i).v=0 ∧ (blocks C ab td w i).alpha=negative w td i := by
  fin_cases i <;> cases td <;>
    simp_all [single,blocks,rawBlocks,swap,SoleEStress.blocks,negative,
      btOwner,tdOwner,ordinaryDE,ordinaryEH]
theorem parts (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (i : Fin 4) :
    (blocks C ab td w i).P=
      (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d i).P ∧
    (blocks C ab td w i).N=
      (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d i).N := by
  fin_cases i <;> simp [blocks,rawBlocks,swap,SoleEStress.blocks,ActualCoreEBlocks.blocks,
    Block.P,Block.N,add_comm]
theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (w : Weights) {t : ℝ} (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (htotal : delta C.theta G+delta C.theta D+primary C td=t) :
    t∈Icc 0 frameCap ∧ (∑i,(blocks C ab td w i).P)≤frameCap-t ∧
      (∑i,(blocks C ab td w i).N)=t+∑i,(blocks C ab td w i).P := by
  have hBT : btOwner td=3 → 0≤delta C.theta B := by cases td <;> simp_all [btOwner,primary]
  have hTD : tdOwner td=2 → 0≤delta C.theta T := by cases td <;> simp_all [tdOwner,primary]
  have hremoved : removed C (btOwner td) (tdOwner td)=delta C.theta G+primary C td := by
    cases td <;> simp [removed,btOwner,tdOwner,primary]
  have hEtotal : eTotal C 3 0=delta C.theta D := by simp [eTotal,primaryDE,primaryEH]
  have hh := ActualCoreEBlocks.block_budgets hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) w.n w.k w.ell w.b w.d hvar hG hBT hTD
    (by simpa only [hEtotal] using hD)
  have hP := Finset.sum_congr rfl (fun i _ => (parts C ab td w i).1)
  have hN := Finset.sum_congr rfl (fun i _ => (parts C ab td w i).2)
  rw [hEtotal,hremoved] at hh
  refine ⟨⟨by linarith,by linarith [hh.2.1.2]⟩,?_,?_⟩
  · rw [hP]
    linarith [hh.2.2.1]
  · rw [hN,hP]
    linarith [hh.2.2.2]
theorem single_parts (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights)
    (i : Fin 4) (hi : single td i=true) :
    (blocks C ab td w i).P=0 ∨ (blocks C ab td w i).N=0 := by
  have hv := (single_data C ab td w i hi).1
  by_cases hu : 0≤(blocks C ab td w i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab td w i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]
theorem angles_small {C : SignedCycle} (ab : Fin 4) (td : Bool) (w : Weights)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab td w i).u|≤frameCap ∧ |(blocks C ab td w i).v|≤frameCap := by
  have hzero : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  fin_cases i <;> cases td <;>
    simp [blocks,rawBlocks,swap,SoleEStress.blocks,btOwner,tdOwner,ordinaryDE,ordinaryEH] <;>
    split_ifs <;> constructor <;>
    first | exact hzero | exact ha H | exact ha A | exact ha B | exact ha T | exact ha E
theorem block_minorant {C : SignedCycle} {ab : Fin 4} {td : Bool} {w : Weights} {R t : ℝ}
    (ht : 0≤t) (hp : ∀ i,0<small w i) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab td w i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab td w i).N)=t+∑i,(blocks C ab td w i).P) (i : Fin 4) :
    F (single td i) R (small w i) (large w i) (negative w td i)
      (blocks C ab td w i).P (blocks C ab td w i).N≤(blocks C ab td w i).increment R := by
  obtain ⟨hpi,hqi⟩ := coefficients C ab td w i
  have hPi := Finset.single_le_sum (fun j _ => (blocks C ab td w j).P_nonneg) (Finset.mem_univ i)
  have hNi := Finset.single_le_sum (fun j _ => (blocks C ab td w j).N_nonneg) (Finset.mem_univ i)
  cases hi : single td i
  · have hh := (blocks C ab td w i).minorant R
      (by rw [hpi]; exact (hp i).le) (by linarith) (by linarith)
    rw [mixed_negative w td i hi]
    simpa only [F,hi,if_false,hpi,hqi] using hh
  · obtain ⟨hv,hnu⟩ := single_data C ab td w i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab td w i) R hv
      (angles_small ab td w ha i).1
    simpa only [hi,hpi,hqi,hnu] using hh
theorem increment_eq {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (w : Weights) (R : ℝ) :
    increment C ab td w R=∑i,(blocks C ab td w i).increment R := by
  rw [increment,SoleEStress.increment_eq C hab (bt_cases td) (td_cases td)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [blocks]
  split_ifs
  · exact (swap_data (rawBlocks C ab td w i) R).2.2.2.2.symm
  · rfl

theorem original_lower {C : SignedCycle} {ab : Fin 4} (td : Bool) (w : Weights)
    {R t L : ℝ} (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQU : R^2≤qCap)
    (hp : ∀ i,0<small w i) (hhalf : ∀ i,large w i≤2*small w i)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (htotal : delta C.theta G+delta C.theta D+primary C td=t)
    (hpure : ∀ i,L≤pure (single td i) R (small w i) (large w i) (negative w td i) t)
    (hsame : ∀ i,single td i=false → L≤OrdinaryAngleConcentration.M R (small w i) (large w i) t)
    (hseparated : ∀ i j,i≠j → L≤OrdinaryAngleConcavity.U R (small w i) (large w i) (frameCap-t)+
      pure (single td j) R (small w j) (large w j) (negative w td j) frameCap) :
    L≤increment C ab td w R := by
  obtain ⟨ht,hP,hN⟩ := original_budgets hab td w hvar hG hD hT htotal
  have henvelope := SingleAngleConcentration.lower_from_endpoints (single td) R
    (small w) (large w) (negative w td)
    (fun i => (blocks C ab td w i).P) (fun i => (blocks C ab td w i).N)
    hR hQU hp (small_le_large w) hhalf (fun i => (negative_between w td i).1)
    (fun i => (blocks C ab td w i).P_nonneg) (fun i => (blocks C ab td w i).N_nonneg)
    ht hP hN (single_parts C ab td w) hpure hsame hseparated
  have hminor := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_minorant ht.1 hp ha hP hN i)
  rw [increment_eq hab td w R]
  exact henvelope.trans hminor

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTBlocks
