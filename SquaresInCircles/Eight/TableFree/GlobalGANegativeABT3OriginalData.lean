module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Low
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Stress

/-!
# The unchanged secondary-E reference cycle for negative A and BT3

Uncompiled Sections 2--5. The A secant multiplier and the rotating
TD0 multiplier have different arguments. Deleting the negative A
primary and the positive BT3 error leaves both exact signed budgets.
The arbitrary TD0 error remains in the two-angle D block.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

abbrev aError := NegativeAPositiveTD.Source.aError

def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,3,0,2,0]

def weights (atG : Bool) (k l m s z : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG l s,lambdaB atG l s,m,PositiveBT3.tilted m z,1,1]

def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l m s : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,lambdaG atG l s,if hg=0 then delta C.theta H else 0,
      if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG l s,m,if atG then delta C.theta A else 0,0⟩,
    ⟨PositiveBT3.tilted m (delta C.theta B),1,delta C.theta T,delta C.theta D⟩]

theorem weights_nonnegative (atG : Bool) {k l m s z : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hm : 0<m)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (i : Vertex) :
    0≤weights atG k l m s z i := by
  have hp := NegativeAPositiveTD.Source.secant_nonnegative hl hs
  have hc := (PositiveTD.tilted_pos hm hz).le
  cases atG <;> fin_cases i <;>
    simp [weights,lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,
      PositiveBT3.tilted] <;> positivity

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} {atG : Bool} {k l m s : ℝ}
    (f : Certificate.Family) (hk : k≤1) (hG : k≤lambdaG atG l s)
    (i : Fin 4) (hi : f=.high∨i≠3) :
    (blocks C hg atG k l m s i).p=pWeights f atG k l m
      (PositiveBT3.tilted m (delta C.theta B)) s i ∧
    (blocks C hg atG k l m s i).q=qWeights f atG k l m
      (PositiveBT3.tilted m (delta C.theta B)) s i := by
  cases f <;> fin_cases i <;>
    simp_all [blocks,Block.p,Block.q,pWeights,qWeights,
      min_eq_left hk,max_eq_right hk,min_eq_left hG,max_eq_right hG,min_comm,max_comm]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l m s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,f (blocks C hg atG k l m s i).u+f (blocks C hg atG k l m s i).v)=
      (∑j,f (delta C.theta j))-f (delta C.theta B)-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,NegativeAPositiveTD.Source.aError,hhg,
      Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l m : ℝ) {s : ℝ}
    (hs : 0≤s) (ha : aError C atG= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) :
    delta C.theta B∈Icc 0 frameCap ∧
    (∑i,(blocks C hg atG k l m s i).P)=positiveVariation C.theta-delta C.theta B ∧
    (∑i,(blocks C hg atG k l m s i).N)=negativeVariation C.theta-s ∧
    (∑i,(blocks C hg atG k l m s i).P)≤frameCap-delta C.theta B ∧
    (∑i,(blocks C hg atG k l m s i).N)≤frameCap-s ∧
    (∑i,(blocks C hg atG k l m s i).N)-
      (∑i,(blocks C hg atG k l m s i).P)=delta C.theta B-s := by
  have hp := sum_parts C hg atG k l m s positivePart positivePart_zero
  have hn := sum_parts C hg atG k l m s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hnz : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by
    rw [ha]
    exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=s := by
    rw [ha]
    simpa [negativePart] using max_eq_left hs
  have hp' : (∑i,(blocks C hg atG k l m s i).P)=
      positiveVariation C.theta-delta C.theta B := by
    simpa only [Block.P,hpz,hpa,positiveVariation,sub_zero] using hp
  have hn' : (∑i,(blocks C hg atG k l m s i).N)=negativeVariation C.theta-s := by
    simpa only [Block.N,hnz,hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l m s i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨hz,by linarith⟩,hp',hn',by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l m : ℝ) {s : ℝ}
    (hs : 0≤s) (ha : aError C atG= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) (i : Fin 4) :
    (blocks C hg atG k l m s i).P≤frameCap ∧ (blocks C hg atG k l m s i).N≤frameCap := by
  have hb := original_budgets hg atG k l m hs ha hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l m s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l m s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.2.2.2.1],by linarith [hb.2.2.2.2.1]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Source
