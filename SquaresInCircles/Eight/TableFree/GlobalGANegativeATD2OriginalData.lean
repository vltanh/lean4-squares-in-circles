module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Endpoints
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveTDStress

/-!
# Removing the actual negative-A and nonnegative-TD2 errors

Uncompiled transcription of Sections 2--3 of the whole-angle companion.
The original secant weights and all remaining signed errors are retained.
The two fixed errors are deleted only from the algebraic block vector;
the resulting positive and negative totals keep their exact balance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks

def aError (C : SignedCycle) (atG : Bool) : ℝ :=
  if atG then delta C.theta G else delta C.theta A
def owners (hg : Fin 4) (atG : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,2,0]
def weights (atG : Bool) (k l c s z : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG l s,lambdaB atG l s,PositiveTD.tilted c z,c,1,1]
def pWeights (atG : Bool) (k l m s : ℝ) : Fin 4→ℝ :=
  ![k,k,min (lambdaB atG l s) m,k]
def qWeights (atG : Bool) (k l m s : ℝ) : Fin 4→ℝ :=
  ![1,lambdaG atG l s,max (lambdaB atG l s) m,1]
def blocks (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ) : Fin 4→Block :=
  ![⟨k,1,if hg=0 then 0 else delta C.theta H,delta C.theta E⟩,
    ⟨k,lambdaG atG l s,if hg=0 then delta C.theta H else 0,
      if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG l s,PositiveTD.tilted c (delta C.theta T),
      if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨k,1,delta C.theta D,0⟩]

theorem secant_nonnegative {l s : ℝ} (hl : 0≤l) (hs : s∈Icc 0 frameCap) :
    0≤ secant l s := div_nonneg hl (by linarith [(transport_trig hs).1])

theorem weights_nonnegative (atG : Bool) {k l c s z : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (i : Vertex) :
    0≤weights atG k l c s z i := by
  have hp := secant_nonnegative hl hs
  have hm := (PositiveTD.tilted_pos hc hz).le
  cases atG <;> fin_cases i <;> simp [weights,lambdaG,lambdaB] <;> positivity

theorem coefficient_domain {atG : Bool} {k l m s : ℝ}
    (hk : k∈Icc (1/2:ℝ) (17/20:ℝ))
    (hG : lambdaG atG l s∈Icc k (2*k))
    (hB : 0<lambdaB atG l s) (hm : 0< m)
    (hratio : lambdaB atG l s≤2*m ∧ m≤2*lambdaB atG l s) (i : Fin 4) :
    0<pWeights atG k l m s i ∧ pWeights atG k l m s i≤qWeights atG k l m s i ∧
      qWeights atG k l m s i≤2*pWeights atG k l m s i := by
  have hk0 : 0<k := by linarith [hk.1]
  have h0 : 0<pWeights atG k l m s 0 ∧ pWeights atG k l m s 0≤qWeights atG k l m s 0 ∧
      qWeights atG k l m s 0≤2*pWeights atG k l m s 0 := by
    simp only [pWeights,qWeights,Matrix.cons_val_zero]
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1]⟩
  have h1 : 0<pWeights atG k l m s 1 ∧ pWeights atG k l m s 1≤qWeights atG k l m s 1 ∧
      qWeights atG k l m s 1≤2*pWeights atG k l m s 1 := by
    simp only [pWeights,qWeights,Matrix.cons_val_one]
    exact ⟨hk0,hG.1,hG.2⟩
  have h2 : 0<pWeights atG k l m s 2 ∧ pWeights atG k l m s 2≤qWeights atG k l m s 2 ∧
      qWeights atG k l m s 2≤2*pWeights atG k l m s 2 := by
    change 0< min (lambdaB atG l s) m ∧
      min (lambdaB atG l s) m ≤ max (lambdaB atG l s) m ∧
      max (lambdaB atG l s) m ≤ 2*min (lambdaB atG l s) m
    refine ⟨lt_min hB hm,min_le_max,?_⟩
    rcases le_total (lambdaB atG l s) m with hh | hh
    · rw [min_eq_left hh,max_eq_right hh]; exact hratio.2
    · rw [min_eq_right hh,max_eq_left hh]; exact hratio.1
  have h3 : 0<pWeights atG k l m s 3 ∧ pWeights atG k l m s 3≤qWeights atG k l m s 3 ∧
      qWeights atG k l m s 3≤2*pWeights atG k l m s 3 := by
    change 0<k ∧ k≤1 ∧ 1≤2*k
    exact ⟨hk0,by linarith [hk.2],by linarith [hk.1]⟩
  fin_cases i
  exacts [h0,h1,h2,h3]

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} {atG : Bool} {k l c s : ℝ}
    (hk : k≤1) (hG : k≤lambdaG atG l s) (i : Fin 4) :
    (blocks C hg atG k l c s i).p=pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s i ∧
    (blocks C hg atG k l c s i).q=qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s i := by
  fin_cases i <;>
    simp [blocks,Block.p,Block.q,pWeights,qWeights,min_eq_left hk,max_eq_right hk,
      min_eq_left hG,max_eq_right hG]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG : Bool) (k l c s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑ i,(f (blocks C hg atG k l c s i).u+f (blocks C hg atG k l c s i).v))=
      (∑ j,f (delta C.theta j))-f (delta C.theta T)-f (aError C atG) := by
  cases atG <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

theorem original_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ) {s : ℝ}
    (hs : 0≤ s) (ha : aError C atG=-s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) :
    delta C.theta T∈Icc 0 frameCap ∧
    (∑ i,(blocks C hg atG k l c s i).P)=positiveVariation C.theta-delta C.theta T ∧
    (∑ i,(blocks C hg atG k l c s i).N)=negativeVariation C.theta-s ∧
    (∑ i,(blocks C hg atG k l c s i).P)≤frameCap-delta C.theta T ∧
    (∑ i,(blocks C hg atG k l c s i).N)≤frameCap-s ∧
    (∑ i,(blocks C hg atG k l c s i).N)-
      (∑ i,(blocks C hg atG k l c s i).P)=delta C.theta T-s := by
  have hp := sum_parts C hg atG k l c s positivePart positivePart_zero
  have hn := sum_parts C hg atG k l c s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by
    rw [ha]
    exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=s := by
    rw [ha]
    simpa [negativePart] using max_eq_left hs
  have hp' : (∑ i,(blocks C hg atG k l c s i).P)=
      positiveVariation C.theta-delta C.theta T := by
    change (∑ i,(positivePart (blocks C hg atG k l c s i).u+
      positivePart (blocks C hg atG k l c s i).v))=_
    simpa only [hpz,hpa,positiveVariation,sub_zero] using hp
  have hn' : (∑ i,(blocks C hg atG k l c s i).N)=negativeVariation C.theta-s := by
    change (∑ i,(negativePart (blocks C hg atG k l c s i).u+
      negativePart (blocks C hg atG k l c s i).v))=_
    simpa only [hnz,hna,negativeVariation,sub_zero] using hn
  have hp0 := Finset.sum_nonneg (s:=Finset.univ)
    (fun i _ => (blocks C hg atG k l c s i).P_nonneg)
  have heq := variations_equal C.theta
  exact ⟨⟨hz,by linarith⟩,hp',hn',by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} (hg : Fin 4) (atG : Bool) (k l c : ℝ) {s : ℝ}
    (hs : 0≤ s) (ha : aError C atG=-s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) (i : Fin 4) :
    (blocks C hg atG k l c s i).P≤frameCap ∧ (blocks C hg atG k l c s i).N≤frameCap := by
  have hb := original_budgets hg atG k l c hs ha hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG k l c s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.2.2.2.1],by linarith [hb.2.2.2.2.1]⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
