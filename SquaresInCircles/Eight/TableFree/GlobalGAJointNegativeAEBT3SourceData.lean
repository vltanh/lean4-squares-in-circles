module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3Chords
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Stress

/-!
# Original joint-negative BT3/TD0 blocks and signed budgets

Uncompiled transcription of Sections 2--4 of the geometric assembly.
The TD0 error remains an independent signed argument at D. When the
actual D block is ordinary, the fifth zero block is the distinguished
separated block for the uniform concentration theorem. Otherwise D
itself is distinguished. Both choices retain the actual signed sums.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

abbrev sec := SecantNormCurvature.secant
abbrev aError := JointNegativeAETD2.Source.aError
abbrev eError := JointNegativeAETD2.Source.eError
abbrev lambdaG := JointNegativeAETD2.Source.lambdaG
abbrev lambdaB := JointNegativeAETD2.Source.lambdaB
abbrev lambdaH := JointNegativeAETD2.Source.lambdaH
abbrev lambdaD := JointNegativeAETD2.Source.lambdaD
def ordinaryD (atH : Bool) (c : ℝ) : Prop := atH=true ∧ c<1
instance (atH : Bool) (c : ℝ) : Decidable (ordinaryD atH c) := by
  unfold ordinaryD; infer_instance
def distinguished (atH : Bool) (c : ℝ) : Fin 5 := if ordinaryD atH c then 4 else 3
def owners (hg : Fin 4) (atG atH : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,3,0,if atH then 2 else 3,if atH then 1 else 0]
def weights (atG atH : Bool) (k m c r s : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG r,lambdaB atG r,m,c,lambdaD atH s,lambdaH atH s]
def pWeights (atG atH : Bool) (k m c r s : ℝ) : Fin 5→ℝ :=
  ![k,k,min (lambdaB atG r) m,if ordinaryD atH c then c else k,k]
def qWeights (atG atH : Bool) (k m c r s : ℝ) : Fin 5→ℝ :=
  ![lambdaH atH s,lambdaG atG r,max (lambdaB atG r) m,1,1]
def blocks (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k m c r s : ℝ) : Fin 5→Block :=
  ![⟨k,lambdaH atH s,if hg=0 then 0 else delta C.theta H,if atH then 0 else delta C.theta E⟩,
    ⟨k,lambdaG atG r,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG r,m,if atG then delta C.theta A else 0,0⟩,
    ⟨c,lambdaD atH s,delta C.theta T,if atH then delta C.theta D else 0⟩,
    ⟨k,1,0,0⟩]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k m c r s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,(f (blocks C hg atG atH k m c r s i).u+f (blocks C hg atG atH k m c r s i).v))=
      (∑v,f (delta C.theta v))-f (delta C.theta B)-f (aError C atG)-f (eError C atH) := by
  cases atG <;> cases atH <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,eError,JointNegativeAETD2.Source.aError,JointNegativeAETD2.Source.eError,
      hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budget (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k m c r s : ℝ) : Prop where
  total_domain : r+s∈Icc 0 frameCap
  bt_domain : delta C.theta B∈Icc 0 frameCap
  positive_eq : (∑i,(blocks C hg atG atH k m c r s i).P)=positiveVariation C.theta-delta C.theta B
  negative_eq : (∑i,(blocks C hg atG atH k m c r s i).N)=negativeVariation C.theta-r-s
  positive_bound : (∑i,(blocks C hg atG atH k m c r s i).P)≤frameCap-delta C.theta B
  negative_bound : (∑i,(blocks C hg atG atH k m c r s i).N)≤frameCap-(r+s)
  balance : (∑i,(blocks C hg atG atH k m c r s i).N)-
    (∑i,(blocks C hg atG atH k m c r s i).P)=delta C.theta B-(r+s)

theorem budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k m c : ℝ)
    (hr : 0≤r) (hs : 0≤ s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) :
    Budget C hg atG atH k m c r s := by
  have hp := sum_parts C hg atG atH k m c r s positivePart positivePart_zero
  have hn := sum_parts C hg atG atH k m c r s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta B)=delta C.theta B := max_eq_left hz
  have hnz : negativePart (delta C.theta B)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by rw [ha]; exact max_eq_right (by linarith)
  have hpe : positivePart (eError C atH)=0 := by rw [he]; exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=r := by rw [ha]; simpa [negativePart] using max_eq_left hr
  have hne : negativePart (eError C atH)=s := by rw [he]; simpa [negativePart] using max_eq_left hs
  have hP : (∑i,(blocks C hg atG atH k m c r s i).P)=positiveVariation C.theta-delta C.theta B := by
    simpa only [Block.P,positiveVariation,hpz,hpa,hpe,sub_zero] using hp
  have hN : (∑i,(blocks C hg atG atH k m c r s i).N)=negativeVariation C.theta-r-s := by
    simpa only [Block.N,negativeVariation,hnz,hna,hne,sub_zero] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => (blocks C hg atG atH k m c r s i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => (blocks C hg atG atH k m c r s i).N_nonneg)
  have hvariation := variations_equal C.theta
  exact ⟨⟨add_nonneg hr hs,by linarith⟩,⟨hz,by linarith⟩,hP,hN,
    by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k m c : ℝ)
    (hr : 0≤r) (hs : 0≤ s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta B) (i : Fin 5) :
    (blocks C hg atG atH k m c r s i).P≤frameCap ∧ (blocks C hg atG atH k m c r s i).N≤frameCap := by
  have hb := budgets hg atG atH k m c hr hs ha he hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG atH k m c r s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _ => (blocks C hg atG atH k m c r s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound],by linarith [hb.negative_bound]⟩

theorem pair_domain (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (i : Fin 5) :
    0<pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i ∧
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
        qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i ∧
      qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i≤
        (17/10)*pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s i := by
  have hc := Explicit.ranges f hz
  have hl := JointNegativeAETD2.Source.lambda_bounds atG atH hr hs hH
  have hk : 0<Explicit.k f z := by linarith [hc.k_domain.1]
  have hm : 0<Explicit.m f z := hk.trans_le hc.k_le_m
  have hmhi : Explicit.m f z≤7/5 := hc.m_le_c.trans hc.c_domain.2
  fin_cases i
  · simp only [pWeights,qWeights,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue,Matrix.cons_val]
    exact ⟨hk,by linarith [hc.k_domain.2,hl.2.2.1.1],by linarith [hc.k_domain.1,hl.2.2.1.2]⟩
  · simp only [pWeights,qWeights,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue,Matrix.cons_val]
    exact ⟨hk,by linarith [hc.k_domain.2,hl.1.1],by linarith [hc.k_domain.1,hl.1.2]⟩
  · change 0 < min (lambdaB atG r) (Explicit.m f z) ∧
      min (lambdaB atG r) (Explicit.m f z) ≤ max (lambdaB atG r) (Explicit.m f z) ∧
      max (lambdaB atG r) (Explicit.m f z) ≤ (17/10)*min (lambdaB atG r) (Explicit.m f z)
    refine ⟨lt_min (by linarith [hl.2.1.1]) hm,min_le_max,?_⟩
    rcases le_total (lambdaB atG r) (Explicit.m f z) with h|h
    · rw [min_eq_left h,max_eq_right h]
      linarith [hl.2.1.1]
    · rw [min_eq_right h,max_eq_left h]
      linarith [hl.2.1.2,hc.k_domain.1,hc.k_le_m]
  · by_cases ho : ordinaryD atH (Explicit.c f z)
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue,Matrix.cons_val,ho,↓reduceIte]
      exact ⟨by linarith [hc.c_domain.1],ho.2.le,by linarith [hc.c_domain.1]⟩
    · simp only [pWeights,qWeights,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue,Matrix.cons_val,ho,↓reduceIte]
      exact ⟨hk,by linarith [hc.k_domain.2],by linarith [hc.k_domain.1]⟩
  · simp only [pWeights,qWeights,Fin.reduceFinMk,Fin.zero_eta,Fin.mk_one,Fin.isValue,Matrix.cons_val]
    exact ⟨hk,by linarith [hc.k_domain.2],by linarith [hc.k_domain.1]⟩

theorem ordinary_coefficients {C : SignedCycle} {hg : Fin 4} (atG atH : Bool)
    {k m c r s : ℝ} (hk : k≤1) (hG : k≤lambdaG atG r) (hH : k≤lambdaH atH s)
    (i : Fin 5) (hi : i≠distinguished atH c) :
    (blocks C hg atG atH k m c r s i).p=pWeights atG atH k m c r s i ∧
      (blocks C hg atG atH k m c r s i).q=qWeights atG atH k m c r s i := by
  by_cases ho : ordinaryD atH c
  · have he : atH=true := ho.1
    subst atH
    fin_cases i <;>
      simp [blocks,Block.p,Block.q,pWeights,qWeights,distinguished,ho,lambdaD,
        JointNegativeAETD2.Source.lambdaD,min_eq_left hk,max_eq_right hk,
        min_eq_left hG,max_eq_right hG,min_eq_left hH,max_eq_right hH,
        min_eq_left ho.2.le,max_eq_right ho.2.le] at hi ⊢
  · fin_cases i <;>
      simp [blocks,Block.p,Block.q,pWeights,qWeights,distinguished,ho,
        min_eq_left hk,max_eq_right hk,min_eq_left hG,max_eq_right hG,
        min_eq_left hH,max_eq_right hH] at hi ⊢

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Source
