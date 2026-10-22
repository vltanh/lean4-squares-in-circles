module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2Scalar

/-!
# Original owners, secant weights, and both remaining signed budgets

Uncompiled transcription of Sections 1--3 of the joint-negative TD2
exclusion. `atG` selects GA3 rather than AB2; `atH` selects EH1 rather
than DE3. Three fixed arguments are deleted from the analytic blocks.
The original cycle, its points, and its physical witnesses are retained.
When DE3 is selected the D block is identically zero; keeping that zero
summand permits the same four-index concentration statement in all cases.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open Certificate (Row)

abbrev sec := SecantNormCurvature.secant
def aError (C : SignedCycle) (atG : Bool) : ℝ := if atG then delta C.theta G else delta C.theta A
def eError (C : SignedCycle) (atH : Bool) : ℝ := if atH then delta C.theta E else delta C.theta D
def lambdaG (atG : Bool) (r : ℝ) : ℝ := if atG then sec r else 1
def lambdaB (atG : Bool) (r : ℝ) : ℝ := if atG then 1 else sec r
def lambdaH (atH : Bool) (s : ℝ) : ℝ := if atH then sec s else 1
def lambdaD (atH : Bool) (s : ℝ) : ℝ := if atH then 1 else sec s
def owners (hg : Fin 4) (atG atH : Bool) : Vertex→Fin 4 :=
  ![hg,if atG then 3 else 2,if atG then 0 else 2,2,2,if atH then 2 else 3,if atH then 1 else 0]
def weights (atG atH : Bool) (k c r s z : ℝ) : Vertex→ℝ :=
  ![k,lambdaG atG r,lambdaB atG r,tilted c z,c,lambdaD atH s,lambdaH atH s]
def pWeights (atG atH : Bool) (k m r s : ℝ) : Fin 4→ℝ := ![k,k,min (lambdaB atG r) m,k]
def qWeights (atG atH : Bool) (k m r s : ℝ) : Fin 4→ℝ :=
  ![lambdaH atH s,lambdaG atG r,max (lambdaB atG r) m,1]
def blocks (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k c r s : ℝ) : Fin 4→Block :=
  ![⟨k,lambdaH atH s,if hg=0 then 0 else delta C.theta H,if atH then 0 else delta C.theta E⟩,
    ⟨k,lambdaG atG r,if hg=0 then delta C.theta H else 0,if atG then 0 else delta C.theta G⟩,
    ⟨lambdaB atG r,tilted c (delta C.theta T),if atG then delta C.theta A else 0,delta C.theta B⟩,
    ⟨k,1,if atH then delta C.theta D else 0,0⟩]

theorem sum_parts (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k c r s : ℝ)
    (f : ℝ→ℝ) (hf : f 0=0) :
    (∑i,f (blocks C hg atG atH k c r s i).u+f (blocks C hg atG atH k c r s i).v)=
      (∑v,f (delta C.theta v))-f (delta C.theta T)-f (aError C atG)-f (eError C atH) := by
  cases atG <;> cases atH <;> by_cases hhg : hg=0 <;>
    simp [blocks,aError,eError,hhg,Fin.sum_univ_succ,H,G,A,B,T,D,E,hf] <;> ring

structure Budget (C : SignedCycle) (hg : Fin 4) (atG atH : Bool) (k c r s : ℝ) : Prop where
  total_domain : r+s∈Icc 0 frameCap
  td_domain : delta C.theta T∈Icc 0 frameCap
  positive_eq : (∑i,(blocks C hg atG atH k c r s i).P)=positiveVariation C.theta-delta C.theta T
  negative_eq : (∑i,(blocks C hg atG atH k c r s i).N)=negativeVariation C.theta-r-s
  positive_bound : (∑i,(blocks C hg atG atH k c r s i).P)≤frameCap-delta C.theta T
  negative_bound : (∑i,(blocks C hg atG atH k c r s i).N)≤frameCap-(r+s)
  balance : (∑i,(blocks C hg atG atH k c r s i).N)-
    (∑i,(blocks C hg atG atH k c r s i).P)=delta C.theta T-(r+s)

theorem budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k c : ℝ)
    (hr : 0≤r) (hs : 0≤s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) :
    Budget C hg atG atH k c r s := by
  have hp := sum_parts C hg atG atH k c r s positivePart positivePart_zero
  have hn := sum_parts C hg atG atH k c r s negativePart negativePart_zero
  have hpz : positivePart (delta C.theta T)=delta C.theta T := max_eq_left hz
  have hnz : negativePart (delta C.theta T)=0 := max_eq_right (by linarith)
  have hpa : positivePart (aError C atG)=0 := by rw [ha]; exact max_eq_right (by linarith)
  have hpe : positivePart (eError C atH)=0 := by rw [he]; exact max_eq_right (by linarith)
  have hna : negativePart (aError C atG)=r := by
    rw [ha]; simpa [negativePart] using max_eq_left hr
  have hne : negativePart (eError C atH)=s := by
    rw [he]; simpa [negativePart] using max_eq_left hs
  have hP : (∑i,(blocks C hg atG atH k c r s i).P)=positiveVariation C.theta-delta C.theta T := by
    simpa only [Block.P,positiveVariation,hpz,hpa,hpe,sub_zero] using hp
  have hN : (∑i,(blocks C hg atG atH k c r s i).N)=negativeVariation C.theta-r-s := by
    simpa only [Block.N,negativeVariation,hnz,hna,hne,sub_zero] using hn
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>(blocks C hg atG atH k c r s i).P_nonneg)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _=>(blocks C hg atG atH k c r s i).N_nonneg)
  have hvariation := variations_equal C.theta
  exact ⟨⟨add_nonneg hr hs,by linarith⟩,⟨hz,by linarith⟩,hP,hN,
    by linarith,by linarith,by linarith⟩

theorem block_budgets {C : SignedCycle} {r s : ℝ} (hg : Fin 4) (atG atH : Bool) (k c : ℝ)
    (hr : 0≤r) (hs : 0≤s) (ha : aError C atG= -r) (he : eError C atH= -s)
    (hvar : positiveVariation C.theta≤frameCap) (hz : 0≤delta C.theta T) (i : Fin 4) :
    (blocks C hg atG atH k c r s i).P≤frameCap ∧ (blocks C hg atG atH k c r s i).N≤frameCap := by
  have hb := budgets hg atG atH k c hr hs ha he hvar hz
  have hp := Finset.single_le_sum (s:=Finset.univ)
    (fun j _=>(blocks C hg atG atH k c r s j).P_nonneg) (Finset.mem_univ i)
  have hn := Finset.single_le_sum (s:=Finset.univ)
    (fun j _=>(blocks C hg atG atH k c r s j).N_nonneg) (Finset.mem_univ i)
  exact ⟨by linarith [hb.positive_bound],by linarith [hb.negative_bound]⟩

theorem secant_short {x : ℝ} (hx : x∈Icc (0:ℝ) (19/50)) :
    sec x∈Icc (1:ℝ) (539/500) := by
  have ht := trig_bracket (l:=0) (u:=(19/50:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hc : (500/539:ℝ)<Real.cos x := by norm_num at ht; linarith [ht.2.2.1]
  have hcos : 0<Real.cos x := by linarith
  refine ⟨SecantNormCurvature.secant_ge_one hcos,?_⟩
  dsimp [SecantNormCurvature.secant]
  apply (div_le_iff₀ hcos).2
  nlinarith

theorem lambda_bounds (atG atH : Bool) {r s : ℝ}
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) :
    lambdaG atG r∈Icc (1:ℝ) (539/500) ∧ lambdaB atG r∈Icc (1:ℝ) (539/500) ∧
      lambdaH atH s∈Icc (1:ℝ) (539/500) ∧ 0<lambdaD atH s := by
  have hA := secant_short hr
  have hE := SecantNormCurvature.secant_ge_one (show 0<Real.cos s by linarith [(transport_trig hs).1])
  cases atG <;> cases atH <;> simp only [lambdaG,lambdaB,lambdaH,lambdaD,if_true,if_false]
  all_goals first
    | exact ⟨⟨by norm_num,by norm_num⟩,hA,⟨by norm_num,by norm_num⟩,by linarith⟩
    | exact ⟨hA,⟨by norm_num,by norm_num⟩,⟨by norm_num,by norm_num⟩,by linarith⟩
    | have hh := secant_short ⟨hs.1,by linarith [hH rfl]⟩
      exact ⟨⟨by norm_num,by norm_num⟩,hA,hh,by norm_num⟩
    | have hh := secant_short ⟨hs.1,by linarith [hH rfl]⟩
      exact ⟨hA,⟨by norm_num,by norm_num⟩,hh,by norm_num⟩

theorem pair_domain (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (i : Fin 4) :
    0<pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i ∧
      pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i≤
        qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i ∧
      qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i≤
        (17/10)*pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s i := by
  have hc := Explicit.ranges f hz
  have hl := lambda_bounds atG atH hr hs hH
  have hk : 0<Explicit.k f z := by linarith [hc.1.1]
  have hm : 0<Explicit.m f z := hk.trans_le hc.2.2.2.1
  have hcap : Explicit.m f z≤69/50 := hc.2.2.2.2.1.trans hc.2.2.2.2.2.1
  fin_cases i
  · simp only [pWeights,qWeights,Matrix.cons_val_zero]
    exact ⟨hk,by linarith [hc.1.2,hl.2.2.1.1],by linarith [hc.1.1,hl.2.2.1.2]⟩
  · simp only [pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact ⟨hk,by linarith [hc.1.2,hl.1.1],by linarith [hc.1.1,hl.1.2]⟩
  · change 0<min (lambdaB atG r) (Explicit.m f z) ∧
      min (lambdaB atG r) (Explicit.m f z)≤max (lambdaB atG r) (Explicit.m f z) ∧
      max (lambdaB atG r) (Explicit.m f z)≤(17/10)*min (lambdaB atG r) (Explicit.m f z)
    refine ⟨lt_min (by linarith [hl.2.1.1]) hm,min_le_max,?_⟩
    rcases le_total (lambdaB atG r) (Explicit.m f z) with hh|hh
    · rw [min_eq_left hh,max_eq_right hh]
      linarith [hl.2.1.1]
    · rw [min_eq_right hh,max_eq_left hh]
      linarith [hl.2.1.2,hc.2.2.2.1,hc.1.1]
  · simp only [pWeights,qWeights,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact ⟨hk,by linarith [hc.1.2],by linarith [hc.1.1]⟩

theorem block_coefficients {C : SignedCycle} {hg : Fin 4} (atG atH : Bool) {k c r s : ℝ}
    (hk : k≤1) (hG : k≤lambdaG atG r) (hH : k≤lambdaH atH s) (i : Fin 4) :
    (blocks C hg atG atH k c r s i).p=pWeights atG atH k (tilted c (delta C.theta T)) r s i ∧
      (blocks C hg atG atH k c r s i).q=qWeights atG atH k (tilted c (delta C.theta T)) r s i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,pWeights,qWeights,
    min_eq_left hk,max_eq_right hk,min_eq_left hG,max_eq_right hG,min_eq_left hH,max_eq_right hH]

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Source
