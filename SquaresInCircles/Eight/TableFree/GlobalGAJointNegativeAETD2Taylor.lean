module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2Coefficients
public import SquaresInCircles.Eight.TableFree.BoundedRadicalPerturbation

/-!
# The explicit Taylor allowance in the joint-negative numerators

Uncompiled algebraic version of the product-derivative bound following
(18) in the scalar companion. Four masses, their erased products, and
the weighted radicands are compared at the two actual input pairs.
The uniform bound is smaller than the hand proof's 10^-8 allowance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Analytic
open Candidate Secondary Polynomial Certificate (Row Endpoint)
open BoundedRadicalPerturbation HighOrderTaylor

def mData (c s t : ℝ) : ℝ := c*(t+eta*s)
def jData (s t : ℝ) : ℝ := 1+2*t+(1/2+(3/2)*eta-(Certificate.sigmaPlus:ℝ))*s
def vData (r : Row) (e : Endpoint) (k c s t : ℝ) : Fin 4→ℝ :=
  ![1+k^2,1+(mData c s t)^2,if e=.V then 1+k^2-2*k*s else 1+k^2*t^2,
    if Certificate.diagonalD r then 0 else 1+c^2]
def alphaData (r : Row) (e : Endpoint) (k c s t : ℝ) : Fin 4→ℝ :=
  ![(91+60*k)/109,(20+21*mData c s t)/29,
    if e=.V then (36*(k-s)+77*t)/85 else (91+60*k*t)/109,
    if Certificate.diagonalD r then 1 else (21+20*c)/29]
def weightData (r : Row) (e : Endpoint) (s t : ℝ) : Fin 4→ℝ :=
  ![if e=.V then 1 else t,if e=.V then 1 else t,1,
    if Certificate.diagonalD r then 0 else if e=.V then 1 else t]
def hData (r : Row) (e : Endpoint) (k c s t : ℝ) : ℝ :=
  (if e=.V then 2*k+5+t+c*jData s t else (2*k+5+c*jData s t)*t+1+(13/12)*s)-
    if Certificate.diagonalD r then
      (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*(if e=.V then 1 else t) else 0
def numeratorData (r : Row) (e : Endpoint) (k c s t : ℝ) : ℝ :=
  2*hData r e k c s t*(∏i,alphaData r e k c s t i)-(Certificate.Rplus:ℝ)*
    ∑i,weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)*
      ∏j∈Finset.univ.erase i,alphaData r e k c s t j

theorem polynomial_identity (r : Row) (e : Endpoint) (z : ℝ) :
    aeval z (Certificate.numerator r e)=
      numeratorData r e (Explicit.k r z) (Explicit.c r z) (S15 z) (C16 z) := by
  simp only [Certificate.numerator,numeratorData,map_sub,map_mul,map_sum,map_prod,
    map_pow,aeval_C,map_ofNat]
  congr 2
  all_goals
    simp [Certificate.H,Certificate.alpha,Certificate.v,Certificate.weight,Certificate.M,
      Certificate.J,Certificate.S,Certificate.Cstar,PositiveScalarPolynomials.sine_eval,
      PositiveScalarPolynomials.cosine_eval,hData,alphaData,vData,weightData,mData,jData,
      Explicit.k,Explicit.c,eta,Certificate.eta]

theorem product_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι→ℝ)
    (ha : ∀i∈s,|a i|≤2) : |∏i∈s,a i|≤(2:ℝ)^s.card := by
  rw [Finset.abs_prod]
  have hh := Finset.prod_le_prod (fun i hi => abs_nonneg (a i)) ha
  simpa using hh

theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι→ℝ)
    {ε : ℝ} (hε : 0≤ε) (ha : ∀i∈s,|a i|≤2) (hb : ∀i∈s,|b i|≤2)
    (hd : ∀i∈s,|a i-b i|≤3*ε) : |(∏i∈s,a i)-(∏i∈s,b i)|≤(6:ℝ)^s.card*ε := by
  revert ha hb hd
  induction s using Finset.induction_on with
  | empty => intro ha hb hd; simpa using hε
  | @insert i s hi ih =>
    intro ha hb hd
    have ha' := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hd' := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hprev := ih ha' hb' hd'
    have hprod := product_bound s b hb'
    have hh := product_difference (ha i (Finset.mem_insert_self i s)) hprod
      (hd i (Finset.mem_insert_self i s)) hprev
    have hp : (2:ℝ)^s.card≤(6:ℝ)^s.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_right hp hε
    simp only [Finset.prod_insert hi,Finset.card_insert_of_not_mem hi,pow_succ] at ⊢
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤6) s.card]

theorem input_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    Real.sin z∈Icc (0:ℝ) (129/200) ∧ Real.cos z∈Icc (191/250:ℝ) (1001/1000) ∧
      S15 z∈Icc (0:ℝ) (129/200) ∧ C16 z∈Icc (191/250:ℝ) (1001/1000) := by
  have ht := transport_trig hz
  have he := frame_remainders hz
  have hS := S15_nonneg hz
  norm_num [remainder] at he
  exact ⟨⟨ht.2.2.1,by linarith [ht.2.2.2.1]⟩,
    ⟨by linarith [ht.1],by linarith [ht.2.1]⟩,
    ⟨hS,by linarith [ht.2.2.2.1,he.1]⟩,
    ⟨by linarith [ht.1,he.2.2.1],by linarith [ht.2.1,he.2.2.2]⟩⟩

theorem input_errors {z : ℝ} (hz : z∈Icc 0 frameCap) :
    |Real.sin z-S15 z|≤remainder ∧ |Real.cos z-C16 z|≤remainder := by
  have hh := frame_remainders hz
  refine ⟨by rw [abs_of_nonneg hh.1]; exact hh.2.1.le,?_⟩
  rw [abs_sub_comm,abs_of_nonneg hh.2.2.1]
  exact hh.2.2.2.le

theorem m_error {c s s' t t' ε : ℝ} (hc : c∈Icc (0:ℝ) (7/5))
    (hs : |s-s'|≤ε) (ht : |t-t'|≤ε) :
    |mData c s t-mData c s' t'|≤2*ε := by
  have hε : 0≤ε := (abs_nonneg _).trans hs
  have hh := linear_difference
    (a:=c) (b:=c*eta) (A:=7/5) (B:=3/5)
    (by rw [abs_of_nonneg hc.1]; exact hc.2)
    (by rw [abs_of_nonneg (by norm_num [eta]; positivity)]; norm_num [eta]; nlinarith [hc.2]) ht hs
  have hid : mData c s t-mData c s' t'=(c*t+(c*eta)*s)-(c*t'+(c*eta)*s') := by
    dsimp [mData]; ring
  rw [hid]
  linarith

theorem data_bounds (r : Row) (e : Endpoint) {k c s t : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc k (7/5))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000))
    (hm : mData c s t∈Icc (0:ℝ) (7/5)) :
    (∀i,alphaData r e k c s t i∈Icc (1/2:ℝ) 2) ∧
      (∀i,|vData r e k c s t i|≤4) ∧
      (∀i,weightData r e s t i∈Icc (0:ℝ) 2) ∧ |hData r e k c s t|≤20 := by
  have hc0 : 0≤c := by linarith [hk.1,hc.1]
  have hk0 : 0≤k := by linarith [hk.1]
  have hksq := pow_le_pow_left₀ hk0 hk.2 2
  have hcsq := pow_le_pow_left₀ hc0 hc.2 2
  have hmsq := pow_le_pow_left₀ hm.1 hm.2 2
  have htsq := pow_le_pow_left₀ (show 0≤t by linarith [ht.1]) ht.2 2
  have hkt := mul_le_mul hk.2 ht.2 (by linarith [ht.1]) (by norm_num : (0:ℝ)≤751/1000)
  have hkt2 := mul_le_mul hksq htsq (sq_nonneg t) (by norm_num : (0:ℝ)≤(751/1000)^2)
  have hks := mul_le_mul hk.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤751/1000)
  have hks0 := mul_nonneg hk0 hs.1
  have hj : |jData s t|≤4 := by
    apply abs_le.mpr
    norm_num [jData,eta,Certificate.sigmaPlus]
    constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
  have hA : |2*k+5+c*jData s t|≤13 := by
    have hp := mul_le_mul hc.2 hj (abs_nonneg (jData s t)) (by norm_num : (0:ℝ)≤7/5)
    rw [←abs_of_nonneg hc0,←abs_mul] at hp
    have hh := abs_add (2*k+5) (c*jData s t)
    have hbase : |2*k+5|≤13/2 := by rw [abs_of_nonneg (by positivity)]; linarith [hk.2]
    linarith
  have hdiag : |(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)|≤7/2 := by
    rw [abs_of_nonneg (by norm_num [Certificate.Rplus,Certificate.dPlus]; positivity)]
    norm_num [Certificate.Rplus,Certificate.dPlus]
    nlinarith [hc.2]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [alphaData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      constructor <;> nlinarith [hk.1,hk.2,hc.1,hc.2,hs.1,hs.2,ht.1,ht.2,hm.1,hm.2]
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [vData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ] <;>
      apply abs_le.mpr <;> constructor <;> nlinarith [sq_nonneg k,sq_nonneg c,sq_nonneg (mData c s t)]
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp [weightData,Certificate.diagonalD] <;> constructor <;> linarith [ht.1,ht.2]
  · have hT : |t|≤1001/1000 := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2
    have hS : |s|≤129/200 := by rw [abs_of_nonneg hs.1]; exact hs.2
    have hprod := mul_le_mul hA hT (abs_nonneg t) (by norm_num : (0:ℝ)≤13)
    have hdiagprod := mul_le_mul hdiag hT (abs_nonneg t) (by norm_num : (0:ℝ)≤7/2)
    rw [←abs_mul] at hprod hdiagprod
    have hlin : |(13/12:ℝ)*s|≤1 := by rw [abs_mul]; norm_num; nlinarith
    have hV : |2*k+5+t+c*jData s t|≤15 := by
      rw [show 2*k+5+t+c*jData s t=(2*k+5+c*jData s t)+t by ring]
      linarith [abs_add (2*k+5+c*jData s t) t]
    have hF : |(2*k+5+c*jData s t)*t+1+(13/12)*s|≤16 := by
      have h1 := abs_add ((2*k+5+c*jData s t)*t) 1
      have h2 := abs_add ((2*k+5+c*jData s t)*t+1) ((13/12)*s)
      norm_num at h1
      linarith
    cases r <;> cases e <;>
      simp only [hData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,mul_one,sub_zero]
    all_goals nlinarith [
      sub_abs_bound (2*k+5+t+c*jData s t) ((Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)),
      sub_abs_bound ((2*k+5+c*jData s t)*t+1+(13/12)*s)
        ((Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t)]

theorem data_errors (r : Row) (e : Endpoint) {k c s t s' t' ε : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc k (7/5))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000))
    (hs' : s'∈Icc (0:ℝ) (129/200)) (ht' : t'∈Icc (191/250:ℝ) (1001/1000))
    (hm : mData c s t∈Icc (0:ℝ) (7/5)) (hm' : mData c s' t'∈Icc (0:ℝ) (7/5))
    (hε : 0≤ε) (hS : |s-s'|≤ε) (hT : |t-t'|≤ε) :
    (∀i,|alphaData r e k c s t i-alphaData r e k c s' t' i|≤3*ε) ∧
      (∀i,|vData r e k c s t i-vData r e k c s' t' i|≤10*ε) ∧
      (∀i,|weightData r e s t i-weightData r e s' t' i|≤ε) ∧
      |hData r e k c s t-hData r e k c s' t'|≤32*ε := by
  have hk0 : 0≤k := by linarith [hk.1]
  have hc0 : 0≤c := by linarith [hk.1,hc.1]
  have hc' : c∈Icc (0:ℝ) (7/5) := ⟨hc0,hc.2⟩
  have hM := m_error hc' hS hT
  have hMsq := square_difference
    (show |mData c s t|≤7/5 by rwa [abs_of_nonneg hm.1])
    (show |mData c s' t'|≤7/5 by rwa [abs_of_nonneg hm'.1]) hM
  have htsq := square_difference
    (show |t|≤1001/1000 by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2)
    (show |t'|≤1001/1000 by rw [abs_of_nonneg (by linarith [ht'.1])]; exact ht'.2) hT
  have hJ : |jData s t-jData s' t'|≤3*ε := by
    have hh := linear_difference (a:=2) (b:=1/2+(3/2)*eta-(Certificate.sigmaPlus:ℝ))
      (A:=2) (B:=1) (by norm_num) (by norm_num [eta,Certificate.sigmaPlus]) hT hS
    simpa [jData] using hh
  have hA : |(2*k+5+c*jData s t)-(2*k+5+c*jData s' t')|≤5*ε := by
    have hh := constant_product_difference
      (show |c|≤7/5 by rwa [abs_of_nonneg hc0]) hJ
    have he : (2*k+5+c*jData s t)-(2*k+5+c*jData s' t')=
        c*jData s t-c*jData s' t' := by ring
    rw [he]
    linarith
  have hAbound : |2*k+5+c*jData s t|≤13 := by
    have hj : |jData s t|≤4 := by
      apply abs_le.mpr
      norm_num [jData,eta,Certificate.sigmaPlus]
      constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    have hp := mul_le_mul hc.2 hj (abs_nonneg (jData s t)) (by norm_num : (0:ℝ)≤7/5)
    rw [←abs_of_nonneg hc0,←abs_mul] at hp
    have hbase : |2*k+5|≤13/2 := by rw [abs_of_nonneg (by positivity)]; linarith [hk.2]
    linarith [abs_add (2*k+5) (c*jData s t)]
  have hdiag : |(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)|≤7/2 := by
    rw [abs_of_nonneg (by norm_num [Certificate.Rplus,Certificate.dPlus]; positivity)]
    norm_num [Certificate.Rplus,Certificate.dPlus]
    nlinarith [hc.2]
  refine ⟨?_,?_,?_,?_⟩
  · have hB : |(20+21*mData c s t)/29-(20+21*mData c s' t')/29|≤3*ε := by
      rw [show (20+21*mData c s t)/29-(20+21*mData c s' t')/29=
        (21/29)*(mData c s t-mData c s' t') by ring,abs_mul]
      norm_num
      nlinarith
    have hV : |(36*(k-s)+77*t)/85-(36*(k-s')+77*t')/85|≤3*ε := by
      have hh := linear_difference (a:=-(36/85)) (b:=77/85) (A:=1) (B:=1)
        (by norm_num) (by norm_num) hS hT
      have hid : (36*(k-s)+77*t)/85-(36*(k-s')+77*t')/85=
          ((-(36/85))*s+(77/85)*t)-((-(36/85))*s'+(77/85)*t') := by ring
      rw [hid]
      linarith
    have hF : |(91+60*k*t)/109-(91+60*k*t')/109|≤3*ε := by
      have hh := constant_product_difference (a:=60*k/109) (A:=1)
        (by rw [abs_of_nonneg (by positivity)]; nlinarith [hk.2]) hT
      have hid : (91+60*k*t)/109-(91+60*k*t')/109=(60*k/109)*t-(60*k/109)*t' := by ring
      rw [hid]
      linarith
    intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [alphaData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sub_self,abs_zero] <;> linarith
  · have hV : |(1+k^2-2*k*s)-(1+k^2-2*k*s')|≤10*ε := by
      have hh := constant_product_difference (a:=2*k) (A:=2)
        (by rw [abs_of_nonneg (by positivity)]; linarith [hk.2]) hS
      have hid : (1+k^2-2*k*s)-(1+k^2-2*k*s')= -(2*k*s-2*k*s') := by ring
      rw [hid,abs_neg]
      linarith
    have hF : |(1+k^2*t^2)-(1+k^2*t'^2)|≤10*ε := by
      have hksq : |k^2|≤1 := by rw [abs_of_nonneg (sq_nonneg k)]; nlinarith [hk.1,hk.2]
      have hh := constant_product_difference hksq htsq
      have hid : (1+k^2*t^2)-(1+k^2*t'^2)=k^2*t^2-k^2*t'^2 := by ring
      rw [hid]
      linarith
    intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [vData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sub_self,abs_zero] <;> linarith
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [weightData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sub_self,abs_zero] <;> linarith
  · have hp := product_difference hAbound
      (show |t'|≤1001/1000 by rw [abs_of_nonneg (by linarith [ht'.1])]; exact ht'.2) hA hT
    have hlin := constant_product_difference (a:=13/12) (A:=2) (by norm_num) hS
    have hd := constant_product_difference hdiag hT
    have hV : |(2*k+5+t+c*jData s t)-(2*k+5+t'+c*jData s' t')|≤6*ε := by
      have hid : (2*k+5+t+c*jData s t)-(2*k+5+t'+c*jData s' t')=
        ((2*k+5+c*jData s t)-(2*k+5+c*jData s' t'))+(t-t') := by ring
      rw [hid]
      linarith [abs_add ((2*k+5+c*jData s t)-(2*k+5+c*jData s' t')) (t-t')]
    have hF : |((2*k+5+c*jData s t)*t+1+(13/12)*s)-
        ((2*k+5+c*jData s' t')*t'+1+(13/12)*s')|≤22*ε := by
      have hid : ((2*k+5+c*jData s t)*t+1+(13/12)*s)-
          ((2*k+5+c*jData s' t')*t'+1+(13/12)*s')=
        ((2*k+5+c*jData s t)*t-(2*k+5+c*jData s' t')*t')+
          ((13/12)*s-(13/12)*s') := by ring
      rw [hid]
      linarith [abs_add ((2*k+5+c*jData s t)*t-(2*k+5+c*jData s' t')*t')
        ((13/12)*s-(13/12)*s')]
    cases r <;> cases e <;>
      simp only [hData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,mul_one,sub_zero]
    all_goals
      first
      | linarith
      | have hid : ((2*k+5+t+c*jData s t)-(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c))-
            ((2*k+5+t'+c*jData s' t')-(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c))=
          (2*k+5+t+c*jData s t)-(2*k+5+t'+c*jData s' t') := by ring
        rw [hid]; linarith
      | have hid :
          ((2*k+5+c*jData s t)*t+1+(13/12)*s-(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t)-
          ((2*k+5+c*jData s' t')*t'+1+(13/12)*s'-(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t')=
          (((2*k+5+c*jData s t)*t+1+(13/12)*s)-((2*k+5+c*jData s' t')*t'+1+(13/12)*s'))-
          ((Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t-
            (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t') := by ring
        rw [hid]
        linarith [sub_abs_bound
          (((2*k+5+c*jData s t)*t+1+(13/12)*s)-((2*k+5+c*jData s' t')*t'+1+(13/12)*s'))
          ((Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t-
            (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t')]

theorem numerator_error (r : Row) (e : Endpoint) {k c s t s' t' ε : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc k (7/5))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000))
    (hs' : s'∈Icc (0:ℝ) (129/200)) (ht' : t'∈Icc (191/250:ℝ) (1001/1000))
    (hm : mData c s t∈Icc (0:ℝ) (7/5)) (hm' : mData c s' t'∈Icc (0:ℝ) (7/5))
    (hε : 0≤ε) (hS : |s-s'|≤ε) (hT : |t-t'|≤ε) :
    |numeratorData r e k c s t-numeratorData r e k c s' t'|≤1000000*ε := by
  have hb := data_bounds r e hk hc hs ht hm
  have hb' := data_bounds r e hk hc hs' ht' hm'
  have he := data_errors r e hk hc hs ht hs' ht' hm hm' hε hS hT
  have hα (i : Fin 4) : |alphaData r e k c s t i|≤2 := by
    rw [abs_of_nonneg (by linarith [(hb.1 i).1])]; exact (hb.1 i).2
  have hα' (i : Fin 4) : |alphaData r e k c s' t' i|≤2 := by
    rw [abs_of_nonneg (by linarith [(hb'.1 i).1])]; exact (hb'.1 i).2
  have hprod (a : Finset (Fin 4)) : |∏i∈a,alphaData r e k c s' t' i|≤16 := by
    have hh := product_bound a _ (fun i _ => hα' i)
    have hn : a.card≤4 := Finset.card_le_univ a
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn
    norm_num at hp
    exact hh.trans hp
  have hdiff (a : Finset (Fin 4)) :
      |(∏i∈a,alphaData r e k c s t i)-(∏i∈a,alphaData r e k c s' t' i)|≤1296*ε := by
    have hh := product_error a _ _ hε (fun i _=>hα i) (fun i _=>hα' i) (fun i _=>he.1 i)
    have hn : a.card≤4 := Finset.card_le_univ a
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤6) hn
    norm_num at hp
    have hmul := mul_le_mul_of_nonneg_right hp hε
    exact hh.trans hmul
  have hfirst := product_difference hb.2.2.2 (hprod Finset.univ) he.2.2.2 (hdiff Finset.univ)
  have hterm (i : Fin 4) :
      |weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)*
          (∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
        weightData r e s' t' i*(vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)*
          (∏j∈Finset.univ.erase i,alphaData r e k c s' t' j)|≤22000*ε := by
    have hsq := square_difference (hα i) (hα' i) (he.1 i)
    have hsum : |(vData r e k c s t i+(alphaData r e k c s t i)^2)-
        (vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)|≤22*ε := by
      have hid : (vData r e k c s t i+(alphaData r e k c s t i)^2)-
          (vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)=
        (vData r e k c s t i-vData r e k c s' t' i)+
          ((alphaData r e k c s t i)^2-(alphaData r e k c s' t' i)^2) := by ring
      rw [hid]
      linarith [abs_add (vData r e k c s t i-vData r e k c s' t' i)
        ((alphaData r e k c s t i)^2-(alphaData r e k c s' t' i)^2),he.2.1 i]
    have hab (s₀ t₀ : ℝ) (hv : |vData r e k c s₀ t₀ i|≤4)
        (ha : |alphaData r e k c s₀ t₀ i|≤2) :
        |vData r e k c s₀ t₀ i+(alphaData r e k c s₀ t₀ i)^2|≤8 := by
      have hp := pow_le_pow_left₀ (abs_nonneg _) ha 2
      rw [sq_abs] at hp
      have hh := abs_add (vData r e k c s₀ t₀ i) ((alphaData r e k c s₀ t₀ i)^2)
      rw [abs_of_nonneg (sq_nonneg _)] at hh
      linarith
    have hw : |weightData r e s t i|≤2 := by rw [abs_of_nonneg (hb.2.2.1 i).1]; exact (hb.2.2.1 i).2
    have hw' : |weightData r e s' t' i|≤2 := by rw [abs_of_nonneg (hb'.2.2.1 i).1]; exact (hb'.2.2.1 i).2
    have habs := hab s t (hb.2.1 i) (hα i)
    have habs' := hab s' t' (hb'.2.1 i) (hα' i)
    have hwp := product_difference hw habs' (he.2.2.1 i) hsum
    have hwpbound : |weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)|≤16 := by
      rw [abs_mul]
      nlinarith [mul_le_mul hw habs (abs_nonneg _) (by norm_num : (0:ℝ)≤2)]
    have hwpdiff : |weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)-
        weightData r e s' t' i*(vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)|≤52*ε := by linarith
    have hh := product_difference hwpbound (hprod (Finset.univ.erase i)) hwpdiff (hdiff (Finset.univ.erase i))
    linarith
  have hsum := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun i : Fin 4 =>
    weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)*
      (∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
    weightData r e s' t' i*(vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)*
      (∏j∈Finset.univ.erase i,alphaData r e k c s' t' j))
  have hsum' := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hterm i)
  simp only [Finset.sum_sub_distrib] at hsum
  norm_num at hsum'
  have hnum := sub_abs_bound
    (2*(hData r e k c s t*(∏i,alphaData r e k c s t i)-
      hData r e k c s' t'*(∏i,alphaData r e k c s' t' i)))
    ((Certificate.Rplus:ℝ)*((∑i,weightData r e s t i*(vData r e k c s t i+
      (alphaData r e k c s t i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
      (∑i,weightData r e s' t' i*(vData r e k c s' t' i+
        (alphaData r e k c s' t' i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s' t' j)))
  have hid : numeratorData r e k c s t-numeratorData r e k c s' t'=
    2*(hData r e k c s t*(∏i,alphaData r e k c s t i)-
      hData r e k c s' t'*(∏i,alphaData r e k c s' t' i))-
    (Certificate.Rplus:ℝ)*((∑i,weightData r e s t i*(vData r e k c s t i+
      (alphaData r e k c s t i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
      (∑i,weightData r e s' t' i*(vData r e k c s' t' i+
        (alphaData r e k c s' t' i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s' t' j)) := by
    dsimp [numeratorData]; ring
  rw [hid]
  rw [abs_mul,abs_mul] at hnum
  norm_num [Certificate.Rplus] at hnum
  nlinarith

theorem actual_numerator_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<numeratorData r e (Explicit.k r z) (Explicit.c r z) (Real.sin z) (Real.cos z) := by
  have hr := Explicit.ranges r hz
  have hdomain := Explicit.frame_domain r hz
  have hi := input_bounds hdomain
  have he := input_errors hdomain
  have hε : 0≤remainder := by norm_num [remainder]
  have hM := m_error (show Explicit.c r z∈Icc (0:ℝ) (7/5) from
    ⟨by linarith [hr.1.1,hr.2.1],hr.2.2.1.le⟩) he.1 he.2
  have hm : mData (Explicit.c r z) (Real.sin z) (Real.cos z)∈Icc (0:ℝ) (7/5) := by
    change Explicit.m r z∈Icc (0:ℝ) (7/5)
    exact ⟨by linarith [hr.1.1,hr.2.2.2.1],by linarith [hr.2.2.2.2.1,hr.2.2.2.2.2.1]⟩
  have hm' : mData (Explicit.c r z) (S15 z) (C16 z)∈Icc (0:ℝ) (7/5) := by
    have hpos : 0≤mData (Explicit.c r z) (S15 z) (C16 z) := by
      dsimp [mData]
      apply mul_nonneg (by linarith [hr.1.1,hr.2.1])
      nlinarith [hi.2.2.1.1,hi.2.2.2.1]
    have hmax : mData (Explicit.c r z) (Real.sin z) (Real.cos z)≤69/50 :=
      hr.2.2.2.2.1.trans hr.2.2.2.2.2.1
    exact ⟨hpos,by norm_num [remainder] at hM; linarith [(abs_le.mp hM).1]⟩
  have hp := Certificate.numerator_positive r e hz
  rw [polynomial_identity] at hp
  have hd := numerator_error r e hr.1 ⟨hr.2.1,hr.2.2.1.le⟩
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hm hm' hε he.1 he.2
  norm_num [remainder] at hd
  linarith [(abs_le.mp hd).1]

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Analytic
