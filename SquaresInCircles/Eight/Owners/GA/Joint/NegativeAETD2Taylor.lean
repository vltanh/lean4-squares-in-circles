module

public import SquaresInCircles.Eight.Owners.BoundedRadicalPerturbation
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Coefficients
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Polynomial

/-!
# Eight squares: the Taylor allowance in the joint-negative numerators

Four masses, their erased products and the weighted radicands are compared at the two input
pairs, the sine and cosine and their Taylor polynomials `S15` and `C16` (`numerator_error`). The
uniform bound is below `10^-8` (`actual_numerator_positive`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Analytic
open Candidate Secondary Polynomial
open Certificate (Row Endpoint)
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
def weightData (r : Row) (e : Endpoint) (_s t : ℝ) : Fin 4→ℝ :=
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
  have hS : aeval z PositiveScalarPolynomials.sine=S15 z := PositiveScalarPolynomials.sine_eval z
  have hC : aeval z PositiveScalarPolynomials.cosine=C16 z :=
    PositiveScalarPolynomials.cosine_eval z
  have hk : aeval z (Certificate.k r)=Explicit.k r z := rfl
  have hc : aeval z (Certificate.c r)=Explicit.c r z := rfl
  have hM : aeval z (Certificate.M r)=mData (Explicit.c r z) (S15 z) (C16 z) := by
    simp [Certificate.M,mData,hS,hC,hc,eta]
  have hα (i : Fin 4) : aeval z (Certificate.alpha r e i)=
      alphaData r e (Explicit.k r z) (Explicit.c r z) (S15 z) (C16 z) i := by
    cases r <;> cases e <;> fin_cases i <;>
      simp [Certificate.alpha,alphaData,Certificate.diagonalD,hS,hC,hk,hc,hM] <;> ring
  have hv (i : Fin 4) : aeval z (Certificate.v r e i)=
      vData r e (Explicit.k r z) (Explicit.c r z) (S15 z) (C16 z) i := by
    cases r <;> cases e <;> fin_cases i <;>
      simp [Certificate.v,vData,Certificate.diagonalD,hS,hC,hk,hc,hM]
  have hw (i : Fin 4) : aeval z (Certificate.weight r e i)=
      weightData r e (S15 z) (C16 z) i := by
    cases r <;> cases e <;> fin_cases i <;>
      simp [Certificate.weight,weightData,Certificate.diagonalD,hC]
  have hH : aeval z (Certificate.H r e)=
      hData r e (Explicit.k r z) (Explicit.c r z) (S15 z) (C16 z) := by
    cases r <;> cases e <;>
      simp [Certificate.H,hData,Certificate.J,jData,Certificate.diagonalD,hS,hC,hk,hc,map_ofNat]
  simp only [Certificate.numerator,numeratorData,map_sub,map_mul,map_sum,map_prod,map_add,
    map_pow,aeval_C,hα,hv,hw,hH,eq_ratCast,Rat.cast_ofNat]

theorem product_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι→ℝ)
    (ha : ∀i∈s,|a i|≤2) : |∏i∈s,a i|≤(2:ℝ)^s.card := by
  rw [Finset.abs_prod]
  calc ∏i∈s,|a i|≤∏_i∈s,(2:ℝ) := Finset.prod_le_prod₀ (fun i _ => abs_nonneg (a i)) ha
    _=(2:ℝ)^s.card := Finset.prod_const 2

theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι→ℝ)
    {ε : ℝ} (hε : 0≤ε) (ha : ∀i∈s,|a i|≤2) (hb : ∀i∈s,|b i|≤2)
    (hd : ∀i∈s,|a i-b i|≤3*ε) : |(∏i∈s,a i)-(∏i∈s,b i)|≤(6:ℝ)^s.card*ε := by
  revert ha hb hd
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simpa using hε
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
    have h6 : 0≤(6:ℝ)^s.card*ε := mul_nonneg (pow_nonneg (by norm_num) _) hε
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.card_insert_of_notMem hi,pow_succ]
    linarith

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
  have heta : (0:ℝ)≤eta := by norm_num [eta]
  have hh := linear_difference
    (a:=c) (b:=c*eta) (A:=7/5) (B:=3/5)
    (by rw [abs_of_nonneg hc.1]; exact hc.2)
    (by rw [abs_of_nonneg (mul_nonneg hc.1 heta)]; simp only [eta]; linarith [hc.2]) ht hs
  have hid : mData c s t-mData c s' t'=(c*t+(c*eta)*s)-(c*t'+(c*eta)*s') := by
    simp only [mData]; ring
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
  have ht0 : 0≤t := by linarith [ht.1]
  have hksq := pow_le_pow_left₀ hk0 hk.2 2
  have hcsq := pow_le_pow_left₀ hc0 hc.2 2
  have hmsq := pow_le_pow_left₀ hm.1 hm.2 2
  have htsq := pow_le_pow_left₀ ht0 ht.2 2
  have hkt := mul_le_mul hk.2 ht.2 ht0 (by norm_num : (0:ℝ)≤751/1000)
  have hkt0 := mul_nonneg hk0 ht0
  have hkt2 := mul_le_mul hksq htsq (sq_nonneg t) (by norm_num : (0:ℝ)≤(751/1000)^2)
  have hkt20 := mul_nonneg (sq_nonneg k) (sq_nonneg t)
  have hks := mul_le_mul hk.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤751/1000)
  have hks0 := mul_nonneg hk0 hs.1
  have hsig : (Certificate.sigmaPlus:ℝ)=1416128429/1000000000 := by
    norm_num [Certificate.sigmaPlus]
  have hj : |jData s t|≤4 := by
    rw [abs_le]; simp only [jData,eta,hsig]
    constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
  have hcj : |c*jData s t|≤28/5 := by
    rw [abs_mul,abs_of_nonneg hc0]
    calc c*|jData s t|≤7/5*4 := mul_le_mul hc.2 hj (abs_nonneg _) (by norm_num)
      _=28/5 := by norm_num
  have hA : |2*k+5+c*jData s t|≤13 := by
    have hh := abs_add_le (2*k+5) (c*jData s t)
    rw [abs_of_nonneg (by linarith : (0:ℝ)≤2*k+5)] at hh
    linarith [hk.2]
  have hRd : (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)≤7/5 ∧
      0≤(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ) := by
    norm_num [Certificate.Rplus,Certificate.dPlus]
  have hdiag : |(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)|≤7/2 := by
    rw [abs_of_nonneg (mul_nonneg hRd.2 (by linarith))]
    have hh := mul_le_mul hRd.1 (show 1+c≤12/5 by linarith [hc.2]) (by linarith)
      (by norm_num : (0:ℝ)≤7/5)
    linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> simp only [alphaData,Fin.reduceFinMk,Matrix.cons_val,mem_Icc] <;>
      (try split_ifs) <;> constructor <;>
      linarith only [hk.1,hk.2,hc.1,hc.2,hs.1,hs.2,ht.1,ht.2,hm.1,hm.2,hkt,hkt0]
  · intro i
    fin_cases i <;> simp only [vData,Fin.reduceFinMk,Matrix.cons_val] <;>
      (try split_ifs) <;> rw [abs_le] <;> constructor <;>
      linarith only [sq_nonneg k,sq_nonneg c,sq_nonneg (mData c s t),hksq,hcsq,hmsq,hkt2,
        hkt20,hks,hks0]
  · intro i
    fin_cases i <;> simp only [weightData,Fin.reduceFinMk,Matrix.cons_val,mem_Icc] <;>
      (try split_ifs) <;> constructor <;> linarith only [ht.1,ht.2]
  · have hT : |t|≤1001/1000 := by rw [abs_of_nonneg ht0]; exact ht.2
    have hprod := mul_le_mul hA hT (abs_nonneg t) (by norm_num : (0:ℝ)≤13)
    have hdiagprod := mul_le_mul hdiag hT (abs_nonneg t) (by norm_num : (0:ℝ)≤7/2)
    rw [←abs_mul] at hprod hdiagprod
    have hlin : |(13/12:ℝ)*s|≤1 := by
      rw [abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have hV : |2*k+5+t+c*jData s t|≤15 := by
      rw [show 2*k+5+t+c*jData s t=(2*k+5+c*jData s t)+t by ring]
      linarith [abs_add_le (2*k+5+c*jData s t) t]
    have hF : |(2*k+5+c*jData s t)*t+1+(13/12)*s|≤16 := by
      have h1 := abs_add_le ((2*k+5+c*jData s t)*t) 1
      have h2 := abs_add_le ((2*k+5+c*jData s t)*t+1) ((13/12)*s)
      rw [abs_one] at h1
      linarith
    cases r <;> cases e <;>
      simp only [hData,Certificate.diagonalD,↓reduceIte,reduceCtorEq,Bool.false_eq_true,
        mul_one,sub_zero]
    all_goals
      have hb1 := sub_abs_bound (2*k+5+t+c*jData s t)
        ((Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c))
      have hb2 := sub_abs_bound ((2*k+5+c*jData s t)*t+1+(13/12)*s)
        ((Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)*t)
      generalize (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)=Rd at *
      linarith

theorem data_errors (r : Row) (e : Endpoint) {k c s t s' t' ε : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc k (7/5))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000))
    (_hs' : s'∈Icc (0:ℝ) (129/200)) (ht' : t'∈Icc (191/250:ℝ) (1001/1000))
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
    (show |mData c s t|≤7/5 by rw [abs_of_nonneg hm.1]; exact hm.2)
    (show |mData c s' t'|≤7/5 by rw [abs_of_nonneg hm'.1]; exact hm'.2) hM
  have hT1 : |t|≤1001/1000 := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2
  have hT1' : |t'|≤1001/1000 := by rw [abs_of_nonneg (by linarith [ht'.1])]; exact ht'.2
  have htsq := square_difference hT1 hT1' hT
  have hsig : (Certificate.sigmaPlus:ℝ)=1416128429/1000000000 := by
    norm_num [Certificate.sigmaPlus]
  have hJ : |jData s t-jData s' t'|≤3*ε := by
    have hh := linear_difference (a:=2) (b:=1/2+(3/2)*eta-1416128429/1000000000)
      (A:=2) (B:=1) (by norm_num) (by rw [abs_le]; norm_num [eta]) hT hS
    have hid : jData s t-jData s' t'=(2*t+(1/2+(3/2)*eta-1416128429/1000000000)*s)-
        (2*t'+(1/2+(3/2)*eta-1416128429/1000000000)*s') := by
      simp only [jData,hsig]; ring
    rw [hid]
    exact hh.trans_eq (by ring)
  have hA : |(2*k+5+c*jData s t)-(2*k+5+c*jData s' t')|≤5*ε := by
    have hh := constant_product_difference
      (show |c|≤7/5 by rw [abs_of_nonneg hc0]; exact hc.2) hJ
    have he : (2*k+5+c*jData s t)-(2*k+5+c*jData s' t')=
        c*jData s t-c*jData s' t' := by ring
    rw [he]
    linarith
  have hAbound : |2*k+5+c*jData s t|≤13 := by
    have hj : |jData s t|≤4 := by
      rw [abs_le]; simp only [jData,eta,hsig]
      constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    have hp : |c*jData s t|≤7/5*4 := by
      rw [abs_mul,abs_of_nonneg hc0]
      exact mul_le_mul hc.2 hj (abs_nonneg _) (by norm_num)
    have hbase : |2*k+5|≤6502/1000 := by
      rw [abs_of_nonneg (by linarith)]; linarith [hk.2]
    linarith [abs_add_le (2*k+5) (c*jData s t)]
  have hRd : (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)≤7/5 ∧
      0≤(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ) := by
    norm_num [Certificate.Rplus,Certificate.dPlus]
  refine ⟨?_,?_,?_,?_⟩
  · have hB : |(20+21*mData c s t)/29-(20+21*mData c s' t')/29|≤3*ε := by
      rw [show (20+21*mData c s t)/29-(20+21*mData c s' t')/29=
        (21/29)*(mData c s t-mData c s' t') by ring,abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ)≤21/29)]
      linarith
    have hV : |(36*(k-s)+77*t)/85-(36*(k-s')+77*t')/85|≤3*ε := by
      have hh := linear_difference (a:=-(36/85)) (b:=77/85) (A:=1) (B:=1)
        (by rw [abs_le]; norm_num) (by rw [abs_le]; norm_num) hS hT
      have hid : (36*(k-s)+77*t)/85-(36*(k-s')+77*t')/85=
          ((-(36/85))*s+(77/85)*t)-((-(36/85))*s'+(77/85)*t') := by ring
      rw [hid]
      linarith
    have hF : |(91+60*k*t)/109-(91+60*k*t')/109|≤3*ε := by
      have hh := constant_product_difference (a:=60*k/109) (A:=1)
        (by rw [abs_of_nonneg (by positivity)]; linarith [hk.2]) hT
      have hid : (91+60*k*t)/109-(91+60*k*t')/109=(60*k/109)*t-(60*k/109)*t' := by ring
      rw [hid]
      linarith
    intro i
    fin_cases i <;> simp only [alphaData,Fin.reduceFinMk,Matrix.cons_val] <;>
      (try split_ifs) <;> (try simp only [sub_self,abs_zero]) <;> linarith
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
    have hMv : |(1+(mData c s t)^2)-(1+(mData c s' t')^2)|≤10*ε := by
      rw [show (1+(mData c s t)^2)-(1+(mData c s' t')^2)=(mData c s t)^2-(mData c s' t')^2
        by ring]
      linarith
    intro i
    fin_cases i <;> simp only [vData,Fin.reduceFinMk,Matrix.cons_val] <;>
      (try split_ifs) <;> (try simp only [sub_self,abs_zero]) <;> linarith
  · intro i
    fin_cases i <;> simp only [weightData,Fin.reduceFinMk,Matrix.cons_val] <;>
      (try split_ifs) <;> (try simp only [sub_self,abs_zero]) <;> linarith
  · have hp := product_difference hAbound hT1' hA hT
    have hlin := constant_product_difference (a:=13/12) (A:=2)
      (by rw [abs_of_nonneg (by norm_num)]; norm_num) hS
    have hV : |(2*k+5+t+c*jData s t)-(2*k+5+t'+c*jData s' t')|≤6*ε := by
      have hid : (2*k+5+t+c*jData s t)-(2*k+5+t'+c*jData s' t')=
        ((2*k+5+c*jData s t)-(2*k+5+c*jData s' t'))+(t-t') := by ring
      rw [hid]
      linarith [abs_add_le ((2*k+5+c*jData s t)-(2*k+5+c*jData s' t')) (t-t')]
    have hF : |((2*k+5+c*jData s t)*t+1+(13/12)*s)-
        ((2*k+5+c*jData s' t')*t'+1+(13/12)*s')|≤22*ε := by
      have hid : ((2*k+5+c*jData s t)*t+1+(13/12)*s)-
          ((2*k+5+c*jData s' t')*t'+1+(13/12)*s')=
        ((2*k+5+c*jData s t)*t-(2*k+5+c*jData s' t')*t')+
          ((13/12)*s-(13/12)*s') := by ring
      rw [hid]
      linarith [abs_add_le ((2*k+5+c*jData s t)*t-(2*k+5+c*jData s' t')*t')
        ((13/12)*s-(13/12)*s')]
    cases r <;> cases e <;>
      simp only [hData,Certificate.diagonalD,↓reduceIte,reduceCtorEq,Bool.false_eq_true,
        mul_one,sub_zero]
    all_goals generalize (Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)=Rd at *
    all_goals first
      | linarith
      | (rw [sub_sub_sub_cancel_right]; linarith)
      | (have hY : |Rd*(1+c)|≤7/2 := by
            rw [abs_of_nonneg (mul_nonneg hRd.2 (by linarith))]
            have hh := mul_le_mul hRd.1 (show 1+c≤12/5 by linarith [hc.2]) (by linarith)
              (by norm_num : (0:ℝ)≤7/5)
            linarith
         have hd := constant_product_difference hY hT
         rw [sub_sub_sub_comm]
         have hb := sub_abs_bound (((2*k+5+c*jData s t)*t+1+(13/12)*s)-
           ((2*k+5+c*jData s' t')*t'+1+(13/12)*s')) (Rd*(1+c)*t-Rd*(1+c)*t')
         linarith)

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
  have hcard (a : Finset (Fin 4)) : a.card≤4 := by
    simpa using Finset.card_le_univ a
  have hprod (a : Finset (Fin 4)) : |∏i∈a,alphaData r e k c s' t' i|≤16 := by
    have hh := product_bound a _ (fun i _ => hα' i)
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hcard a)
    norm_num at hp
    exact hh.trans hp
  have hdiff (a : Finset (Fin 4)) :
      |(∏i∈a,alphaData r e k c s t i)-(∏i∈a,alphaData r e k c s' t' i)|≤1296*ε := by
    have hh := product_error a _ _ hε (fun i _=>hα i) (fun i _=>hα' i) (fun i _=>he.1 i)
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤6) (hcard a)
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
      linarith [abs_add_le (vData r e k c s t i-vData r e k c s' t' i)
        ((alphaData r e k c s t i)^2-(alphaData r e k c s' t' i)^2),he.2.1 i]
    have hab (s₀ t₀ : ℝ) (hv : |vData r e k c s₀ t₀ i|≤4)
        (ha : |alphaData r e k c s₀ t₀ i|≤2) :
        |vData r e k c s₀ t₀ i+(alphaData r e k c s₀ t₀ i)^2|≤8 := by
      have hp := pow_le_pow_left₀ (abs_nonneg _) ha 2
      rw [sq_abs] at hp
      have hh := abs_add_le (vData r e k c s₀ t₀ i) ((alphaData r e k c s₀ t₀ i)^2)
      rw [abs_of_nonneg (sq_nonneg (alphaData r e k c s₀ t₀ i))] at hh
      linarith
    have hw : |weightData r e s t i|≤2 := by
      rw [abs_of_nonneg (hb.2.2.1 i).1]; exact (hb.2.2.1 i).2
    have habs := hab s t (hb.2.1 i) (hα i)
    have habs' := hab s' t' (hb'.2.1 i) (hα' i)
    have hwp := product_difference hw habs' (he.2.2.1 i) hsum
    have hwpbound :
        |weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)|≤16 := by
      rw [abs_mul]
      linarith [mul_le_mul hw habs (abs_nonneg _) (by norm_num : (0:ℝ)≤2)]
    have hwpdiff : |weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)-
        weightData r e s' t' i*(vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)|≤
          52*ε := by linarith
    have hh := product_difference hwpbound (hprod (Finset.univ.erase i)) hwpdiff
      (hdiff (Finset.univ.erase i))
    linarith
  have hsum := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun i : Fin 4 =>
    weightData r e s t i*(vData r e k c s t i+(alphaData r e k c s t i)^2)*
      (∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
    weightData r e s' t' i*(vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)*
      (∏j∈Finset.univ.erase i,alphaData r e k c s' t' j))
  simp only [Finset.sum_sub_distrib] at hsum
  have hsum' : ∑i : Fin 4,|weightData r e s t i*(vData r e k c s t i+
      (alphaData r e k c s t i)^2)*(∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
      weightData r e s' t' i*(vData r e k c s' t' i+(alphaData r e k c s' t' i)^2)*
        (∏j∈Finset.univ.erase i,alphaData r e k c s' t' j)|≤4*(22000*ε) := by
    calc _≤∑_i : Fin 4,22000*ε := Finset.sum_le_sum (fun i _=>hterm i)
      _=4*(22000*ε) := by simp
  have hid : numeratorData r e k c s t-numeratorData r e k c s' t'=
    2*(hData r e k c s t*(∏i,alphaData r e k c s t i)-
      hData r e k c s' t'*(∏i,alphaData r e k c s' t' i))-
    (Certificate.Rplus:ℝ)*((∑i,weightData r e s t i*(vData r e k c s t i+
      (alphaData r e k c s t i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
      (∑i,weightData r e s' t' i*(vData r e k c s' t' i+
        (alphaData r e k c s' t' i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s' t' j)) := by
    simp only [numeratorData]; ring
  rw [hid]
  have hR : (0:ℝ)≤Certificate.Rplus ∧ (Certificate.Rplus:ℝ)≤2 := by
    norm_num [Certificate.Rplus]
  generalize (Certificate.Rplus:ℝ)=R at hR ⊢
  have hY := mul_le_mul hR.2 (hsum.trans hsum') (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hnum := sub_abs_bound
    (2*(hData r e k c s t*(∏i,alphaData r e k c s t i)-
      hData r e k c s' t'*(∏i,alphaData r e k c s' t' i)))
    (R*((∑i,weightData r e s t i*(vData r e k c s t i+
      (alphaData r e k c s t i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s t j)-
      (∑i,weightData r e s' t' i*(vData r e k c s' t' i+
        (alphaData r e k c s' t' i)^2)*∏j∈Finset.univ.erase i,alphaData r e k c s' t' j)))
  rw [abs_mul,abs_mul,abs_two,abs_of_nonneg hR.1] at hnum
  linarith

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
    have hpos : 0 ≤ mData (Explicit.c r z) (S15 z) (C16 z) := by
      simp only [mData]
      apply mul_nonneg (by linarith [hr.1.1,hr.2.1])
      have := mul_nonneg (by norm_num [eta] : (0:ℝ)≤eta) hi.2.2.1.1
      linarith [hi.2.2.2.1]
    have hmax : mData (Explicit.c r z) (Real.sin z) (Real.cos z)≤69/50 :=
      hr.2.2.2.2.1.trans hr.2.2.2.2.2.1
    exact ⟨hpos,by norm_num [remainder] at hM; linarith [(abs_le.mp hM).1]⟩
  have hp := Certificate.numerator_positive r e hz
  rw [polynomial_identity] at hp
  have hd := numerator_error r e hr.1 ⟨hr.2.1,hr.2.2.1.le⟩
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hm hm' hε he.1 he.2
  norm_num [remainder] at hd
  linarith [(abs_le.mp hd).1]

end SquaresInCircles.Eight.GlobalGA.JointNegativeAETD2.Analytic
