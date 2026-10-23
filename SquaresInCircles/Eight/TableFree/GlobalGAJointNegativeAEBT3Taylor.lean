module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAEBT3AnalyticData

/-!
# A whole-input Taylor allowance for the joint-negative BT3 numerator

Uncompiled product estimate for the five positive masses. All factors
are bounded at the two inputs before their differences are multiplied.
The final allowance is 10^-9, below the hand proof's 10^-8 allowance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Analytic
open Candidate Secondary Polynomial Certificate (Row Endpoint)
open BoundedRadicalPerturbation HighOrderTaylor

theorem data_errors (r : Row) (e : Endpoint) {k c eta s t s' t' ε : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc (7/10:ℝ) (7/5))
    (he : eta∈Icc (0:ℝ) (9/20))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000))
    (hs' : s'∈Icc (0:ℝ) (129/200)) (ht' : t'∈Icc (191/250:ℝ) (1001/1000))
    (hε : 0≤ε) (hS : |s-s'|≤ε) (hT : |t-t'|≤ε) :
    (∀i,|alphaData r e k c eta s t i-alphaData r e k c eta s' t' i|≤4*ε) ∧
      (∀i,|vData r e k c eta s t i-vData r e k c eta s' t' i|≤10*ε) ∧
      (∀i,|weightData r e c eta s t i-weightData r e c eta s' t' i|≤4*ε) ∧
      |AData r e k c eta s t-AData r e k c eta s' t'|≤100*ε := by
  have hf := factor_bounds he hs ht
  have hf' := factor_bounds he hs' ht'
  have hdiff := factor_errors he hε hS hT
  have hka : |k|≤1 := by rw [abs_of_nonneg (by linarith [hk.1])]; linarith [hk.2]
  have hca : |c|≤7/5 := by rw [abs_of_nonneg (by linarith [hc.1])]; exact hc.2
  have hfa : |fData eta s t|≤13/10 := by rw [abs_of_nonneg (by linarith [hf.1.1])]; exact hf.1.2
  have hfa' : |fData eta s' t'|≤13/10 := by rw [abs_of_nonneg (by linarith [hf'.1.1])]; exact hf'.1.2
  have hta : |t|≤1001/1000 := by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.2
  have hta' : |t'|≤1001/1000 := by rw [abs_of_nonneg (by linarith [ht'.1])]; exact ht'.2
  have hsa : |s|≤129/200 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hsa' : |s'|≤129/200 := by rw [abs_of_nonneg hs'.1]; exact hs'.2
  have hft : |fData eta s t*t-fData eta s' t'*t'|≤4*ε := by
    have hh := product_difference hfa hta' hdiff.1 hT
    linarith
  have hcs : |c*s-c*s'|≤2*ε := by
    have hh := constant_product_difference hca hS
    linarith
  have hcsa : |c*s|≤1 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hca hsa (abs_nonneg s) (by norm_num : (0:ℝ)≤7/5)]
  have hcst : |c*s*t-c*s'*t'|≤4*ε := by
    have hh := product_difference hcsa hta' hcs hT
    linarith
  have hαB : |(20*fData eta s t+21*c)/29-(20*fData eta s' t'+21*c)/29|≤4*ε := by
    have hh := constant_product_difference (a:=20/29) (A:=1) (by norm_num) hdiff.1
    rw [show (20*fData eta s t+21*c)/29-(20*fData eta s' t'+21*c)/29=
      (20/29)*fData eta s t-(20/29)*fData eta s' t' by ring]
    linarith
  have hαV : |(36*(k-s)+77*t)/85-(36*(k-s')+77*t')/85|≤4*ε := by
    have hh := linear_difference (a:=-(36/85)) (b:=77/85) (A:=1) (B:=1)
      (by norm_num) (by norm_num) hS hT
    rw [show (36*(k-s)+77*t)/85-(36*(k-s')+77*t')/85=
      ((-(36/85))*s+(77/85)*t)-((-(36/85))*s'+(77/85)*t') by ring]
    linarith
  have hαF : |(91+60*k*t)/109-(91+60*k*t')/109|≤4*ε := by
    have hh := constant_product_difference (a:=60*k/109) (A:=1)
      (by rw [abs_of_nonneg (by linarith [hk.1])]; linarith [hk.2]) hT
    rw [show (91+60*k*t)/109-(91+60*k*t')/109=(60*k/109)*t-(60*k/109)*t' by ring]
    linarith
  have hvB : |((fData eta s t)^2+c^2)-((fData eta s' t')^2+c^2)|≤10*ε := by
    have hh := square_difference hfa hfa' hdiff.1
    simpa only [add_sub_add_right_eq_sub] using hh.trans (by nlinarith : (2:ℝ)*(13/10)*(2*ε)≤10*ε)
  have hvV : |(1+k^2-2*k*s)-(1+k^2-2*k*s')|≤10*ε := by
    have hh := constant_product_difference (a:=2*k) (A:=2)
      (by rw [abs_mul]; norm_num; linarith) hS
    rw [show (1+k^2-2*k*s)-(1+k^2-2*k*s')= -(2*k*s-2*k*s') by ring,abs_neg]
    linarith
  have hvF : |(1+k^2*t^2)-(1+k^2*t'^2)|≤10*ε := by
    have htsq := square_difference hta hta' hT
    have hk2 : |k^2|≤1 := by nlinarith [sq_abs k,pow_le_pow_left₀ (abs_nonneg k) hka 2]
    have hh := constant_product_difference hk2 htsq
    rw [show (1+k^2*t^2)-(1+k^2*t'^2)=k^2*t^2-k^2*t'^2 by ring]
    linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [alphaData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sub_self,abs_zero] <;> linarith
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [vData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sub_self,abs_zero] <;> linarith
  · intro i
    cases r <;> cases e <;> fin_cases i <;>
      simp only [weightData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,
        Matrix.cons_val_zero,Matrix.cons_val_succ,sub_self,abs_zero] <;> linarith [hdiff.1]
  · have hκ : |2*k+5|≤7 := by rw [abs_of_nonneg (by linarith [hk.1])]; linarith [hk.2]
    have hκt : |2*k+5+t'|≤8 := by rw [abs_of_nonneg (by linarith [hk.1,ht'.1])]; linarith [hk.2,ht'.2]
    have hJ := constant_product_difference hca hdiff.2
    have hfirst := product_difference hfa hκt hdiff.1
      (show |(2*k+5+t)-(2*k+5+t')|≤ε by simpa using hT)
    have hV := add_error hfirst hJ
    have hbaseFirst := constant_product_difference hκ hdiff.1
    have hbaseFirst' : |fData eta s t*(2*k+5)-fData eta s' t'*(2*k+5)|≤14*ε := by
      simpa only [mul_comm] using hbaseFirst
    have hbase := add_error hbaseFirst' hJ
    have hbaseA : |fData eta s t*(2*k+5)+c*TData eta s t|≤16 := by
      have ha := mul_le_mul hfa hκ (abs_nonneg _) (by norm_num : (0:ℝ)≤13/10)
      have hJabs : |TData eta s t|≤9/2 := by rw [abs_of_nonneg hf.2.1]; exact hf.2.2
      have hb := mul_le_mul hca hJabs (abs_nonneg _) (by norm_num : (0:ℝ)≤7/5)
      rw [←abs_mul] at ha hb
      linarith [abs_add (fData eta s t*(2*k+5)) (c*TData eta s t)]
    have hbase20 : |(fData eta s t*(2*k+5)+c*TData eta s t)-
        (fData eta s' t'*(2*k+5)+c*TData eta s' t')|≤20*ε := by linarith
    have hbaseT := product_difference hbaseA hta' hbase20 hT
    have hlast := product_difference hfa
      (show |1+(13/12)*s'|≤2 by rw [abs_of_nonneg (by positivity)]; linarith [hs'.2])
      hdiff.1 (show |(1+(13/12)*s)-(1+(13/12)*s')|≤2*ε by
        simpa using constant_product_difference (a:=13/12) (A:=2) (by norm_num) hS)
    have hF := add_error hbaseT hlast
    have hdiag : |(Certificate.Rplus:ℝ)*(Certificate.dPlus:ℝ)*(1+c)|≤7/2 := by
      rw [abs_of_nonneg (by norm_num [Certificate.Rplus,Certificate.dPlus]; positivity)]
      norm_num [Certificate.Rplus,Certificate.dPlus]
      nlinarith [hc.2]
    have hdV := constant_product_difference hdiag hdiff.1
    have hdF := constant_product_difference hdiag hft
    have hVdiag := subtract_error hV hdV
    have hFdiag := subtract_error hF hdF
    cases r <;> cases e <;>
      simp only [AData,Certificate.diagonalD,if_true,if_false,reduceCtorEq,mul_one,sub_zero,mul_assoc] at ⊢ hVdiag hFdiag <;>
      linarith

theorem product_bound {ι : Type*} [DecidableEq ι] (a : Finset ι) (v : ι→ℝ)
    (hv : ∀i∈a,|v i|≤3) : |∏i∈a,v i|≤(3:ℝ)^a.card := by
  rw [Finset.abs_prod]
  have hh := Finset.prod_le_prod (fun i hi => abs_nonneg (v i)) hv
  simpa using hh

theorem product_error {ι : Type*} [DecidableEq ι] (a : Finset ι) (v w : ι→ℝ)
    {ε : ℝ} (hε : 0≤ε) (hv : ∀i∈a,|v i|≤3) (hw : ∀i∈a,|w i|≤3)
    (hd : ∀i∈a,|v i-w i|≤4*ε) : |(∏i∈a,v i)-(∏i∈a,w i)|≤(10:ℝ)^a.card*ε := by
  revert hv hw hd
  induction a using Finset.induction_on with
  | empty => intro hv hw hd; simpa using hε
  | @insert i a hi ih =>
    intro hv hw hd
    have hv' := fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hw' := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hd' := fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hh := product_difference (hv i (Finset.mem_insert_self i a)) (product_bound a w hw')
      (hd i (Finset.mem_insert_self i a)) (ih hv' hw' hd')
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) (by norm_num : (3:ℝ)≤10) a.card
    have hm := mul_le_mul_of_nonneg_right hp hε
    simp only [Finset.prod_insert hi,Finset.card_insert_of_not_mem hi,pow_succ] at ⊢
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤10) a.card]

theorem numerator_error (r : Row) (e : Endpoint) {k c eta s t s' t' ε : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hc : c∈Icc (7/10:ℝ) (7/5))
    (he : eta∈Icc (0:ℝ) (9/20))
    (hs : s∈Icc (0:ℝ) (129/200)) (ht : t∈Icc (191/250:ℝ) (1001/1000))
    (hs' : s'∈Icc (0:ℝ) (129/200)) (ht' : t'∈Icc (191/250:ℝ) (1001/1000))
    (hε : 0≤ε) (hS : |s-s'|≤ε) (hT : |t-t'|≤ε) :
    |numeratorData r e k c eta s t-numeratorData r e k c eta s' t'|≤100000000*ε := by
  have hb := data_bounds r e hk hc he hs ht
  have hb' := data_bounds r e hk hc he hs' ht'
  have hd := data_errors r e hk hc he hs ht hs' ht' hε hS hT
  let a := alphaData r e k c eta s t
  let a' := alphaData r e k c eta s' t'
  let v := vData r e k c eta s t
  let v' := vData r e k c eta s' t'
  let w := weightData r e c eta s t
  let w' := weightData r e c eta s' t'
  have ha (i : Fin 5) : |a i|≤3 := by rw [abs_of_nonneg (by linarith [(hb.1 i).1])]; exact (hb.1 i).2
  have ha' (i : Fin 5) : |a' i|≤3 := by rw [abs_of_nonneg (by linarith [(hb'.1 i).1])]; exact (hb'.1 i).2
  have hp (b : Finset (Fin 5)) : |∏i∈b,a' i|≤243 := by
    have hh := product_bound b a' (fun i _ => ha' i)
    have hc : b.card≤5 := Finset.card_le_univ b
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3) hc
    norm_num at hpow
    exact hh.trans hpow
  have hpd (b : Finset (Fin 5)) : |(∏i∈b,a i)-(∏i∈b,a' i)|≤100000*ε := by
    have hh := product_error b a a' hε (fun i _ => ha i) (fun i _ => ha' i) (fun i _ => hd.1 i)
    have hc : b.card≤5 := Finset.card_le_univ b
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤10) hc
    norm_num at hpow
    exact hh.trans (mul_le_mul_of_nonneg_right hpow hε)
  have hfirst := product_difference hb.2.2.2 (hp Finset.univ) hd.2.2.2 (hpd Finset.univ)
  have hterm (i : Fin 5) :
      |w i*(v i+(a i)^2)*(∏j∈Finset.univ.erase i,a j)-
        w' i*(v' i+(a' i)^2)*(∏j∈Finset.univ.erase i,a' j)|≤3000000*ε := by
    have hsq := square_difference (ha i) (ha' i) (hd.1 i)
    have hsum := add_error (hd.2.1 i) hsq
    have hab : |v i+(a i)^2|≤13 := by
      have hh := abs_add (v i) ((a i)^2)
      rw [abs_of_nonneg (sq_nonneg _)] at hh
      nlinarith [hb.2.1 i,pow_le_pow_left₀ (abs_nonneg _) (ha i) 2,sq_abs (a i)]
    have hab' : |v' i+(a' i)^2|≤13 := by
      have hh := abs_add (v' i) ((a' i)^2)
      rw [abs_of_nonneg (sq_nonneg _)] at hh
      nlinarith [hb'.2.1 i,pow_le_pow_left₀ (abs_nonneg _) (ha' i) 2,sq_abs (a' i)]
    have hw : |w i|≤2 := by rw [abs_of_nonneg (hb.2.2.1 i).1]; exact (hb.2.2.1 i).2
    have hws : |w i*(v i+(a i)^2)|≤26 := by
      rw [abs_mul]
      exact mul_le_mul hw hab (abs_nonneg _) (by norm_num)
    have hwd := product_difference hw hab' (hd.2.2.1 i) hsum
    have hwd' : |w i*(v i+(a i)^2)-w' i*(v' i+(a' i)^2)|≤120*ε := by linarith
    have hh := product_difference hws (hp (Finset.univ.erase i)) hwd' (hpd (Finset.univ.erase i))
    linarith
  have hsum := Finset.abs_sum_le_sum_abs (s:=Finset.univ) (fun i : Fin 5 =>
    w i*(v i+(a i)^2)*(∏j∈Finset.univ.erase i,a j)-
      w' i*(v' i+(a' i)^2)*(∏j∈Finset.univ.erase i,a' j))
  have hsum' := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_sub_distrib] at hsum
  norm_num at hsum'
  have hscaled := constant_product_difference (a:=(Certificate.Rplus:ℝ)) (A:=2)
    (by norm_num [Certificate.Rplus]) (hsum.trans hsum')
  have htwice := constant_product_difference (a:=(2:ℝ)) (A:=2) (by norm_num) hfirst
  have hh := subtract_error htwice hscaled
  change |2*(AData r e k c eta s t*(∏i,a i))-(Certificate.Rplus:ℝ)*
      (∑i,w i*(v i+(a i)^2)*∏j∈Finset.univ.erase i,a j)-
    (2*(AData r e k c eta s' t'*(∏i,a' i))-(Certificate.Rplus:ℝ)*
      (∑i,w' i*(v' i+(a' i)^2)*∏j∈Finset.univ.erase i,a' j))|≤100000000*ε
  linarith

theorem actual_numerator_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (Certificate.left r:ℝ) (Certificate.right r:ℝ)) :
    0<numeratorData r e (Explicit.k r z) (Explicit.c r z) (Explicit.eta r z) (Real.sin z) (Real.cos z) := by
  have hr := Explicit.ranges r hz
  have hi := JointNegativeAETD2.Analytic.input_bounds (Explicit.frame_domain r hz)
  have he := input_errors (Explicit.frame_domain r hz)
  have hh := numerator_error r e hr.k_domain hr.c_domain hr.eta_domain
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 (by norm_num [epsilon]) he.1 he.2
  have hp := Certificate.numerator_positive r e hz
  rw [polynomial_identity] at hp
  have hlo := (abs_le.mp hh).1
  norm_num [epsilon] at hlo
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAEBT3.Analytic
