module

public import Mathlib.Data.Int.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveData

/-!
# Eight squares: the axial polynomials for opposite edge five

The sparse degree-thirteen numerator, its squared polynomial, the two degree-eight lower
polynomials and their division by `h-X` (`quotient_identity`) are kept exactly. All finite
arithmetic here is rational polynomial arithmetic decided by the kernel.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.AxialPolynomial
open Polynomial

def h : ℚ := 733/2500
def L (r : Bool) : ℚ :=
  157079632679489/100000000000000+50283/100000+pQ r*(1414575672/1000000000)+
    (PQ r+tQ r)/2-449/500
def denominator : ℚ[X] := 1+X^2
def eNumerator (r : Bool) : ℚ[X] := C (2*PQ r)*X+C (tQ r)*(1-X^2)
def radicalNumerator : ℚ[X] := C (9789/2500)*denominator^2-(C 3-X^2)^2*C (1/4)
def f (r : Bool) : ℚ[X] :=
  C (L r-3*PQ r/2)+C (-2+3*tQ r)*X+C (2*L r+2*PQ r)*X^2+
    C (-10/3-tQ r)*X^3+C (L r-PQ r/2)*X^4-C (16/15)*X^5+
      C (16/105)*X^7-C (16/315)*X^9-C (10/63)*X^11-C (2/9)*X^13
def polynomial (r : Bool) : ℚ[X] := (f r)^2-(eNumerator r)^2*radicalNumerator
def low : Bool→ℚ[X]
  | false => C (184988/100000000)-C (12669362/100000000)*X+C (275886083/100000000)*X^2-
      C (1129910079/100000000)*X^3+C (1664986399/100000000)*X^4-
        C (2393610952/100000000)*X^5+C (2262536812/100000000)*X^6-
          C (1473514417/100000000)*X^7+C (379/50)*X^8
  | true => C (139186/100000000)-C (10601133/100000000)*X+C (265965496/100000000)*X^2-
      C (1113153209/100000000)*X^3+C (1640798861/100000000)*X^4-
        C (2367380575/100000000)*X^5+C (2245323221/100000000)*X^6-
          C (1460933832/100000000)*X^7+C (189/25)*X^8
def remainder (r : Bool) : ℚ[X] := low r-C (1/10000)-C 3*X^8
def endpoint (r : Bool) : ℚ := (remainder r).eval h
def quotient (r : Bool) : ℚ[X] :=
  -∑j : Fin 8,C ((remainder r).coeff (j.val+1))*
    ∑k : Fin (j.val+1),C (h^(j.val-k.val))*X^k.val
def cubic0 : Bool→ℚ | false => 58479/10000000 | true => 43024/10000000
def cubic1 : Bool→ℚ | false => -4121613/10000000 | true => -3468926/10000000
def cubic2 : Bool→ℚ | false => 80037503/10000000 | true => 78880026/10000000
def cubic3 : Bool→ℚ | false => -128805661/10000000 | true => -12691901/1000000
def cubic (r : Bool) : ℚ[X] :=
  C (cubic0 r)+C (cubic1 r)*X+C (cubic2 r)*X^2+C (cubic3 r)*X^3
def reference : Bool→ℚ | false => 27/1000 | true => 23/1000
def valueLower : Bool→ℚ | false => 3007/10000000 | true => 3422/10000000
def slopeUpper : Bool→ℚ | false => 41/5000 | true => 21/5000
def curvature : Bool→ℚ | false => 353/100 | true => 179/50
def tailReserve (r : Bool) : ℚ :=
  ∑j : Fin 18,|(polynomial r).coeff (j.val+9)| *h^j.val
def lowDifference (r : Bool) : ℚ[X] :=
  (∑j : Fin 9,C ((polynomial r).coeff j.val)*X^j.val)-low r-C (2*h)*X^8


open WholeIntervalPolynomial.Certificate in
private theorem r84_rep_C {n : ℤ} {d : ℕ} {q : ℚ} (hq : (n:ℚ)=d*q) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,hq,map_mul]

open WholeIntervalPolynomial.Certificate in
/-- Integer representations of `polynomial r` (`c`) and of `low r+C (2h) X^8` (`d`), with the
coefficient bounds used below. -/
private theorem r84_cert (r : Bool) : ∃ c d : Scaled,
    c.Rep (polynomial r) ∧ d.Rep (low r+C (2*h)*X^8) ∧
    (c.s≠0 ∧ c.l.length≤27 ∧ d.s≠0 ∧ d.l.length≤9 ∧
      |c.l.getD 9 0| *2000<3771*(c.s:ℤ) ∧ |c.l.getD 10 0| *5000<919*(c.s:ℤ) ∧
      |c.l.getD 11 0| *10000<2771*(c.s:ℤ) ∧ |c.l.getD 12 0| *5000<309*(c.s:ℤ) ∧
      (∀ j : Fin 14,|c.l.getD (j.val+13) 0| *1<3*(c.s:ℤ)) ∧
      d.l.getD 0 0*(c.s:ℤ)<c.l.getD 0 0*(d.s:ℤ) ∧
      ∀ j : Fin 8,d.l.getD (j.val+1) 0*(c.s:ℤ)≤c.l.getD (j.val+1) 0*(d.s:ℤ)) := by
  have hrad : Scaled.Rep _ radicalNumerator :=
    ((r84_rep_C (n:=9789) (d:=2500) (q:=9789/2500) (by norm_num)).mul
      ((Scaled.rep_one.add (Scaled.rep_var.pow 2)).pow 2)).sub
      ((((r84_rep_C (n:=3) (d:=1) (q:=3) (by norm_num)).sub (Scaled.rep_var.pow 2)).pow 2).mul
        (r84_rep_C (n:=1) (d:=4) (q:=1/4) (by norm_num)))
  have h2h : Scaled.Rep _ (C (2*h)*X^8) :=
    (r84_rep_C (n:=733) (d:=1250) (q:=2*h) (by norm_num [h])).mul (Scaled.rep_var.pow 8)
  cases r
  · have hf : Scaled.Rep _ (f false) :=
      (((((((((r84_rep_C (n:=21562644912933) (d:=20000000000000) (q:=L false-3*PQ false/2)
        (by norm_num [L,PQ,pQ,tQ])).add
        ((r84_rep_C (n:=3151) (d:=6250) (q:=-2+3*tQ false) (by norm_num [tQ])).mul
          Scaled.rep_var)).add
        ((r84_rep_C (n:=32475644912933) (d:=10000000000000) (q:=2*L false+2*PQ false)
          (by norm_num [L,PQ,pQ,tQ])).mul (Scaled.rep_var.pow 2))).add
        ((r84_rep_C (n:=-78151) (d:=18750) (q:=-10/3-tQ false) (by norm_num [tQ])).mul
          (Scaled.rep_var.pow 3))).add
        ((r84_rep_C (n:=25927844912933) (d:=20000000000000) (q:=L false-PQ false/2)
          (by norm_num [L,PQ,pQ,tQ])).mul (Scaled.rep_var.pow 4))).sub
        ((r84_rep_C (n:=16) (d:=15) (q:=16/15) (by norm_num)).mul (Scaled.rep_var.pow 5))).add
        ((r84_rep_C (n:=16) (d:=105) (q:=16/105) (by norm_num)).mul (Scaled.rep_var.pow 7))).sub
        ((r84_rep_C (n:=16) (d:=315) (q:=16/315) (by norm_num)).mul (Scaled.rep_var.pow 9))).sub
        ((r84_rep_C (n:=10) (d:=63) (q:=10/63) (by norm_num)).mul (Scaled.rep_var.pow 11))).sub
        ((r84_rep_C (n:=2) (d:=9) (q:=2/9) (by norm_num)).mul (Scaled.rep_var.pow 13))
    have he : Scaled.Rep _ (eNumerator false) :=
      ((r84_rep_C (n:=10913) (d:=25000) (q:=2*PQ false) (by norm_num [PQ])).mul
        Scaled.rep_var).add
      ((r84_rep_C (n:=5217) (d:=6250) (q:=tQ false) (by norm_num [tQ])).mul
        (Scaled.rep_one.sub (Scaled.rep_var.pow 2)))
    have hlow : Scaled.Rep _ (low false) :=
      ((((((((r84_rep_C (n:=184988) (d:=100000000) (q:=184988/100000000) (by norm_num)).sub
        ((r84_rep_C (n:=12669362) (d:=100000000) (q:=12669362/100000000) (by norm_num)).mul
          Scaled.rep_var)).add
        ((r84_rep_C (n:=275886083) (d:=100000000) (q:=275886083/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 2))).sub
        ((r84_rep_C (n:=1129910079) (d:=100000000) (q:=1129910079/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 3))).add
        ((r84_rep_C (n:=1664986399) (d:=100000000) (q:=1664986399/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 4))).sub
        ((r84_rep_C (n:=2393610952) (d:=100000000) (q:=2393610952/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 5))).add
        ((r84_rep_C (n:=2262536812) (d:=100000000) (q:=2262536812/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 6))).sub
        ((r84_rep_C (n:=1473514417) (d:=100000000) (q:=1473514417/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 7))).add
        ((r84_rep_C (n:=379) (d:=50) (q:=379/50) (by norm_num)).mul (Scaled.rep_var.pow 8))
    exact ⟨_,_,(hf.pow 2).sub ((he.pow 2).mul hrad),hlow.add h2h,by decide +kernel⟩
  · have hf : Scaled.Rep _ (f true) :=
      (((((((((r84_rep_C (n:=107245104062417) (d:=100000000000000) (q:=L true-3*PQ true/2)
        (by norm_num [L,PQ,pQ,tQ])).add
        ((r84_rep_C (n:=6143) (d:=12500) (q:=-2+3*tQ true) (by norm_num [tQ])).mul
          Scaled.rep_var)).add
        ((r84_rep_C (n:=159662604062417) (d:=50000000000000) (q:=2*L true+2*PQ true)
          (by norm_num [L,PQ,pQ,tQ])).mul (Scaled.rep_var.pow 2))).add
        ((r84_rep_C (n:=-156143) (d:=37500) (q:=-10/3-tQ true) (by norm_num [tQ])).mul
          (Scaled.rep_var.pow 3))).add
        ((r84_rep_C (n:=128212104062417) (d:=100000000000000) (q:=L true-PQ true/2)
          (by norm_num [L,PQ,pQ,tQ])).mul (Scaled.rep_var.pow 4))).sub
        ((r84_rep_C (n:=16) (d:=15) (q:=16/15) (by norm_num)).mul (Scaled.rep_var.pow 5))).add
        ((r84_rep_C (n:=16) (d:=105) (q:=16/105) (by norm_num)).mul (Scaled.rep_var.pow 7))).sub
        ((r84_rep_C (n:=16) (d:=315) (q:=16/315) (by norm_num)).mul (Scaled.rep_var.pow 9))).sub
        ((r84_rep_C (n:=10) (d:=63) (q:=10/63) (by norm_num)).mul (Scaled.rep_var.pow 11))).sub
        ((r84_rep_C (n:=2) (d:=9) (q:=2/9) (by norm_num)).mul (Scaled.rep_var.pow 13))
    have he : Scaled.Rep _ (eNumerator true) :=
      ((r84_rep_C (n:=20967) (d:=50000) (q:=2*PQ true) (by norm_num [PQ])).mul
        Scaled.rep_var).add
      ((r84_rep_C (n:=10381) (d:=12500) (q:=tQ true) (by norm_num [tQ])).mul
        (Scaled.rep_one.sub (Scaled.rep_var.pow 2)))
    have hlow : Scaled.Rep _ (low true) :=
      ((((((((r84_rep_C (n:=139186) (d:=100000000) (q:=139186/100000000) (by norm_num)).sub
        ((r84_rep_C (n:=10601133) (d:=100000000) (q:=10601133/100000000) (by norm_num)).mul
          Scaled.rep_var)).add
        ((r84_rep_C (n:=265965496) (d:=100000000) (q:=265965496/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 2))).sub
        ((r84_rep_C (n:=1113153209) (d:=100000000) (q:=1113153209/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 3))).add
        ((r84_rep_C (n:=1640798861) (d:=100000000) (q:=1640798861/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 4))).sub
        ((r84_rep_C (n:=2367380575) (d:=100000000) (q:=2367380575/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 5))).add
        ((r84_rep_C (n:=2245323221) (d:=100000000) (q:=2245323221/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 6))).sub
        ((r84_rep_C (n:=1460933832) (d:=100000000) (q:=1460933832/100000000) (by norm_num)).mul
          (Scaled.rep_var.pow 7))).add
        ((r84_rep_C (n:=189) (d:=25) (q:=189/25) (by norm_num)).mul (Scaled.rep_var.pow 8))
    exact ⟨_,_,(hf.pow 2).sub ((he.pow 2).mul hrad),hlow.add h2h,by decide +kernel⟩

private theorem r84_abs_lt {n a b : ℤ} {s : ℕ} {q : ℚ} (hs : s≠0) (hb : 0<b) (hq : q=a/b)
    (h : |n| *b<a*(s:ℤ)) : |(n:ℚ)/s|<q := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  rw [hq,abs_div,abs_of_pos hs',div_lt_div_iff₀ hs' hb']
  exact_mod_cast h

private theorem r84_lowDifference_eq (r : Bool) : lowDifference r=
    (∑j : Fin 9,C ((polynomial r).coeff j.val)*X^j.val)-(low r+C (2*h)*X^8) := by
  rw [lowDifference]
  ring

private theorem r84_inner_coeff (j i : ℕ) :
    (∑k : Fin (j+1),C (h^(j-k.val))*X^k.val).coeff i=if i<j+1 then h^(j-i) else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Fin.sum_univ_eq_sum_range (fun k => if i=k then h^(j-k) else 0) (j+1),Finset.sum_ite_eq]
  simp [Finset.mem_range]

private theorem r84_quotient_coeff (r : Bool) (i : ℕ) :
    (quotient r).coeff i=
      -∑j : Fin 8,(remainder r).coeff (j.val+1)*(if i<j.val+1 then h^(j.val-i) else 0) := by
  rw [quotient,coeff_neg,finsetSum_coeff]
  simp only [coeff_C_mul,r84_inner_coeff]

private theorem r84_quotient_coeff' (r : Bool) (i : ℕ) :
    (quotient r).coeff i=
      -∑j ∈ Finset.range 8,(remainder r).coeff (j+1)*(if i<j+1 then h^(j-i) else 0) := by
  rw [r84_quotient_coeff,Finset.sum_range]

private theorem r84_remainder_false :
    (remainder false).coeff 1=-12669362/100000000 ∧ (remainder false).coeff 2=275886083/100000000 ∧
    (remainder false).coeff 3=-1129910079/100000000 ∧
    (remainder false).coeff 4=1664986399/100000000 ∧
    (remainder false).coeff 5=-2393610952/100000000 ∧
    (remainder false).coeff 6=2262536812/100000000 ∧
    (remainder false).coeff 7=-1473514417/100000000 ∧ (remainder false).coeff 8=229/50 := by
  simp only [remainder,low,coeff_sub,coeff_add,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X,
    Nat.reduceEqDiff,ite_true,ite_false,mul_one,mul_zero,sub_zero,add_zero,zero_add,zero_sub]
  norm_num

private theorem r84_remainder_true :
    (remainder true).coeff 1=-10601133/100000000 ∧ (remainder true).coeff 2=265965496/100000000 ∧
    (remainder true).coeff 3=-1113153209/100000000 ∧
    (remainder true).coeff 4=1640798861/100000000 ∧
    (remainder true).coeff 5=-2367380575/100000000 ∧
    (remainder true).coeff 6=2245323221/100000000 ∧
    (remainder true).coeff 7=-1460933832/100000000 ∧ (remainder true).coeff 8=114/25 := by
  simp only [remainder,low,coeff_sub,coeff_add,coeff_C_mul,coeff_C,coeff_X_pow,coeff_X,
    Nat.reduceEqDiff,ite_true,ite_false,mul_one,mul_zero,sub_zero,add_zero,zero_add,zero_sub]
  norm_num

private theorem r84_quotient_natDegree (r : Bool) : (quotient r).natDegree<8 := by
  rw [quotient,natDegree_neg]
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n:=7) _ _ fun j _ => ?_) (by norm_num)
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := k.isLt
  have := j.isLt
  omega

/-- Synthetic division by `X-a` of a polynomial of degree at most eight. -/
private theorem r84_synthetic (R : ℚ[X]) (hR : R.natDegree<9) (a : ℚ) :
    R=C (R.eval a)+(C a-X)*-∑j : Fin 8,C (R.coeff (j.val+1))*
      ∑k : Fin (j.val+1),C (a^(j.val-k.val))*X^k.val := by
  apply Polynomial.funext
  intro x
  simp only [eval_add,eval_C,eval_mul,eval_sub,eval_X,eval_neg,eval_finsetSum,eval_pow]
  rw [eval_eq_sum_range' hR x,eval_eq_sum_range' hR a]
  have hg (j : ℕ) : (x-a)*∑k : Fin (j+1),a^(j-k.val)*x^k.val=x^(j+1)-a^(j+1) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => a^(j-k)*x^k) (j+1),← geom_sum₂_mul x a (j+1),
      mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm,Nat.add_sub_cancel]
  have hsum : (a-x)*-∑j : Fin 8,R.coeff (j.val+1)*∑k : Fin (j.val+1),a^(j.val-k.val)*x^k.val=
      ∑j : Fin 8,R.coeff (j.val+1)*(x^(j.val+1)-a^(j.val+1)) := by
    rw [mul_neg,← neg_mul,neg_sub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hg j.val]
    ring
  rw [hsum,Fin.sum_univ_eq_sum_range (fun j => R.coeff (j+1)*(x^(j+1)-a^(j+1))) 8,
    Finset.sum_range_succ' (fun i => R.coeff i*x^i),Finset.sum_range_succ' (fun i => R.coeff i*a^i)]
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem tail_coefficients (r : Bool) :
    |(polynomial r).coeff 9|<3771/2000 ∧ |(polynomial r).coeff 10|<919/5000 ∧
    |(polynomial r).coeff 11|<2771/10000 ∧ |(polynomial r).coeff 12|<309/5000 ∧
    ∀j : Fin 14,|(polynomial r).coeff (j.val+13)|<3 := by
  obtain ⟨c,d,hc,-,hs,-,-,-,h9,h10,h11,h12,h13,-⟩ := r84_cert r
  rw [hc.coeff hs 9,hc.coeff hs 10,hc.coeff hs 11,hc.coeff hs 12]
  refine ⟨r84_abs_lt hs (by norm_num) (by norm_num) h9,r84_abs_lt hs (by norm_num) (by norm_num) h10,
    r84_abs_lt hs (by norm_num) (by norm_num) h11,r84_abs_lt hs (by norm_num) (by norm_num) h12,
    fun j => ?_⟩
  rw [hc.coeff hs]
  exact r84_abs_lt hs (by norm_num) (by norm_num) (h13 j)

theorem tail_reserve (r : Bool) :
    tailReserve r≤3771/2000+(919/5000)*h+(2771/10000)*h^2+(309/5000)*h^3+3*h^4/(1-h) ∧
    3771/2000+(919/5000)*h+(2771/10000)*h^2+(309/5000)*h^3+3*h^4/(1-h)≤2 := by
  obtain ⟨h9,h10,h11,h12,h13⟩ := tail_coefficients r
  have hh0 : (0:ℚ)≤h := by norm_num [h]
  refine ⟨?_,by norm_num [h]⟩
  have hsplit : tailReserve r=|(polynomial r).coeff 9|+|(polynomial r).coeff 10| *h+
      |(polynomial r).coeff 11| *h^2+|(polynomial r).coeff 12| *h^3+
      ∑j : Fin 14,|(polynomial r).coeff (j.val+13)| *h^(j.val+4) := by
    rw [tailReserve,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,add_assoc,Nat.reduceAdd,pow_zero,pow_one,mul_one,
      zero_add]
  rw [hsplit]
  have htail : ∑j : Fin 14,|(polynomial r).coeff (j.val+13)| *h^(j.val+4)≤
      ∑j : Fin 14,(3:ℚ)*h^(j.val+4) :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (h13 j).le (pow_nonneg hh0 _))
  have hgeo : ∑j : Fin 14,(3:ℚ)*h^(j.val+4)≤3*h^4/(1-h) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ]
    norm_num [h]
  have hm10 := mul_le_mul_of_nonneg_right h10.le hh0
  have hm11 := mul_le_mul_of_nonneg_right h11.le (pow_nonneg hh0 2)
  have hm12 := mul_le_mul_of_nonneg_right h12.le (pow_nonneg hh0 3)
  linarith [h9.le]

theorem low_expansion (r : Bool) :
    polynomial r=low r+lowDifference r+C (2*h)*X^8+PowerTailBounds.tail (polynomial r) 9 18 := by
  obtain ⟨c,d,hc,-,hs,hl,-⟩ := r84_cert r
  have hdeg : (polynomial r).natDegree<27 := by
    have := hc.natDegree_le hs
    omega
  rw [lowDifference,PowerTailBounds.tail]
  conv_lhs => rw [as_sum_range_C_mul_X_pow' (polynomial r) hdeg]
  rw [show 27=9+18 from rfl,Finset.sum_range_add,
    Fin.sum_univ_eq_sum_range (fun j => C ((polynomial r).coeff j)*X^j) 9,
    Fin.sum_univ_eq_sum_range (fun j => C ((polynomial r).coeff (j+9))*X^(j+9)) 18]
  have e : ∑x ∈ Finset.range 18,C ((polynomial r).coeff (9+x))*X^(9+x)=
      ∑x ∈ Finset.range 18,C ((polynomial r).coeff (x+9))*X^(x+9) :=
    Finset.sum_congr rfl (fun x _ => by rw [add_comm 9 x])
  rw [e]
  ring

theorem difference_expansion (r : Bool) :
    lowDifference r=C ((lowDifference r).coeff 0)+
      ∑j : Fin 8,C ((lowDifference r).coeff (j.val+1))*X^(j.val+1) := by
  obtain ⟨c,d,-,hd,-,-,hds,hdl,-⟩ := r84_cert r
  have hdeg : (lowDifference r).natDegree<9 := by
    have h1 : (∑j : Fin 9,C ((polynomial r).coeff j.val)*X^j.val).natDegree≤8 :=
      natDegree_sum_le_of_forall_le _ _
        (fun j _ => (natDegree_C_mul_X_pow_le _ _).trans (by have := j.isLt; omega))
    have h2 : (low r+C (2*h)*X^8).natDegree≤8 :=
      (hd.natDegree_le hds).trans (by omega)
    rw [r84_lowDifference_eq]
    exact lt_of_le_of_lt ((natDegree_sub_le _ _).trans (max_le h1 h2)) (by norm_num)
  conv_lhs => rw [as_sum_range_C_mul_X_pow' (lowDifference r) hdeg]
  rw [Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun j => C ((lowDifference r).coeff (j+1))*X^(j+1)) 8]
  simp only [pow_zero,mul_one]
  ring

theorem difference_coefficients (r : Bool) :
    0<(lowDifference r).coeff 0 ∧ ∀j : Fin 8,0≤(lowDifference r).coeff (j.val+1) := by
  obtain ⟨c,d,hc,hd,hcs,-,hds,-,-,-,-,-,-,h0,hj⟩ := r84_cert r
  have key (k : ℕ) (hk : k<9) :
      (lowDifference r).coeff k=(c.l.getD k 0:ℚ)/c.s-(d.l.getD k 0:ℚ)/d.s := by
    rw [r84_lowDifference_eq,coeff_sub,← hc.coeff hcs,← hd.coeff hds,finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Fin.sum_univ_eq_sum_range (fun j => if k=j then (polynomial r).coeff j else 0) 9,
      Finset.sum_ite_eq]
    simp only [Finset.mem_range,hk,ite_true]
  have hcs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hcs
  have hds' : (0:ℚ)<d.s := by exact_mod_cast Nat.pos_of_ne_zero hds
  constructor
  · rw [key 0 (by norm_num),sub_pos,div_lt_div_iff₀ hds' hcs']
    exact_mod_cast h0
  · intro j
    rw [key (j.val+1) (by omega),sub_nonneg,div_le_div_iff₀ hds' hcs']
    exact_mod_cast hj j

theorem quotient_identity (r : Bool) :
    low r=C (1/10000)+C 3*X^8+C (endpoint r)+(C h-X)*quotient r := by
  have hdeg : (remainder r).natDegree<9 := by
    apply Nat.lt_succ_of_le
    cases r <;> simp only [remainder,low] <;> compute_degree!
  have hs : C (endpoint r)+(C h-X)*quotient r=remainder r :=
    (r84_synthetic (remainder r) hdeg h).symm
  rw [remainder] at hs
  linear_combination (-1:ℚ[X])*hs

theorem endpoint_reserve (r : Bool) :
    (if r then 303/10000000 else 352/10000000)<endpoint r := by
  simp only [endpoint,remainder,eval_sub,eval_mul,eval_C,eval_X,eval_pow]
  cases r <;> simp only [low,eval_sub,eval_add,eval_mul,eval_C,eval_X,eval_pow] <;> norm_num [h]

theorem quotient_expansion (r : Bool) :
    quotient r=C ((quotient r).coeff 0)+C ((quotient r).coeff 1)*X+
      C ((quotient r).coeff 2)*X^2+C ((quotient r).coeff 3)*X^3+
        C ((quotient r).coeff 4)*X^4+C ((quotient r).coeff 5)*X^5+
          C ((quotient r).coeff 6)*X^6+C ((quotient r).coeff 7)*X^7 := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' (quotient r) (r84_quotient_natDegree r)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]

theorem quotient_coefficients (r : Bool) :
    cubic0 r<(quotient r).coeff 0 ∧ cubic1 r≤(quotient r).coeff 1 ∧
    cubic2 r≤(quotient r).coeff 2 ∧
    cubic3 r≤(quotient r).coeff 3+(quotient r).coeff 5*h^2+(quotient r).coeff 7*h^4 ∧
    0≤(quotient r).coeff 4 ∧ (quotient r).coeff 5≤0 ∧
    0≤(quotient r).coeff 6 ∧ (quotient r).coeff 7≤0 := by
  simp only [r84_quotient_coeff',Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,
    Nat.reduceLT,Nat.reduceSub,ite_true,ite_false,mul_zero,add_zero,zero_add]
  cases r
  · obtain ⟨e1,e2,e3,e4,e5,e6,e7,e8⟩ := r84_remainder_false
    rw [e1,e2,e3,e4,e5,e6,e7,e8]
    norm_num [cubic0,cubic1,cubic2,cubic3,h]
  · obtain ⟨e1,e2,e3,e4,e5,e6,e7,e8⟩ := r84_remainder_true
    rw [e1,e2,e3,e4,e5,e6,e7,e8]
    norm_num [cubic0,cubic1,cubic2,cubic3,h]

theorem cubic_reference (r : Bool) :
    valueLower r<(cubic r).eval (reference r) ∧
    |(cubic r).derivative.eval (reference r)|<slopeUpper r ∧
    curvature r<cubic2 r+cubic3 r*(h+2*reference r) ∧
    0<valueLower r-(slopeUpper r)^2/(4*curvature r) := by
  simp only [cubic,eval_add,eval_mul,eval_C,eval_X,eval_pow,derivative_add,derivative_mul,
    derivative_C,derivative_X,derivative_X_pow,zero_mul,zero_add,mul_one]
  cases r <;> norm_num [cubic0,cubic1,cubic2,cubic3,reference,valueLower,slopeUpper,
    curvature,h,abs_lt]

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.AxialPolynomial
