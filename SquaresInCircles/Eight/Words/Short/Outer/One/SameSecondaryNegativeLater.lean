module

public import Mathlib.Data.Int.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryDiagonalBound
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryPositiveZero

/-!
# Eight squares: negative halves of the second and third secondary owners

The strict target derivative sends each contact to the target diagonal or to the source diagonal
(`contact_lower`). Source slack is removed by its monotone label, and zero-source target slack
moves to contact. The original weak separator is kept in the concluding theorem `original`.
-/

section
/-!
## The axial polynomials for opposite edge five

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
end
end
end

section
/-!
## The earlier secondary target-diagonal arc

The exact third derivative is negative throughout the physical arc.
Its first derivative is concave and initially positive, so the cost
has its minimum at alignment or at the simultaneous-diagonal join.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.TargetDiagonal
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD ratioDD)
open Diagonal (joinContact joinSpeed)

def cost (r : Row) (x : ℝ) : ℝ := Negative.cost r outerDiagonal x
def first (r : Row) (x : ℝ) : ℝ := -1+slope r (joinContact x)*joinSpeed x
def second (r : Row) (x : ℝ) : ℝ :=
  P r*ratioD (joinContact x)*(joinSpeed x)^2+slope r (joinContact x)*(1/2-joinContact x)
def third (r : Row) (x : ℝ) : ℝ := joinSpeed x*
  (P r*ratioDD (joinContact x)*(joinSpeed x)^2+
    3*P r*ratioD (joinContact x)*(1/2-joinContact x)-slope r (joinContact x))

lemma joinSpeed_hasDerivAt (x : ℝ) : HasDerivAt joinSpeed (1/2-joinContact x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul (outerDiagonal-1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (outerDiagonal+1/2))
  convert h using 1
  · funext y; simp only [joinSpeed,Pi.add_apply]
  · simp only [joinContact]; ring

lemma source_range {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    joinContact x∈Icc b0 outerDiagonal := by
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (Diagonal.event_angle he).2⟩
  have hm := Diagonal.joinContact_strictMono.monotoneOn
  have hlo := hm (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx' hx.1
  have hhi := hm hx' (Diagonal.event_angle he) hx.2
  rw [he.2] at hhi
  norm_num [joinContact] at hlo
  exact ⟨by simp only [b0,joinContact]; linarith,hhi⟩

lemma domain {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    Negative.Domain outerDiagonal x := by
  have hb := source_range he hx
  refine ⟨⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩,
    ⟨hx.1,hx.2.trans (Diagonal.event_angle he).2⟩,?_⟩
  rw [diagonal_contact]
  exact ⟨b0_mem.1.trans hb.1,hb.2⟩

lemma speed_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<joinSpeed x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  simpa [Negative.speed,joinSpeed,SameContact.arc_diagonal] using
    Negative.speed_positive hdiag hx

lemma speed_circle (x : ℝ) :
    (joinSpeed x)^2+(joinContact x-1/2)^2=2*outerDiagonal^2+1/2 := by
  dsimp [joinSpeed,joinContact]
  linear_combination (2*outerDiagonal^2+1/2)*(Real.sin_sq_add_cos_sq x)

lemma speed_reserve {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    Q0/2≤(joinSpeed x)^2 := by
  have hb := source_range he hx
  have hdiag := diagonal_circle
  have hnonneg := mul_nonneg (show 0≤joinContact x-b0 by linarith [hb.1])
    (show 0≤outerDiagonal-joinContact x by linarith [hb.2])
  have hc := speed_circle x
  dsimp [b0] at hnonneg
  nlinarith

lemma cost_hasDerivAt (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (cost r) (first r x) x := by
  have hh := Negative.cost_angle_hasDerivAt r (domain he hx)
  show HasDerivAt (Negative.cost r outerDiagonal) _ x
  convert hh using 1
  simp only [first,Negative.first,Negative.speed,diagonal_contact,SameContact.arc_diagonal,
    joinSpeed]

lemma first_hasDerivAt (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (first r) (second r x) x := by
  have hb := (domain he hx).2.2
  rw [diagonal_contact] at hb
  have h := (((Secondary.slope_hasDerivAt r hb).comp x (Diagonal.joinContact_hasDerivAt x)).mul
    (joinSpeed_hasDerivAt x)).const_add (-1)
  convert h using 1
  · rfl
  · simp only [second,Function.comp_apply]; ring

lemma second_hasDerivAt (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (second r) (third r x) x := by
  have hb := (domain he hx).2.2
  rw [diagonal_contact] at hb
  have h := ((((SameContact.ratioD_hasDerivAt (SameContact.outer_domain hb)).comp x
    (Diagonal.joinContact_hasDerivAt x)).const_mul (P r)).mul
      ((joinSpeed_hasDerivAt x).pow 2)).add
        (((Secondary.slope_hasDerivAt r hb).comp x (Diagonal.joinContact_hasDerivAt x)).mul
          ((Diagonal.joinContact_hasDerivAt x).const_sub (1/2)))
  convert h using 1
  · funext y
    simp only [second,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
  · simp only [third,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one,Function.comp_apply,
      Pi.pow_apply]; ring

lemma third_negative (r : Row) {e x : ℝ} (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) :
    third r x<0 := by
  let b := joinContact x
  have hb : b∈Icc 0 outerDiagonal := by
    simpa [b,diagonal_contact] using (domain he hx).2.2
  have hs := speed_positive (domain he hx).2.1
  have hl := (Secondary.slope_bounds r hb).1
  have hP := (coefficient_bounds r).2.2.2.2.1
  have hr := SameContact.ratioD_pos (SameContact.outer_domain hb)
  have hrr := SecondWord.ratioDD_positive hb
  have hsum : P r*ratioDD b*(joinSpeed x)^2+
      3*P r*ratioD b*(1/2-b)≤0 := by
    by_cases hsmall : b≤1/2
    · have hfirst := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hP hrr.le) (sq_nonneg (joinSpeed x))
      have hsecond := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (show 3*P r≤0 by linarith) hr.le)
        (show 0≤1/2-b by linarith)
      linarith
    · have hbhalf : 1/2≤b := le_of_not_ge hsmall
      have hu := SecondWord.U_positive (SameContact.outer_domain hb)
      have hc := SecondWord.UW_circle (SameContact.outer_domain hb)
      have hU2 : (SecondWord.U b)^2≤Q0-1 := by
        dsimp [SecondWord.W] at hc
        nlinarith
      have hleft : Q0/2≤(b+1/2)*(joinSpeed x)^2 := by
        have hm := mul_nonneg (show 0≤b-1/2 by linarith) (sq_nonneg (joinSpeed x))
        nlinarith [speed_reserve he hx]
      have hright : (b-1/2)*(SecondWord.U b)^2≤(2/5:ℝ)*(Q0-1) := by
        have hm := mul_le_mul (show b-1/2≤(2/5:ℝ) by
          linarith [hb.2,outer_endpoint_bounds.2.2.2]) hU2 (sq_nonneg _) (by norm_num)
        exact hm
      have hgeom : (b-1/2)*(SecondWord.U b)^2≤(b+1/2)*(joinSpeed x)^2 := by
        norm_num [Q0] at hleft hright ⊢
        linarith
      have hid : ratioDD b*(SecondWord.U b)^2=3*(b+1/2)*ratioD b := by
        rw [SecondWord.ratioDD_formula hb]
        dsimp [SecondWord.W]
        field_simp [hu.ne']
      have hmul := mul_le_mul_of_nonneg_left hgeom (show 0≤3*ratioD b by positivity)
      have hcomp : 3*ratioD b*(b-1/2)≤ratioDD b*(joinSpeed x)^2 := by
        have hUpos := sq_pos_of_pos hu
        refine le_of_mul_le_mul_right ?_ hUpos
        calc
          (3*ratioD b*(b-1/2))*(SecondWord.U b)^2 =
              (3*ratioD b)*((b-1/2)*(SecondWord.U b)^2) := by ring
          _ ≤ (3*ratioD b)*((b+1/2)*(joinSpeed x)^2) := hmul
          _ = (ratioDD b*(joinSpeed x)^2)*(SecondWord.U b)^2 := by
            linear_combination -(joinSpeed x)^2*hid
      have hnegative := mul_nonpos_of_nonpos_of_nonneg hP
        (sub_nonneg.mpr hcomp)
      nlinarith only [hnegative]
  have hinside : P r*ratioDD b*(joinSpeed x)^2+
      3*P r*ratioD b*(1/2-b)-slope r b<0 := by linarith
  exact mul_neg_of_pos_of_neg hs hinside

lemma initial_first (r : Row) (hr : r=1 ∨ r=2) : (17/250:ℝ)<first r 0 := by
  have hrat : ratio b0<(319/1000:ℝ) := by
    simpa [b0,ShortOuterZero.Opposite.low] using ShortOuterZero.Opposite.low_ratio
  have hratioPos := SameContact.ratio_pos (SameContact.outer_domain b0_mem)
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hcontact : joinContact 0=b0 := by norm_num [joinContact,b0]; ring
  have hspeed : joinSpeed 0=outerDiagonal+1/2 := by norm_num [joinSpeed]
  rw [first,hcontact,hspeed]
  have hl : (1527/2000:ℝ)<slope r b0 := by
    rcases hr with rfl | rfl <;> norm_num [slope,t,P] <;> linarith
  have hp := mul_lt_mul_of_pos_left
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith) (show 0<slope r b0 by linarith)
  nlinarith

lemma initial_cost (r : Row) : cost r 0=aligned r b0 := by
  have hcontact : Negative.contact outerDiagonal 0=b0 := by
    norm_num [Negative.contact,SameContact.arc_diagonal,b0]; ring
  dsimp [cost,Negative.cost]
  rw [hcontact,targetCost,SameContact.arc_diagonal]
  have hb : 1-b0=outerDiagonal := by dsimp [b0]; ring
  dsimp [aligned,source]
  rw [hb,SameContact.arc_diagonal]
  ring

lemma join_cost (r : Row) {e : ℝ} (he : Diagonal.IsEvent e) :
    cost r e=SourceDiagonal.cost r e := by
  have hc := SourceDiagonal.event_coordinates he
  dsimp [cost,Negative.cost,SourceDiagonal.cost]
  rw [diagonal_contact,he.2,target,targetCost,SameContact.arc_diagonal,hc.1,hc.2]
  ring

theorem cost_lower (r : Row) (hr : r=1 ∨ r=2) {e x : ℝ}
    (he : Diagonal.IsEvent e) (hx : x∈Icc 0 e) : (8981/10000:ℝ)<cost r x := by
  have hc : ConcaveOn ℝ (Icc 0 e) (first r) := concave_of_deriv2
    (fun y hy => first_hasDerivAt r he hy)
    (fun y hy => second_hasDerivAt r he hy)
    (fun y hy => (third_negative r he hy).le)
  have hm := RoleFour.minimum_of_concave_derivative
    (fun y hy => cost_hasDerivAt r he hy) hc (by linarith [initial_first r hr]) hx
  have hl : (8981/10000:ℝ)<cost r 0 := by
    rw [initial_cost]
    exact aligned_lower r ⟨b0_mem.1,le_rfl⟩
  have hu : (8981/10000:ℝ)<cost r e := by
    rw [join_cost r he]
    exact SourceDiagonal.cost_lower r hr he ⟨le_rfl,(Diagonal.event_angle he).2⟩
  exact (lt_min hl hu).trans_le hm

theorem original_contact (r : Row) (hr : r=1 ∨ r=2) {x : ℝ}
    (hd : Negative.Domain outerDiagonal x) : (8981/10000:ℝ)<Negative.cost r outerDiagonal x := by
  obtain ⟨e,he⟩ := Diagonal.exists_event
  have hbefore : x≤e := by
    by_contra! hbad
    have hh := Diagonal.joinContact_strictMono (Diagonal.event_angle he) hd.2.1 hbad
    rw [he.2,←diagonal_contact] at hh
    linarith [hd.2.2.2]
  exact cost_lower r hr he ⟨hd.2.1.1,hbefore⟩

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.TargetDiagonal
end
end
end

section
/-!
## Decreasing target cost on both later-row contact domains

The target ratio is extended continuously to the diagonal ratio one. A single positive derivative
controls that extension. At its endpoint a quadratic and its exact discriminant give the strict
target descent for rows two and three (`target_negative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.TargetRatio
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)
open SecondWord (U W)

def M : ℝ := 383/200
def root (w : ℝ) : ℝ := Real.sqrt (1+w^2)
def curveU (w : ℝ) : ℝ := Real.sqrt Q0/root w
def v (w x : ℝ) : ℝ := 1+Real.cos x+curveU w*(w*Real.sin x-Real.cos x)
def X (w x : ℝ) : ℝ := Real.sin x+w*Real.cos x
def E (r : Row) (w x : ℝ) : ℝ := (t r+P r*v w x/M)*X w x-p r*w-q r
def ED (r : Row) (w x : ℝ) : ℝ :=
  t r*Real.cos x-p r+(P r/M)*(Real.cos x*v w x+curveU w*(X w x)^2/(1+w^2))
def z (r : Row) : ℝ := -P r/M
def c0 (r : Row) : ℝ := t r-(3/5)*z r-p r-q r
def c1 (r : Row) : ℝ := t r-(441/250)*z r
def c2 (r : Row) : ℝ := t r/2+(13/10)*z r
def polynomial (r : Row) (s : ℝ) : ℝ := c0 r+c1 r*s-c2 r*s^2

lemma root_positive (w : ℝ) : 0<root w := Real.sqrt_pos.mpr (by positivity)
lemma root_sq (w : ℝ) : (root w)^2=1+w^2 := Real.sq_sqrt (by positivity)
lemma curveU_positive (w : ℝ) : 0<curveU w :=
  div_pos (Real.sqrt_pos.mpr (by norm_num [Q0])) (root_positive w)

lemma curveU_circle (w : ℝ) : (curveU w)^2*(1+w^2)=Q0 := by
  have hr := root_sq w
  have hR := Real.sq_sqrt (show 0≤Q0 by norm_num [Q0])
  dsimp [curveU]
  rw [←hr,div_pow]
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (root_positive w).ne')]
  exact hR

lemma curveU_upper {w : ℝ} (hw : w∈Icc (261/1000:ℝ) 1) : curveU w<M := by
  have hc := curveU_circle w
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤261/1000) hw.1 2
  have hp := mul_le_mul_of_nonneg_left hsq (sq_nonneg (curveU w))
  norm_num [Q0,M] at *
  nlinarith [curveU_positive w]

lemma curveU_one : curveU 1=outerDiagonal+1/2 := by
  have hc := curveU_circle 1
  norm_num at hc
  nlinarith [diagonal_circle,curveU_positive 1,outer_endpoint_bounds.2.2.1]

lemma root_hasDerivAt (w : ℝ) : HasDerivAt root (w/root w) w := by
  have h := (((hasDerivAt_id w).pow 2).const_add 1).sqrt (show (1+w^2:ℝ)≠0 by positivity)
  convert h using 1
  · rfl
  change w/root w=((2:ℕ):ℝ)*w^(2-1)*1/(2*root w)
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one,mul_one]
  rw [mul_div_mul_left _ _ two_ne_zero]

lemma curveU_hasDerivAt (w : ℝ) :
    HasDerivAt curveU (-curveU w*w/(1+w^2)) w := by
  have hp := root_positive w
  have hr := root_sq w
  convert (hasDerivAt_const w (Real.sqrt Q0)).div (root_hasDerivAt w) hp.ne' using 1
  · rfl
  · dsimp [curveU]
    field_simp [hp.ne',show (1+w^2:ℝ)≠0 by positivity]
    nlinarith only [congrArg (fun y : ℝ => Real.sqrt Q0*w*y) hr]

lemma v_hasDerivAt (w x : ℝ) :
    HasDerivAt (fun w => v w x) (curveU w*X w x/(1+w^2)) w := by
  convert ((curveU_hasDerivAt w).mul
    (((hasDerivAt_id w).mul_const (Real.sin x)).sub_const (Real.cos x))).const_add
      (1+Real.cos x) using 1
  · rfl
  · dsimp [X]
    field_simp [show (1+w^2:ℝ)≠0 by positivity]
    ring

lemma X_positive {w x : ℝ} (hw : w∈Icc (261/1000:ℝ) 1) (hx : x∈Icc 0 (7/10)) :
    0<X w x := by
  have ht := positive_trig hx
  have hp := mul_pos (show 0<w by linarith [hw.1]) (show 0<Real.cos x by linarith [ht.1])
  dsimp [X]
  linarith [ht.2.2.1]

lemma v_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun w => v w x) (Icc (261/1000:ℝ) 1) := monoOn_of_hasDeriv_nonneg
  (fun w _ => (v_hasDerivAt w x).continuousAt.continuousWithinAt)
  (fun w _ => v_hasDerivAt w x)
  (fun w hw => (div_pos (mul_pos (curveU_positive w)
    (X_positive (Ioo_subset_Icc_self hw) hx)) (by positivity)).le)

lemma v_one (x : ℝ) :
    v 1 x=1-(outerDiagonal-1/2)*Real.cos x+(outerDiagonal+1/2)*Real.sin x := by
  rw [v,curveU_one]
  ring

lemma v_upper {w x : ℝ} (hw : w∈Icc (261/1000:ℝ) 1) (hx : x∈Icc 0 (7/10)) :
    v w x<(8/5:ℝ) := by
  have hm := v_monotone hx hw (show (1:ℝ)∈Icc (261/1000) 1 by norm_num) hw.2
  beta_reduce at hm
  rw [v_one] at hm
  have ht := positive_trig hx
  have hneg := mul_le_mul
    (show (399/1000:ℝ)≤outerDiagonal-1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
  have hpos := mul_le_mul
    (show outerDiagonal+1/2≤(7/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    (show Real.sin x≤(129/200:ℝ) by linarith [ht.2.2.2.1]) ht.2.2.1 (by norm_num)
  nlinarith

lemma X_square (w x : ℝ) : (X w x)^2≤1+w^2 := by
  have hs := sq_nonneg (Real.cos x-w*Real.sin x)
  have he : (X w x)^2+(Real.cos x-w*Real.sin x)^2=1+w^2 := by
    dsimp [X]
    linear_combination (1+w^2)*(Real.sin_sq_add_cos_sq x)
  linarith

lemma E_hasDerivAt (r : Row) (w x : ℝ) : HasDerivAt (fun w => E r w x) (ED r w x) w := by
  have hX : HasDerivAt (fun w => X w x) (Real.cos x) w := by
    have h := ((hasDerivAt_id w).mul_const (Real.cos x)).const_add (Real.sin x)
    rw [one_mul] at h
    exact h
  convert ((((((v_hasDerivAt w x).const_mul (P r)).div_const M).const_add (t r)).mul hX).sub
    ((hasDerivAt_id w).const_mul (p r))).sub_const (q r) using 1
  · rfl
  · dsimp [ED]
    field_simp [show M≠0 by norm_num [M],show (1+w^2:ℝ)≠0 by positivity]
    ring

lemma E_derivative (r : Row) (hr : r=1 ∨ r=2) {w x : ℝ}
    (hw : w∈Icc (261/1000:ℝ) 1) (hx : x∈Icc 0 (7/10)) : (1/25:ℝ)<ED r w x := by
  have ht := positive_trig hx
  have hcu := curveU_upper hw
  have hv := v_upper hw hx
  have hproj := mul_le_mul_of_nonneg_left hv.le (show 0≤Real.cos x by linarith [ht.1])
  have hcos : Real.cos x*v w x≤(8/5:ℝ) := by nlinarith [ht.2.1]
  have hterm : curveU w*(X w x)^2/(1+w^2)≤curveU w := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<1+w^2)).2
    exact mul_le_mul_of_nonneg_left (X_square w x) (curveU_positive w).le
  have hbrace : Real.cos x*v w x+curveU w*(X w x)^2/(1+w^2)<(703/200:ℝ) := by
    dsimp [M] at hcu
    linarith
  rcases hr with rfl | rfl <;> norm_num [ED,M,t,p,P] <;> linarith [ht.1]

lemma E_monotone (r : Row) (hr : r=1 ∨ r=2) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun w => E r w x) (Icc (261/1000:ℝ) 1) := monoOn_of_hasDeriv_nonneg
  (fun w _ => (E_hasDerivAt r w x).continuousAt.continuousWithinAt)
  (fun w _ => E_hasDerivAt r w x)
  (fun w hw => by linarith [E_derivative r hr (Ioo_subset_Icc_self hw) hx])

lemma v_one_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    1-(2/5)*Real.cos x+(7/5)*Real.sin x≤v 1 x := by
  have ht := positive_trig hx
  have hp := mul_nonneg
    (show 0≤9/10-outerDiagonal by linarith [outer_endpoint_bounds.2.2.2])
    (show 0≤Real.cos x-Real.sin x by linarith [ht.1,ht.2.2.2.1])
  rw [v_one]
  nlinarith

lemma polynomial_upper (r : Row) (hr : r=1 ∨ r=2) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    E r 1 x≤polynomial r (Real.sin x) := by
  have ht := positive_trig hx
  have htrig := Real.sin_sq_add_cos_sq x
  have hz : 0<z r ∧ 0<t r-z r := by rcases hr with rfl | rfl <;> norm_num [z,M,P,t]
  have hsum : 0≤Real.cos x+Real.sin x := by linarith [ht.1,ht.2.2.1]
  have hv := mul_le_mul_of_nonneg_left (v_one_lower hx) (mul_nonneg hz.1.le hsum)
  have hcos : Real.cos x≤1-(Real.sin x)^2/2 := by
    nlinarith [sq_nonneg (1-Real.cos x)]
  have hlinear := mul_le_mul_of_nonneg_left hcos hz.2.le
  have hnegative := mul_le_mul_of_nonneg_left
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (mul_nonneg hz.1.le ht.2.2.1)
  rcases hr with rfl | rfl <;>
    norm_num [E,X,polynomial,c0,c1,c2,z,M,t,p,q,P] at * <;> nlinarith

lemma discriminant (r : Row) (hr : r=1 ∨ r=2) :
    0<c2 r ∧ (43/5000:ℝ)<4*c2 r*(-c0 r)-(c1 r)^2 := by
  rcases hr with rfl | rfl <;> norm_num [c0,c1,c2,z,M,t,p,q,P]

lemma polynomial_negative (r : Row) (hr : r=1 ∨ r=2) (s : ℝ) : polynomial r s<0 := by
  have hd := discriminant r hr
  have hs := sq_nonneg (2*c2 r*s-c1 r)
  have he : 4*c2 r*polynomial r s=
      4*c2 r*c0 r+(c1 r)^2-(2*c2 r*s-c1 r)^2 := by dsimp [polynomial]; ring
  have hn : 4*c2 r*polynomial r s<0 := by nlinarith
  by_contra! hnonneg
  have hh := mul_nonneg (show 0≤4*c2 r by linarith [hd.1]) hnonneg
  linarith

lemma endpoint_negative (r : Row) (hr : r=1 ∨ r=2) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    E r 1 x<0 := (polynomial_upper r hr hx).trans_lt (polynomial_negative r hr (Real.sin x))

lemma actual_curveU {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : curveU (ratio B)=U B := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hB)
  have hc := SecondWord.UW_circle (SecondWord.outer_domain hB)
  have ha : (U B)^2*(1+(ratio B)^2)=Q0 := by
    have h1 : U B*ratio B=W B := mul_div_cancel₀ _ hU.ne'
    rw [←hc]
    linear_combination (U B*ratio B+W B)*h1
  have hh := curveU_circle (ratio B)
  have he : ((curveU (ratio B))^2-(U B)^2)*(1+(ratio B)^2)=0 := by nlinarith only [ha,hh]
  have hs : (curveU (ratio B))^2=(U B)^2 := by
    rcases mul_eq_zero.mp he with he | he
    · linarith
    · exact False.elim ((show (1+(ratio B)^2:ℝ)≠0 by positivity) he)
  nlinarith [curveU_positive (ratio B)]

lemma actual_v {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) : v (ratio B) x=contact B x+1/2 := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hB)
  have h1 : U B*ratio B=W B := mul_div_cancel₀ _ hU.ne'
  rw [v,actual_curveU hB]
  simp only [contact,U,W] at h1 ⊢
  linear_combination Real.sin x*h1

lemma original_upper (r : Row) {B x : ℝ} (hd : Domain B x) : targetFirst r B x≤E r (ratio B) x := by
  have hsource := outer_bounds (SameContact.arc_state hd.2.2)
  have hU := SecondWord.U_positive (SecondWord.outer_domain hd.2.2)
  have hupper : U (contact B x)≤M := by
    dsimp [U,M]
    linarith [hsource.2.1,ShortOuterZero.fine_axial_bounds.2]
  have hratio : (contact B x+1/2)/M≤ratio (contact B x) := by
    change (contact B x+1/2)/M≤(contact B x+1/2)/U (contact B x)
    apply (le_div_iff₀ hU).2
    have hh := mul_le_mul_of_nonneg_left hupper
      (show 0≤(contact B x+1/2)/M by dsimp [M]; linarith [hd.2.2.1])
    dsimp [M] at *
    nlinarith
  have hl := mul_le_mul_of_nonpos_left hratio (coefficient_bounds r).2.2.2.2.1
  have hk := K_positive hd.1 hd.2.1
  have hp := mul_le_mul_of_nonneg_right
    (show slope r (contact B x)≤t r+P r*(contact B x+1/2)/M by
      dsimp [slope]; rw [mul_div_assoc]; linarith only [hl]) hk.le
  rw [E,actual_v hd.1]
  dsimp [targetFirst,targetSlope,K,X] at *
  nlinarith only [hp]

/-- The physical target derivative is negative on the whole domain for the two later rows; the
source ratio and the target circle are kept. -/
theorem target_negative (r : Row) (hr : r=1 ∨ r=2) {B x : ℝ} (hd : Domain B x) :
    targetFirst r B x<0 := by
  have hratio := SecondWord.outer_ratio_bounds hd.1
  have hw : ratio B∈Icc (261/1000:ℝ) 1 := ⟨hratio.1.le,hratio.2.1⟩
  have hm := E_monotone r hr hd.2.1 hw (show (1:ℝ)∈Icc (261/1000) 1 by norm_num) hw.2
  exact (original_upper r hd).trans_lt (hm.trans_lt (endpoint_negative r hr hd.2.1))

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.TargetRatio
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.Later
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

lemma interval_domain {B C D x : ℝ} (hB : Domain B x) (hC : Domain C x)
    (hD : D∈Icc B C) : Domain D x := by
  have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.1.trans hD.1,hD.2.trans hC.1.2⟩
  have hmono := contact_target_monotone hB.2.1
  exact ⟨hDouter,hB.2.1,
    ⟨hB.2.2.1.trans (hmono hB.1 hDouter hD.1),
      (hmono hDouter hC.1 hD.2).trans hC.2.2.2⟩⟩

lemma target_motion (r : Row) (hr : r=1 ∨ r=2) {B C x : ℝ}
    (hB : Domain B x) (hC : Domain C x) (hBC : B≤C) : cost r C x≤cost r B x := by
  have ha : AntitoneOn (fun D => cost r D x) (Icc B C) := antiOn_of_hasDeriv_nonpos
    (fun D hD => (cost_target_hasDerivAt r (interval_domain hB hC hD)).continuousAt.continuousWithinAt)
    (fun D hD => cost_target_hasDerivAt r (interval_domain hB hC (Ioo_subset_Icc_self hD)))
    (fun D hD => (TargetRatio.target_negative r hr
      (interval_domain hB hC (Ioo_subset_Icc_self hD))).le)
  exact ha ⟨le_rfl,hBC⟩ ⟨hBC,le_rfl⟩ hBC

theorem contact_lower (r : Row) (hr : r=1 ∨ r=2) {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<cost r B x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  by_cases hfits : contact outerDiagonal x≤outerDiagonal
  · have hD : Domain outerDiagonal x :=
      ⟨hdiag,hd.2.1,⟨(diagonal_contact_positive hd.2.1).le,hfits⟩⟩
    exact (TargetDiagonal.original_contact r hr hD).trans_le (target_motion r hr hd hD hd.1.2)
  · have hc : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hd.1.2 hc.continuousOn
      (show outerDiagonal∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨hd.2.2.2,le_of_not_ge hfits⟩)
    beta_reduce at he
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hd.1.1.trans hD.1,hD.2⟩
    have hDD : Domain D x := ⟨hDouter,hd.2.1,by rw [he]; exact hdiag⟩
    have hsource := SourceDiagonal.original_contact r hr (SameContact.arc_state hDouter)
      hd.2.1 (by simpa [contact] using he)
    have hbound : (8981/10000:ℝ)<cost r D x := by
      dsimp [cost]
      rw [he,target,SameContact.arc_diagonal,targetCost]
      linarith
    exact hbound.trans_le (target_motion r hr hd hDD hD.1)

theorem original (r : Row) (hr : r=1 ∨ r=2) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (8981/10000:ℝ)<Real.pi/2-x+c r-P r*a+t r*b+p r*A-q r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hrequired : contact B x≤b := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2-x+c r+target r b+targetCost r B=
      Real.pi/2-x+c r-P r*a+t r*b+p r*A-q r*B := by
    have hh := Secondary.original_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : 0≤contact B x
  · have hd : Domain B x := ⟨hB,hx,⟨hactive,hrequired.trans hb.2⟩⟩
    have hsource := target_monotone r hd.2.2 hb hrequired
    have hh := contact_lower r hr hd
    dsimp [cost] at hh
    linarith
  · have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
    have hc : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hB.2 hc.continuousOn
      (show (0:ℝ)∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨by linarith,(diagonal_contact_positive hx).le⟩)
    beta_reduce at he
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have htarget := targetCost_antitone r hB hDouter hD.1
    have hsource := target_monotone r (show (0:ℝ)∈Icc 0 outerDiagonal from
      ⟨le_rfl,hdiag.1⟩) hb hb.1
    have hh := contact_lower r hr (show Domain D x from
      ⟨hDouter,hx,by rw [he]; exact ⟨le_rfl,hdiag.1⟩⟩)
    dsimp [cost] at hh
    rw [he] at hh
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.Later
end
end
end
