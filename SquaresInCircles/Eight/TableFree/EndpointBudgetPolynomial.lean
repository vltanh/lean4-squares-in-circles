module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# One whole-interval polynomial for the narrow endpoint budget

Uncompiled source draft.  This is a direct squared version of the
H/D endpoint-circle comparison on `0≤α≤1/2`.  Its polynomial is formed
from the degree-five sine upper bound, degree-six cosine lower bound,
and exact rational upper bounds for the two original radius radicals.
Expansion at `31/200` gives a positive quadratic lower bound on the
entire interval.  No angle rows or sampled acceptance values occur.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.EndpointBudgetPolynomial
open Polynomial

def kbar : ℚ := 914576/1000000
def sbar : ℚ := 415026/1000000
def reserve : ℚ := 1/8000
def center : ℚ := 31/200
def span : ℚ := 69/200

def S5 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def C6 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6
def primary : ℚ[X] := C (3/2)-C (1/2)*(C kbar*S5+C (1/2)*(1-C6))
def transverse : ℚ[X] := C ((3-sbar-reserve)/2)+C (25/49)*X
def certificate : ℚ[X] := primary^2+transverse^2-C (9789/2500)
def shifted : ℚ[X] := certificate.comp (C center+X)
def remainder : ℚ[X] :=
  ∑ j : Fin 10,C (shifted.coeff (j.val+3))*X^(j.val+3)

/-! Exact rational coefficient lists: `r23ev l` is the polynomial with coefficient list `l`;
sums and products of lists are computed by the kernel. -/
private def r23ev : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a + X * r23ev l

private def r23add : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a+b) :: r23add l m

private def r23smul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: r23smul c l

private def r23mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => r23add (r23smul a m) (0 :: r23mul l m)

private def r23sub (l m : List ℚ) : List ℚ := r23add l (r23smul (-1) m)

private theorem r23ev_add (l m : List ℚ) : r23ev (r23add l m)=r23ev l+r23ev m := by
  induction l generalizing m with
  | nil => simp [r23add,r23ev]
  | cons a l ih =>
    cases m with
    | nil => simp [r23add,r23ev]
    | cons b m => simp only [r23add,r23ev,ih,map_add]; ring

private theorem r23ev_smul (c : ℚ) (l : List ℚ) : r23ev (r23smul c l)=C c*r23ev l := by
  induction l with
  | nil => simp [r23smul,r23ev]
  | cons a l ih => simp only [r23smul,r23ev,ih,map_mul]; ring

private theorem r23ev_mul (l m : List ℚ) : r23ev (r23mul l m)=r23ev l*r23ev m := by
  induction l with
  | nil => simp [r23mul,r23ev]
  | cons a l ih => simp only [r23mul,r23ev,r23ev_add,r23ev_smul,ih,map_zero]; ring

private theorem r23ev_sub (l m : List ℚ) : r23ev (r23sub l m)=r23ev l-r23ev m := by
  simp only [r23sub,r23ev_add,r23ev_smul,map_neg,map_one]; ring

private theorem r23ev_single (a : ℚ) : r23ev [a]=C a := by simp [r23ev]

private theorem r23ev_X : r23ev [0,1]=X := by simp [r23ev]

private theorem r23_coeff (l : List ℚ) (n : ℕ) : (r23ev l).coeff n=l.getD n 0 := by
  induction l generalizing n with
  | nil => simp [r23ev]
  | cons a l ih =>
    cases n with
    | zero => simp [r23ev]
    | succ n => simp [r23ev,ih]

private theorem r23_natDegree (l : List ℚ) (n : ℕ) (h : l.length≤n+1) :
    (r23ev l).natDegree≤n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [r23_coeff,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)]
  rfl

private def r23comp : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, q => r23add [a] (r23mul (r23comp l q) q)

private theorem r23ev_comp (l q : List ℚ) : r23ev (r23comp l q)=(r23ev l).comp (r23ev q) := by
  induction l with
  | nil => simp [r23comp,r23ev]
  | cons a l ih =>
    simp only [r23comp,r23ev_add,r23ev_mul,ih,r23ev,add_comp,mul_comp,C_comp,X_comp,mul_zero,
      add_zero]
    ring

private def r23S5L : List ℚ := [0,1,0,-(1/6),0,1/120]
private def r23C6L : List ℚ := [1,0,-(1/2),0,1/24,0,-(1/720)]
private def r23primaryL : List ℚ :=
  r23sub [3/2] (r23smul (1/2) (r23add (r23smul kbar r23S5L) (r23smul (1/2) (r23sub [1] r23C6L))))
private def r23transverseL : List ℚ := [(3-sbar-reserve)/2,25/49]
private def r23certL : List ℚ :=
  r23sub (r23add (r23mul r23primaryL r23primaryL) (r23mul r23transverseL r23transverseL))
    [9789/2500]

/-- The exact coefficients of `shifted`, from degree `0` to degree `12`. -/
private def r23Sval : List ℚ :=
  [(2077210500683914241291060856060733642321/31863767040000000000000000000000000000000000),
      (139823037340314387780167163837433879/295034880000000000000000000000000000000),
      (2205441626495707709914549793579833693/8851046400000000000000000000000000000),
      (26515140684396729980671007908961/82944000000000000000000000000000),
      -(9482908839149717246286710837/184320000000000000000000000000),
      -(19242951779055197993729239/576000000000000000000000000),
      (29200689169224892408081/3456000000000000000000000),
      (6535555128412378237/2880000000000000000000),
      -(64580872447222469/115200000000000000000),
      -(152183206879687/1296000000000000000),
      (86335758097/7200000000000000),
      (82673/28800000000),
      (1/8294400)]

private theorem r23SL_val : r23comp r23certL [center,1]=r23Sval := by decide +kernel

private theorem r23S5 : S5=r23ev r23S5L := by
  simp only [S5,r23S5L,r23ev,map_neg,map_zero,map_one]; ring
private theorem r23C6 : C6=r23ev r23C6L := by
  simp only [C6,r23C6L,r23ev,map_neg,map_zero,map_one]; ring
private theorem r23transverse : transverse=r23ev r23transverseL := by
  simp only [transverse,r23transverseL,r23ev]; ring

private theorem r23S_ev : shifted=r23ev r23Sval := by
  rw [← r23SL_val,r23ev_comp]
  simp only [r23certL,r23primaryL,r23ev_add,r23ev_sub,r23ev_mul,r23ev_smul,r23ev_single,map_one,
    ← r23S5,← r23C6,← r23transverse]
  simp only [shifted,certificate,primary,r23ev,map_one,mul_one,mul_zero,add_zero]
  congr 1
  ring

theorem expansion_identity :
    shifted=C (shifted.coeff 0)+C (shifted.coeff 1)*X+
      C (shifted.coeff 2)*X^2+remainder := by
  have hdeg : shifted.natDegree<13 := by
    rw [r23S_ev]
    exact Nat.lt_succ_of_le (r23_natDegree _ 12 (by rfl))
  conv_lhs => rw [as_sum_range_C_mul_X_pow' shifted hdeg]
  rw [show (13:ℕ)=3+10 from rfl,Finset.sum_range_add,remainder,
    Fin.sum_univ_eq_sum_range (fun j => C (shifted.coeff (j+3))*X^(j+3)) 10]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,mul_one,zero_add]

theorem coefficient_reserves :
    (1/20000 : ℚ)<shifted.coeff 0 ∧
      |shifted.coeff 1|<1/2000 ∧
      (1/8 : ℚ)<shifted.coeff 2-
        ∑ j : Fin 10,|shifted.coeff (j.val+3)| *span^(j.val+1) := by
  rw [r23S_ev]
  simp only [r23_coeff]
  decide +kernel

/-- The tail estimate is a coefficient norm for one continuous interval.
Its sign-independent remainder is charged only against the quadratic. -/
theorem shifted_positive {x : ℝ} (hx : |x|≤(span:ℝ)) :
    0<aeval x shifted := by
  have hspan : (0:ℝ)≤(span:ℝ) := by norm_num [span]
  have hterm (j : Fin 10) :
      -|(shifted.coeff (j.val+3):ℝ)| *(span:ℝ)^(j.val+1)*x^2≤
        (shifted.coeff (j.val+3):ℝ)*x^(j.val+3) := by
    have hpow : |x^(j.val+1)|≤(span:ℝ)^(j.val+1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx _
    have hm := mul_le_mul_of_nonneg_left hpow
      (abs_nonneg (shifted.coeff (j.val+3):ℝ))
    rw [← abs_mul] at hm
    have hlo := (abs_le.mp hm).1
    have hmul := mul_le_mul_of_nonneg_right hlo (sq_nonneg x)
    have he : (shifted.coeff (j.val+3):ℝ)*x^(j.val+3)=
        ((shifted.coeff (j.val+3):ℝ)*x^(j.val+1))*x^2 := by
      rw [show j.val+3=(j.val+1)+2 by omega,pow_add]
      ring
    rw [he]
    linarith
  have htail := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  have htail' :
      -(∑ j : Fin 10,|(shifted.coeff (j.val+3):ℝ)| *(span:ℝ)^(j.val+1))*x^2≤
        aeval x remainder := by
    simp only [remainder,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
    simpa only [neg_mul,Finset.sum_neg_distrib,Finset.sum_mul] using htail
  have hc0 : (1/20000 : ℝ)<(shifted.coeff 0:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.1
    push_cast at h
    exact h
  have hc1 : |(shifted.coeff 1:ℝ)|<1/2000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.2.1
    push_cast at h
    exact h
  have hc2 : (1/8 : ℝ)<(shifted.coeff 2:ℝ)-
      ∑ j : Fin 10,|(shifted.coeff (j.val+3):ℝ)| *(span:ℝ)^(j.val+1) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.2.2
    push_cast at h
    exact h
  have hlinear : -(1/2000)*|x|≤(shifted.coeff 1:ℝ)*x := by
    have hm := mul_le_mul_of_nonneg_right hc1.le (abs_nonneg x)
    rw [← abs_mul] at hm
    rw [neg_mul]
    exact (abs_le.mp hm).1
  have hquadratic := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg x)
  have he := congrArg (fun p : ℚ[X] => aeval x p) expansion_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hsq := sq_nonneg (|x|-(1/500 : ℝ))
  nlinarith [sq_abs x]

theorem certificate_positive {a : ℝ} (ha : a∈Set.Icc 0 (1/2 : ℝ)) :
    0<aeval a certificate := by
  have hx : |a-(center:ℝ)|≤(span:ℝ) := by
    rw [abs_le]
    norm_num [center,span]
    constructor <;> linarith [ha.1,ha.2]
  have h := shifted_positive hx
  have he : aeval (a-(center:ℝ)) shifted=aeval a certificate := by
    have harg : aeval (a-(center:ℝ)) (C center+X)=a := by
      simp
    rw [shifted,aeval_comp]
    rw [harg]
  rw [he] at h
  exact h

@[simp] theorem primary_eval (a : ℝ) :
    aeval a primary=3/2-
      ((kbar:ℝ)*(a-a^3/6+a^5/120)+(1-(1-a^2/2+a^4/24-a^6/720))/2)/2 := by
  simp [primary,S5,C6]
  ring

@[simp] theorem transverse_eval (a : ℝ) :
    aeval a transverse=((3:ℝ)-(sbar:ℝ)-(reserve:ℝ))/2+(25/49)*a := by
  simp [transverse]

theorem real_certificate_positive {a : ℝ} (ha : a∈Set.Icc 0 (1/2 : ℝ)) :
    (aeval a primary)^2+
      (((3:ℝ)-(sbar:ℝ)-(reserve:ℝ))/2+(25/49)*a)^2>(9789/2500 : ℝ) := by
  have h := certificate_positive ha
  simp only [certificate,map_sub,map_add,map_pow,aeval_C,transverse_eval,eq_ratCast] at h
  have h9 : ((9789/2500:ℚ):ℝ)=9789/2500 := by norm_num
  rw [h9] at h
  linarith

end SquaresInCircles.Eight.TableFree.EndpointBudgetPolynomial
