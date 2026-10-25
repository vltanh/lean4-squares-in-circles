module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.Varying.BCertificate

/-!
# Eight squares: the single polynomial for the common 1.03 secant gain

A Taylor polynomial is centered at 9/20; its
quadratic coefficient dominates the entire higher-degree tail on the
one interval |s-9/20|≤9/20. Completing a square proves positivity. The
finite coefficient reductions are specified from the polynomial itself
and have not been executed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SecantGainPolynomial
open Polynomial

def numerator : ℚ[X] := C (13/12)*VaryingBCertificate.S11-
  C (103/100)*X*VaryingBCertificate.C12-
  C (64551/40000)*(1-VaryingBCertificate.C10)+
  C (111571/200000)*VaryingBCertificate.S11^2+
  C (59531/1000000)*VaryingBCertificate.S11^4
def certificate : ℚ[X] := numerator.divX
def shifted : ℚ[X] := certificate.comp (C (9/20)+X)
def b (j : ℕ) : ℚ := shifted.coeff j
def tailBudget : ℚ := ∑ j : Fin 41,|b (j.val+3)| *(9/20)^(j.val+1)
def quadraticReserve : ℚ := b 2-tailBudget
def expansion : ℚ[X] := C (b 0)+C (b 1)*X+C (b 2)*X^2+
  ∑ j : Fin 41,C (b (j.val+3))*X^(j.val+3)

/-! Exact rational coefficient lists, evaluated by Horner's rule. The kernel
computes the coefficients of `shifted` from these lists. -/

private def r29_poly : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a+X*r29_poly l

private def r29_add : List ℚ → List ℚ → List ℚ
  | [],m => m
  | a :: l,[] => a :: l
  | a :: l,b :: m => (a+b) :: r29_add l m

private def r29_smul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: r29_smul c l

private def r29_mul : List ℚ → List ℚ → List ℚ
  | [],_ => []
  | a :: l,m => r29_add (r29_smul a m) (0 :: r29_mul l m)

private def r29_sub (l m : List ℚ) : List ℚ := r29_add l (r29_smul (-1) m)

private def r29_pow (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => r29_mul (r29_pow l n) l

private def r29_shiftStep (c b : ℚ) (m : List ℚ) : List ℚ :=
  r29_add [b] (r29_add (r29_smul c m) (0 :: m))

/-- Horner composition with `C c+X`. -/
private def r29_shift (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | b :: l => r29_shiftStep c b (r29_shift c l)

private theorem r29_poly_add : ∀ l m : List ℚ,r29_poly (r29_add l m)=r29_poly l+r29_poly m
  | [],m => by simp [r29_add,r29_poly]
  | a :: l,[] => by simp [r29_add,r29_poly]
  | a :: l,b :: m => by
    simp only [r29_add,r29_poly,r29_poly_add l m,map_add]
    ring

private theorem r29_poly_smul (c : ℚ) :
    ∀ l : List ℚ,r29_poly (r29_smul c l)=C c*r29_poly l
  | [] => by simp [r29_smul,r29_poly]
  | a :: l => by
    simp only [r29_smul,r29_poly,r29_poly_smul c l,map_mul]
    ring

private theorem r29_poly_mul : ∀ l m : List ℚ,r29_poly (r29_mul l m)=r29_poly l*r29_poly m
  | [],m => by simp [r29_mul,r29_poly]
  | a :: l,m => by
    rw [r29_mul,r29_poly_add,r29_poly_smul]
    simp only [r29_poly,r29_poly_mul l m,map_zero]
    ring

private theorem r29_poly_sub (l m : List ℚ) :
    r29_poly (r29_sub l m)=r29_poly l-r29_poly m := by
  rw [r29_sub,r29_poly_add,r29_poly_smul,map_neg,map_one]
  ring

private theorem r29_poly_pow (l : List ℚ) : ∀ n : ℕ,r29_poly (r29_pow l n)=r29_poly l^n
  | 0 => by simp [r29_pow,r29_poly]
  | n+1 => by rw [r29_pow,r29_poly_mul,r29_poly_pow l n,pow_succ]

private theorem r29_poly_shift (c : ℚ) :
    ∀ l : List ℚ,r29_poly (r29_shift c l)=(r29_poly l).comp (C c+X)
  | [] => by simp [r29_shift,r29_poly]
  | b :: l => by
    simp only [r29_shift,r29_shiftStep,r29_poly_add,r29_poly_smul,r29_poly,r29_poly_shift c l,
      add_comp,C_comp,mul_comp,X_comp,map_zero,mul_zero,add_zero]
    ring

private theorem r29_poly_tail : ∀ l : List ℚ,r29_poly l.tail=divX (r29_poly l)
  | [] => by simp [r29_poly]
  | a :: l => by
    simp only [r29_poly,List.tail_cons,divX_add,divX_C,zero_add]
    ext n
    rw [coeff_divX,coeff_X_mul]

private theorem r29_coeff_poly : ∀ (l : List ℚ) (n : ℕ),(r29_poly l).coeff n=l.getD n 0
  | [],n => by simp [r29_poly]
  | a :: l,0 => by simp [r29_poly]
  | a :: l,n+1 => by
    simp only [r29_poly,coeff_add,coeff_C,coeff_X_mul,r29_coeff_poly l n]
    simp

private theorem r29_natDegree_poly : ∀ l : List ℚ,(r29_poly l).natDegree≤l.length-1
  | [] => by simp [r29_poly]
  | [a] => by simp [r29_poly]
  | a :: b :: l => by
    have ih := r29_natDegree_poly (b :: l)
    have h1 : (X*r29_poly (b :: l)).natDegree≤(b :: l).length := by
      calc (X*r29_poly (b :: l)).natDegree≤X.natDegree+(r29_poly (b :: l)).natDegree :=
            natDegree_mul_le
        _≤1+((b :: l).length-1) := by
            gcongr
            exact natDegree_X_le
        _=(b :: l).length := by simp; omega
    calc (r29_poly (a :: b :: l)).natDegree≤
          max (C a).natDegree (X*r29_poly (b :: l)).natDegree := natDegree_add_le _ _
      _≤(a :: b :: l).length-1 := by
          rw [natDegree_C]
          simp only [List.length_cons] at h1 ⊢
          omega

private def r29_X : List ℚ := [0,1]
private def r29_C (q : ℚ) : List ℚ := [q]

private theorem r29_poly_X : r29_poly r29_X=X := by simp [r29_X,r29_poly]
private theorem r29_poly_C (q : ℚ) : r29_poly (r29_C q)=C q := by simp [r29_C,r29_poly]

private def r29_S9 : List ℚ :=
  r29_add (r29_sub (r29_add (r29_sub r29_X (r29_mul (r29_C (1/6)) (r29_pow r29_X 3)))
    (r29_mul (r29_C (1/120)) (r29_pow r29_X 5))) (r29_mul (r29_C (1/5040)) (r29_pow r29_X 7)))
    (r29_mul (r29_C (1/362880)) (r29_pow r29_X 9))
private def r29_S11 : List ℚ :=
  r29_sub r29_S9 (r29_mul (r29_C (1/39916800)) (r29_pow r29_X 11))
private def r29_C10 : List ℚ :=
  r29_sub (r29_add (r29_sub (r29_add (r29_sub (r29_C 1)
    (r29_mul (r29_C (1/2)) (r29_pow r29_X 2)))
    (r29_mul (r29_C (1/24)) (r29_pow r29_X 4))) (r29_mul (r29_C (1/720)) (r29_pow r29_X 6)))
    (r29_mul (r29_C (1/40320)) (r29_pow r29_X 8)))
    (r29_mul (r29_C (1/3628800)) (r29_pow r29_X 10))
private def r29_C12 : List ℚ :=
  r29_add r29_C10 (r29_mul (r29_C (1/479001600)) (r29_pow r29_X 12))
private def r29_num : List ℚ :=
  r29_add (r29_add (r29_sub (r29_sub (r29_mul (r29_C (13/12)) r29_S11)
    (r29_mul (r29_mul (r29_C (103/100)) r29_X) r29_C12))
    (r29_mul (r29_C (64551/40000)) (r29_sub (r29_C 1) r29_C10)))
    (r29_mul (r29_C (111571/200000)) (r29_pow r29_S11 2)))
    (r29_mul (r29_C (59531/1000000)) (r29_pow r29_S11 4))
private def r29_B : List ℚ := r29_shift (9/20) r29_num.tail

private theorem r29_rep_num : r29_poly r29_num=numerator := by
  simp only [r29_num,r29_S11,r29_S9,r29_C10,r29_C12,r29_poly_add,r29_poly_sub,r29_poly_mul,
    r29_poly_pow,r29_poly_C,r29_poly_X,map_one,numerator,VaryingBCertificate.S11,
    VaryingBCertificate.S9,VaryingBCertificate.C10,VaryingBCertificate.C12]

private theorem r29_rep_shifted : r29_poly r29_B=shifted := by
  rw [r29_B,r29_poly_shift,r29_poly_tail,r29_rep_num]
  rfl

private theorem r29_b_eq (j : ℕ) : b j=r29_B.getD j 0 := by
  rw [b,← r29_rep_shifted,r29_coeff_poly]

theorem zero_identity : X*certificate=numerator := by
  have h0 : numerator.coeff 0=0 := by
    rw [← r29_rep_num,r29_coeff_poly]
    decide +kernel
  have h := X_mul_divX_add numerator
  rwa [h0,map_zero,add_zero] at h

theorem expansion_identity : shifted=expansion := by
  have hdeg : shifted.natDegree<44 := by
    rw [← r29_rep_shifted]
    have h := r29_natDegree_poly r29_B
    have hl : r29_B.length=44 := by decide +kernel
    omega
  have hsplit (f : ℕ → ℚ[X]) :
      ∑ i ∈ Finset.range 44,f i=f 0+f 1+f 2+∑ j : Fin 41,f (j.val+3) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => f (i+3)) 41,
      show 44=3+41 from rfl,Finset.sum_range_add]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,add_comm 3]
  rw [shifted.as_sum_range_C_mul_X_pow' hdeg,hsplit]
  simp only [expansion,b,pow_zero,mul_one,pow_one]

theorem coefficient_reserves :
    (2427/1250000 : ℚ)<b 0 ∧ |b 1|<(169/200000 : ℚ) ∧
      (12849/100000 : ℚ)<quadraticReserve := by
  simp only [quadraticReserve,tailBudget,r29_b_eq]
  decide +kernel

theorem tail_term_lower {z : ℝ} (hz : |z|≤9/20) (j : Fin 41) :
    -( |(b (j.val+3):ℝ)| *(9/20)^(j.val+1))*z^2≤
      (b (j.val+3):ℝ)*z^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (b (j.val+3):ℝ))
  have habs : |(b (j.val+3):ℝ)*z^(j.val+1)|≤
      |(b (j.val+3):ℝ)| *(9/20)^(j.val+1) := by simpa [abs_mul,abs_pow] using hm
  have hlo := (abs_le.mp habs).1
  have hprod := mul_le_mul_of_nonneg_right hlo (sq_nonneg z)
  have hid : z^(j.val+3)=z^(j.val+1)*z^2 := by ring
  rw [hid]
  nlinarith

theorem quadratic_lower {z : ℝ} (hz : |z|≤9/20) :
    (b 0:ℝ)+(b 1:ℝ)*z+(quadraticReserve:ℝ)*z^2≤aeval z shifted := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => tail_term_lower hz j)
  have hbudget : ∑ j : Fin 41,-(|(b (j.val+3):ℝ)| *(9/20)^(j.val+1))*z^2=
      -(tailBudget:ℝ)*z^2 := by
    simp [tailBudget,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [hbudget] at hh
  rw [expansion_identity]
  simp only [expansion,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  dsimp [quadraticReserve]
  push_cast
  linarith

theorem shifted_positive {z : ℝ} (hz : |z|≤9/20) :
    (97/50000 : ℝ)<aeval z shifted := by
  have h0 : (2427/1250000 : ℝ)<(b 0:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.1
    rwa [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
  have h1 : |(b 1:ℝ)|<(169/200000 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.2.1
    rwa [Rat.cast_abs,Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
  have h2 : (12849/100000 : ℝ)<(quadraticReserve:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr coefficient_reserves.2.2
    rwa [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
  have hlin := neg_abs_le ((b 1:ℝ)*z)
  rw [abs_mul] at hlin
  have hprod := mul_le_mul_of_nonneg_right h1.le (abs_nonneg z)
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg z)
  have h := quadratic_lower hz
  nlinarith [sq_abs z,sq_nonneg (|z|-(169/51396 : ℝ))]

theorem certificate_positive {s : ℝ} (hs : s∈Set.Icc 0 frameCap) :
    (97/50000 : ℝ)<aeval s certificate := by
  have hs2 : s≤7/10 := hs.2
  have hz : |s-9/20|≤9/20 := by apply abs_le.mpr; constructor <;> linarith [hs.1]
  have hh := shifted_positive hz
  have he : aeval (s-9/20) shifted=aeval s certificate := by
    rw [shifted,aeval_comp]
    congr 1
    simp
  rwa [he] at hh

theorem numerator_positive {s : ℝ} (hs : s∈Set.Ioc 0 frameCap) :
    0<aeval s numerator := by
  have h := congrArg (fun p : ℚ[X] => aeval s p) zero_identity
  simp only [map_mul,aeval_X] at h
  rw [← h]
  exact mul_pos hs.1 (by linarith [certificate_positive (Set.Ioc_subset_Icc_self hs)])

theorem sine11_nonneg {s : ℝ} (hs : s∈Set.Icc 0 frameCap) :
    0≤HighOrderTaylor.S11 s := by
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have h1 : 0≤1-s^2/6 := by norm_num [frameCap] at hs2; nlinarith
  have h2 : 0≤1/120-s^2/5040 := by norm_num [frameCap] at hs2; nlinarith
  have h3 : 0≤1/362880-s^2/39916800 := by norm_num [frameCap] at hs2; nlinarith
  have he : HighOrderTaylor.S11 s=
      s*(1-s^2/6)+s^5*(1/120-s^2/5040)+s^9*(1/362880-s^2/39916800) := by
    dsimp [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7]
    ring
  rw [he]
  have k1 := mul_nonneg hs.1 h1
  have k2 := mul_nonneg (pow_nonneg hs.1 5) h2
  have k3 := mul_nonneg (pow_nonneg hs.1 9) h3
  linarith

theorem trigonometric_positive {s : ℝ} (hs : s∈Set.Ioc 0 frameCap) :
    0<(13/12)*Real.sin s-(103/100)*s*Real.cos s-
      (64551/40000)*(1-Real.cos s)+(111571/200000)*(Real.sin s)^2+
        (59531/1000000)*(Real.sin s)^4 := by
  have hp := numerator_positive hs
  have hS := HighOrderTaylor.S11_le_sin hs.1.le
  have hC := HighOrderTaylor.cos_le_C12 hs.1.le
  have hcl := Arithmetic.cos10_le_cos hs.1.le
  have hs0 := sine11_nonneg (Set.Ioc_subset_Icc_self hs)
  have hs2 := pow_le_pow_left₀ hs0 hS 2
  have hs4 := pow_le_pow_left₀ hs0 hS 4
  have hcosprod := mul_le_mul_of_nonneg_left hC hs.1.le
  simp only [numerator,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    VaryingBCertificate.S11_eval,VaryingBCertificate.C12_eval,VaryingBCertificate.C10_eval] at hp
  norm_num at hp
  linarith

end SquaresInCircles.Eight.SecantGainPolynomial
