module

public import SquaresInCircles.Eight.TableFree.VaryingBCertificate

/-!
# The single polynomial for the common 1.03 secant gain

Uncompiled source draft. A Taylor polynomial is centered at 9/20; its
quadratic coefficient dominates the entire higher-degree tail on the
one interval |s-9/20|≤9/20. Completing a square proves positivity. The
finite coefficient reductions are specified from the polynomial itself
and have not been executed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecantGainPolynomial
open Polynomial

def numerator : ℚ[X] := C (13/12)*VaryingBCertificate.S11-
  C (103/100)*X*VaryingBCertificate.C12-
  C (64551/40000)*(1-VaryingBCertificate.C10)+
  C (111571/200000)*VaryingBCertificate.S11^2+
  C (59531/1000000)*VaryingBCertificate.S11^4
def certificate : ℚ[X] := numerator.divX
def shifted : ℚ[X] := certificate.comp (C (9/20)+X)
def b (j : ℕ) : ℚ := shifted.coeff j
def tailBudget : ℚ := ∑ j : Fin 41,|b (j.val+3)|*(9/20)^(j.val+1)
def quadraticReserve : ℚ := b 2-tailBudget
def expansion : ℚ[X] := C (b 0)+C (b 1)*X+C (b 2)*X^2+
  ∑ j : Fin 41,C (b (j.val+3))*X^(j.val+3)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zero_identity : X*certificate=numerator := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem expansion_identity : shifted=expansion := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserves :
    (2427/1250000 : ℚ)<b 0 ∧ |b 1|<(169/200000 : ℚ) ∧
      (12849/100000 : ℚ)<quadraticReserve := by decide

theorem tail_term_lower {z : ℝ} (hz : |z|≤9/20) (j : Fin 41) :
    -( |(b (j.val+3):ℝ)|*(9/20)^(j.val+1))*z^2≤
      (b (j.val+3):ℝ)*z^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (b (j.val+3):ℝ))
  have habs : |(b (j.val+3):ℝ)*z^(j.val+1)|≤
      |(b (j.val+3):ℝ)|*(9/20)^(j.val+1) := by simpa [abs_mul,abs_pow] using hm
  have hlo := (abs_le.mp habs).1
  have hprod := mul_le_mul_of_nonneg_right hlo (sq_nonneg z)
  have hid : z^(j.val+3)=z^(j.val+1)*z^2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hid]
  nlinarith

theorem quadratic_lower {z : ℝ} (hz : |z|≤9/20) :
    (b 0:ℝ)+(b 1:ℝ)*z+(quadraticReserve:ℝ)*z^2≤aeval z shifted := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => tail_term_lower hz j)
  have hbudget : ∑ j : Fin 41,-(|(b (j.val+3):ℝ)|*(9/20)^(j.val+1))*z^2=
      -(tailBudget:ℝ)*z^2 := by
    simp [tailBudget,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [hbudget] at hh
  rw [expansion_identity]
  simp only [expansion,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X]
  dsimp [quadraticReserve]
  push_cast
  linarith

theorem shifted_positive {z : ℝ} (hz : |z|≤9/20) :
    (97/50000 : ℝ)<aeval z shifted := by
  have h0 : (2427/1250000 : ℝ)<(b 0:ℝ) := by exact_mod_cast coefficient_reserves.1
  have h1 : |(b 1:ℝ)|<(169/200000 : ℝ) := by exact_mod_cast coefficient_reserves.2.1
  have h2 : (12849/100000 : ℝ)<(quadraticReserve:ℝ) := by exact_mod_cast coefficient_reserves.2.2
  have hlin := neg_abs_le ((b 1:ℝ)*z)
  rw [abs_mul] at hlin
  have hprod := mul_le_mul_of_nonneg_right h1.le (abs_nonneg z)
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg z)
  have h := quadratic_lower hz
  nlinarith [sq_abs z,sq_nonneg (|z|-(169/51396 : ℝ))]

theorem certificate_positive {s : ℝ} (hs : s∈Set.Icc 0 frameCap) :
    (97/50000 : ℝ)<aeval s certificate := by
  have hz : |s-9/20|≤9/20 := by apply abs_le.mpr; constructor <;> linarith [hs.1,hs.2]
  have hh := shifted_positive hz
  have he : aeval (s-9/20) shifted=aeval s certificate := by
    rw [shifted,aeval_comp]
    congr 1
    simp
    ring
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
  positivity

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

end SquaresInCircles.Eight.TableFree.SecantGainPolynomial
