module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# A whole-interval Bernstein lower bound

Uncompiled source. A rational polynomial identity, nonnegative basis
functions, and their partition of unity imply a bound at every real
point. Concrete identities are proved in the application, not accepted
as external certificates or inferred from sampled values.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.WholeIntervalBernstein
open Polynomial

def basis (D : ℕ) (b : ℚ) (i : Fin (D+1)) : ℚ[X] :=
  C ((Nat.choose D i.val : ℚ)/b^D)*X^i.val*(C b-X)^(D-i.val)

def coefficient (D : ℕ) (b : ℚ) (p : ℚ[X]) (i : Fin (D+1)) : ℚ :=
  ∑ j∈Finset.range (i.val+1),p.coeff j*b^j*(Nat.choose i.val j : ℚ)/(Nat.choose D j : ℚ)

def expansion (D : ℕ) (b : ℚ) (p : ℚ[X]) : ℚ[X] :=
  ∑ i : Fin (D+1),C (coefficient D b p i)*basis D b i

theorem basis_nonneg {D : ℕ} {b : ℚ} (hb : 0<b) (i : Fin (D+1))
    {x : ℝ} (hx : x∈Set.Icc 0 (b:ℝ)) : 0≤aeval x (basis D b i) := by
  have hb' : (0:ℝ)<(b:ℝ) := by exact_mod_cast hb
  simp only [basis,map_mul,aeval_C,eq_ratCast,map_pow,aeval_X,map_sub]
  push_cast
  exact mul_nonneg
    (mul_nonneg (div_nonneg (by positivity) (pow_nonneg hb'.le _)) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem lower_on_interval {D : ℕ} {b r : ℚ} {p : ℚ[X]}
    (hb : 0<b) (hid : p=expansion D b p)
    (hone : (∑ i : Fin (D+1),basis D b i)=1)
    (hcoef : ∀i,r≤coefficient D b p i) {x : ℝ}
    (hx : x∈Set.Icc 0 (b:ℝ)) : (r:ℝ)≤aeval x p := by
  have hsum : (∑ i : Fin (D+1),aeval x (basis D b i))=1 := by
    simpa only [map_sum,map_one] using congrArg (aeval x) hone
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right
      (show (r:ℝ)≤(coefficient D b p i:ℝ) by exact_mod_cast hcoef i)
      (basis_nonneg hb i hx))
  rw [hid]
  simp only [expansion,map_sum,map_mul,aeval_C,eq_ratCast]
  rw [← Finset.mul_sum,hsum,mul_one] at hbound
  exact hbound

end SquaresInCircles.Eight.TableFree.WholeIntervalBernstein
