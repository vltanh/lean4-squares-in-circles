module

public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalPolynomial

/-!
# A Bernstein lower bound on one complete centered square

Uncompiled source. The polynomial identities and rational coefficient
reserves are checked in each application. The theorem here transfers
those identities to every real point of the square. The indices are
polynomial indices, not a subdivision of either angle variable.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.TensorWholeIntervalBernstein
open Polynomial TensorWholeIntervalPolynomial

def left : Bivar := scalar (1/2)*(X+1)
def right : Bivar := scalar (1/2)*(C X+1)

def basis (D : ℕ) (i j : Fin (D+1)) : Bivar :=
  scalar ((Nat.choose D i.val : ℚ)*(Nat.choose D j.val : ℚ))*
    left^i.val*(1-left)^(D-i.val)*right^j.val*(1-right)^(D-j.val)

/-- Coefficients after the substitution `X=2U-1`, `Y=2V-1`. -/
def shiftedCoefficient (D : ℕ) (p : Bivar) (k l : ℕ) : ℚ :=
  2^(k+l)*∑ i : Fin (D+1),∑ j : Fin (D+1),
    if k≤ i.val ∧ l≤j.val then
      (-1)^(i.val+j.val-k-l)*(Nat.choose i.val k : ℚ)*
        (Nat.choose j.val l : ℚ)*(p.coeff i.val).coeff j.val
    else 0

def coefficient (D : ℕ) (p : Bivar) (i j : Fin (D+1)) : ℚ :=
  ∑ k∈Finset.range (i.val+1),∑ l∈Finset.range (j.val+1),
    shiftedCoefficient D p k l*
      ((Nat.choose i.val k : ℚ)/(Nat.choose D k : ℚ))*
      ((Nat.choose j.val l : ℚ)/(Nat.choose D l : ℚ))

def expansion (D : ℕ) (p : Bivar) : Bivar :=
  ∑ i : Fin (D+1),∑ j : Fin (D+1),
    scalar (coefficient D p i j)*basis D i j

theorem basis_nonneg {D : ℕ} (i j : Fin (D+1)) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) : 0≤evaluate x y (basis D i j) := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hx0 : 0≤(1/2 : ℝ)*(x+1) := by linarith
  have hx1 : 0≤1-(1/2 : ℝ)*(x+1) := by linarith
  have hy0 : 0≤(1/2 : ℝ)*(y+1) := by linarith
  have hy1 : 0≤1-(1/2 : ℝ)*(y+1) := by linarith
  simp only [basis,left,right,map_mul,map_pow,map_sub,map_add,map_one,
    evaluate_scalar,evaluate_X,evaluate_inner_X]
  push_cast
  positivity

theorem lower_on_square {D : ℕ} {p : Bivar} {r : ℚ}
    (hid : p=expansion D p)
    (hone : (∑ i : Fin (D+1),∑ j : Fin (D+1),basis D i j)=1)
    (hcoef : ∀ i j,r≤coefficient D p i j) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) : (r:ℝ)≤evaluate x y p := by
  have hsum : (∑ i : Fin (D+1),∑ j : Fin (D+1),evaluate x y (basis D i j))=1 := by
    simpa only [map_sum,map_one] using congrArg (evaluate x y) hone
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_right
        (show (r:ℝ)≤(coefficient D p i j:ℝ) by exact_mod_cast hcoef i j)
        (basis_nonneg i j hx hy)))
  rw [hid]
  simp only [expansion,map_sum,map_mul,evaluate_scalar]
  simpa only [← Finset.mul_sum,hsum,mul_one] using hbound

end SquaresInCircles.Eight.TableFree.TensorWholeIntervalBernstein
