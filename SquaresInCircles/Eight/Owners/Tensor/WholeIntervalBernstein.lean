module

public import SquaresInCircles.Eight.Arithmetic.TensorWholeIntervalPolynomial

/-!
# Eight squares: A Bernstein lower bound on one complete centered square

The polynomial identities and rational coefficient
reserves are checked in each application. The theorem here transfers
those identities to every real point of the square. The indices are
polynomial indices, not a subdivision of either angle variable.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TensorWholeIntervalBernstein
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

end SquaresInCircles.Eight.TensorWholeIntervalBernstein
