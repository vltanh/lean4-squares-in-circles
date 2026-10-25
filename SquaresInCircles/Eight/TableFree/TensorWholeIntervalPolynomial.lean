module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# A rational tensor coefficient bound on one whole square

Uncompiled source draft.  A nested rational polynomial is expanded in
the tensor products of the ordinary Chebyshev polynomials.  The constant
coefficient minus the sum of the absolute values of every other
coefficient bounds its value on the entire closed unit square.

Applications supply an exact polynomial identity and exact rational
coefficient inequalities.  The construction has no grid or subdivision.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.TensorWholeIntervalPolynomial
open Polynomial

abbrev Bivar := Polynomial (Polynomial ℚ)

def scalar (r : ℚ) : Bivar := C (C r)

/-- The outer variable is evaluated at `x`, and the inner variable at `y`. -/
def evaluate (x y : ℝ) : Bivar →+* ℝ :=
  Polynomial.eval₂RingHom
    ((Polynomial.aeval y : ℚ[X] →ₐ[ℚ] ℝ).toRingHom) x

@[simp] theorem evaluate_C (x y : ℝ) (p : ℚ[X]) :
    evaluate x y (C p)=aeval y p := by
  simp [evaluate]

@[simp] theorem evaluate_scalar (x y : ℝ) (r : ℚ) :
    evaluate x y (scalar r)=(r:ℝ) := by
  simp [scalar]

@[simp] theorem evaluate_X (x y : ℝ) : evaluate x y X=x := by
  simp [evaluate]

@[simp] theorem evaluate_inner_X (x y : ℝ) : evaluate x y (C X)=y := by
  simp

def basis (i j : ℕ) : Bivar :=
  Polynomial.Chebyshev.T (Polynomial ℚ) i * C (Polynomial.Chebyshev.T ℚ j)

theorem evaluate_outer_T (x y : ℝ) (i : ℕ) :
    evaluate x y (Polynomial.Chebyshev.T (Polynomial ℚ) i)=
      (Polynomial.Chebyshev.T ℝ i).eval x := by
  change Polynomial.eval₂
    ((Polynomial.aeval y : ℚ[X] →ₐ[ℚ] ℝ).toRingHom) x _=_
  rw [← Polynomial.eval_map,Polynomial.Chebyshev.map_T]

theorem evaluate_basis (x y : ℝ) (i j : ℕ) :
    evaluate x y (basis i j)=
      (Polynomial.Chebyshev.T ℝ i).eval x *
        (Polynomial.Chebyshev.T ℝ j).eval y := by
  simp only [basis,map_mul,evaluate_outer_T,evaluate_C,
    Polynomial.Chebyshev.aeval_T]

/-- Formula (17): the tensor product of the exact monomial transforms. -/
def coefficient (D : ℕ) (p : Bivar) (i j : ℕ) : ℚ :=
  ∑ a : Fin (D+1),∑ b : Fin (D+1),
    (p.coeff a.val).coeff b.val *
      WholeIntervalPolynomial.monomialCoefficient a.val i *
      WholeIntervalPolynomial.monomialCoefficient b.val j

def indices (D : ℕ) : Finset (Fin (D+1) × Fin (D+1)) :=
  Finset.univ.erase (0,0)

def series (D : ℕ) (c : ℕ → ℕ → ℚ) : Bivar :=
  scalar (c 0 0)+
    ∑ ij∈indices D,scalar (c ij.1.val ij.2.val)*basis ij.1.val ij.2.val

def norm (D : ℕ) (c : ℕ → ℕ → ℚ) : ℚ :=
  ∑ ij∈indices D,|c ij.1.val ij.2.val|

def lower (D : ℕ) (c : ℕ → ℕ → ℚ) : ℚ := c 0 0-norm D c

def expansion (D : ℕ) (p : Bivar) : Bivar := series D (coefficient D p)

theorem basis_abs_le_one {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1)
    (i j : ℕ) : |evaluate x y (basis i j)|≤1 := by
  rw [evaluate_basis,abs_mul]
  have hi := Polynomial.Chebyshev.abs_eval_T_real_le_one (i:ℤ) hx
  have hj := Polynomial.Chebyshev.abs_eval_T_real_le_one (j:ℤ) hy
  simpa using mul_le_mul hi hj
    (abs_nonneg ((Polynomial.Chebyshev.T ℝ j).eval y)) (by norm_num : (0:ℝ)≤1)

theorem series_lower (D : ℕ) (c : ℕ → ℕ → ℚ) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) :
    (lower D c:ℝ)≤evaluate x y (series D c) := by
  have hterm (ij : Fin (D+1) × Fin (D+1)) :
      -|(c ij.1.val ij.2.val:ℝ)|≤
        (c ij.1.val ij.2.val:ℝ)*evaluate x y (basis ij.1.val ij.2.val) :=
    (WholeIntervalPolynomial.scalar_bounds
      (basis_abs_le_one hx hy ij.1.val ij.2.val)).1
  have hs := Finset.sum_le_sum (s := indices D) (fun ij _ => hterm ij)
  have hn : (norm D c:ℝ)=
      ∑ ij∈indices D,|(c ij.1.val ij.2.val:ℝ)| := by
    simp [norm]
  simp only [series,map_add,map_sum,map_mul,evaluate_scalar]
  dsimp only [lower]
  push_cast
  rw [hn]
  rw [Finset.sum_neg_distrib] at hs
  linarith

theorem lower_bound {D : ℕ} {p : Bivar}
    (hidentity : p=expansion D p) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) :
    (lower D (coefficient D p):ℝ)≤evaluate x y p := by
  have he := congrArg (fun z : Bivar => evaluate x y z) hidentity
  rw [he]
  exact series_lower D (coefficient D p) hx hy

theorem positive_on_square {D : ℕ} {p : Bivar} {reserve : ℚ}
    (hidentity : p=expansion D p)
    (hreserve : reserve<lower D (coefficient D p)) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) : (reserve:ℝ)<evaluate x y p := by
  have hc : (reserve:ℝ)<(lower D (coefficient D p):ℝ) := by
    exact_mod_cast hreserve
  exact hc.trans_le (lower_bound hidentity hx hy)

end SquaresInCircles.Eight.TableFree.TensorWholeIntervalPolynomial
