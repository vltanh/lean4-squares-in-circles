module

public import SquaresInCircles.Eight.TableFree.TensorPolynomialEnclosure

/-!
# Two-sided roots and reciprocals certified by exact residuals

Uncompiled source. Polynomial construction is separated from validity:
the squared residual certifies a root, and the product residual certifies
a reciprocal. All discarded coefficients remain in the exact L1 error.
The bounds hold on the entire square and require no subdivision.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.TensorResidualEnclosure
open Polynomial TensorWholeIntervalPolynomial TensorPolynomialEnclosure

def center (P : Bivar) : ℚ := (P.coeff 0).coeff 0
def polynomialFloor (P : Bivar) : ℚ := center P-norm (P-scalar (center P))
def floor (a : Enclosure) : ℚ := polynomialFloor a.polynomial-a.error

theorem polynomial_lower (P : Bivar) {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1) :
    (polynomialFloor P:ℝ)≤evaluate x y P := by
  have hh := evaluate_abs_le_norm (P-scalar (center P)) hx hy
  have hl := (abs_le.mp hh).1
  simp only [map_sub,evaluate_scalar] at hl
  dsimp [polynomialFloor]
  push_cast
  linarith

theorem Contains.lower {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) : (floor a:ℝ)≤v := by
  have hp := polynomial_lower a.polynomial hx hy
  have he := (abs_le.mp ha.2).1
  dsimp [floor]
  push_cast
  linarith

/-- The H7 expression only chooses the polynomial. Its validity below
comes from its complete squared residual, in both directions. -/
def rootPolynomial (a : Enclosure) : Bivar := (sqrtUpper ⟨a.polynomial,0⟩).polynomial
def rootResidual (a : Enclosure) : ℚ := norm ((rootPolynomial a)^2-a.polynomial)+a.error
def radicandRootLower (a : Enclosure) : ℚ := max 0 (nearestRoot (floor a)-1/100000000)
def rootFloor (a : Enclosure) : ℚ := polynomialFloor (rootPolynomial a)+radicandRootLower a
def root (a : Enclosure) : Enclosure :=
  ⟨rootPolynomial a,rootResidual a/rootFloor a⟩

theorem Contains.root {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hv : 0≤v) (hm : 0<rootFloor a) (hl : (radicandRootLower a)^2≤floor a) :
    Contains (root a) x y (Real.sqrt v) := by
  let w := evaluate x y (rootPolynomial a)
  have hm' : (0:ℝ)<(rootFloor a:ℝ) := by exact_mod_cast hm
  have hw : (polynomialFloor (rootPolynomial a):ℝ)≤w := polynomial_lower (rootPolynomial a) hx hy
  have hrootL : (radicandRootLower a:ℝ)≤Real.sqrt v := by
    have hl' : (radicandRootLower a:ℝ)^2≤(floor a:ℝ) := by exact_mod_cast hl
    have hl0 : (0:ℝ)≤(radicandRootLower a:ℝ) := by
      exact_mod_cast (le_max_left 0 (nearestRoot (floor a)-1/100000000))
    nlinarith [Contains.lower ha hx hy,Real.sq_sqrt hv,Real.sqrt_nonneg v]
  have hden : (rootFloor a:ℝ)≤Real.sqrt v+w := by
    dsimp [rootFloor]
    push_cast
    linarith
  have hres := evaluate_abs_le_norm ((rootPolynomial a)^2-a.polynomial) hx hy
  have hsum := abs_add_le (v-evaluate x y a.polynomial)
    (evaluate x y a.polynomial-w^2)
  have hres' : |evaluate x y a.polynomial-w^2|≤
      (norm ((rootPolynomial a)^2-a.polynomial):ℝ) := by
    simpa [w,map_sub,map_pow,abs_sub_comm] using hres
  have hr : |v-w^2|≤(rootResidual a:ℝ) := by
    have he : (v-evaluate x y a.polynomial)+(evaluate x y a.polynomial-w^2)=v-w^2 := by ring
    rw [he] at hsum
    dsimp [rootResidual]
    push_cast
    linarith [ha.2]
  have hsq := Real.sq_sqrt hv
  have hs0 := Real.sqrt_nonneg v
  have hid : |v-w^2|=|Real.sqrt v-w| * (Real.sqrt v+w) := by
    rw [show v-w^2=(Real.sqrt v-w)*(Real.sqrt v+w) by nlinarith [hsq],abs_mul,
      abs_of_pos (hm'.trans_le hden)]
  have hprod := mul_le_mul_of_nonneg_left hden
    (abs_nonneg (Real.sqrt v-w))
  refine ⟨div_nonneg (add_nonneg (norm_nonneg _) ha.1) hm.le,?_⟩
  change |Real.sqrt v-w|≤((rootResidual a/rootFloor a:ℚ):ℝ)
  push_cast
  apply (le_div_iff₀ hm').2
  rw [hid] at hr
  linarith

def reciprocalPolynomial (a : Enclosure) : Bivar :=
  let c := center a.polynomial
  truncate (scalar (1/c)*∑ j : Fin 15,(-(a.polynomial-scalar c)*scalar (1/c))^j.val)

def reciprocalResidual (a : Enclosure) : ℚ :=
  norm (a.polynomial*reciprocalPolynomial a-1)+a.error*norm (reciprocalPolynomial a)

def reciprocal (a : Enclosure) : Enclosure :=
  ⟨reciprocalPolynomial a,reciprocalResidual a/floor a⟩

theorem Contains.reciprocal {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hm : 0<floor a) : Contains (reciprocal a) x y (1/v) := by
  let P := evaluate x y a.polynomial
  let w := evaluate x y (reciprocalPolynomial a)
  have hm' : (0:ℝ)<(floor a:ℝ) := by exact_mod_cast hm
  have hv := Contains.lower ha hx hy
  have hv0 : 0<v := hm'.trans_le hv
  have hres := evaluate_abs_le_norm (a.polynomial*reciprocalPolynomial a-1) hx hy
  have hw := evaluate_abs_le_norm (reciprocalPolynomial a) hx hy
  have hmul := mul_le_mul ha.2 hw (abs_nonneg _)
    (show (0:ℝ)≤(a.error:ℝ) by exact_mod_cast ha.1)
  have hadd := abs_add_le (P*w-1) ((v-P)*w)
  have he : P*w-1+(v-P)*w=v*w-1 := by ring
  rw [he] at hadd
  have hr : |v*w-1|≤(reciprocalResidual a:ℝ) := by
    dsimp [P,w] at hadd
    simp only [map_sub,map_mul,map_one] at hres
    simp only [abs_mul] at hadd
    dsimp [reciprocalResidual]
    push_cast
    linarith
  have hid : |1/v-w| * v=|v*w-1| := by
    have hh : (1/v-w)*v= -(v*w-1) := by field_simp [hv0.ne']; ring
    rw [← abs_neg (v*w-1),← hh,abs_mul,abs_of_pos hv0]
  have hprod := mul_le_mul_of_nonneg_left hv (abs_nonneg (1/v-w))
  refine ⟨div_nonneg (add_nonneg (norm_nonneg _)
    (mul_nonneg ha.1 (norm_nonneg _))) hm.le,?_⟩
  change |1/v-w|≤((reciprocalResidual a/floor a:ℚ):ℝ)
  push_cast
  apply (le_div_iff₀ hm').2
  rw [hid] at hprod
  linarith

def divide (a b : Enclosure) : Enclosure := mul a (reciprocal b)

theorem Contains.divide {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) (hx : |x|≤1) (hy : |y|≤1)
    (hm : 0<floor b) : Contains (divide a b) x y (v/w) := by
  simpa [TensorResidualEnclosure.divide,div_eq_mul_inv] using
    ha.mul (Contains.reciprocal hb hx hy hm) hx hy

theorem Contains.positive {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) (hm : 0<floor a) : 0<v := by
  exact (show (0:ℝ)<(floor a:ℝ) by exact_mod_cast hm).trans_le (Contains.lower ha hx hy)

end SquaresInCircles.Eight.TableFree.TensorResidualEnclosure
