module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic

/-!
# Eight squares: A rational coefficient norm for a whole interval

A polynomial identity
and a rational coefficient inequality imply a bound at every real point
of the interval. The coefficient formula is explicit; its input is a
polynomial, not a table of sampled angles.

Concrete applications must prove the displayed polynomial identity. It
is not supplied as an axiom or accepted by an external checker.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.WholeIntervalPolynomial
open Polynomial

def affine (a b : ℚ) : ℚ[X] := C ((a+b)/2)+C ((b-a)/2)*X
def centered (a b : ℚ) (p : ℚ[X]) : ℚ[X] := p.comp (affine a b)

/-- The coefficient of T_j in a monomial u^i, with the constant term's
factor one distinguished from the other coefficients' factor two. -/
def monomialCoefficient (i j : ℕ) : ℚ :=
  if j≤ i ∧ (i-j)%2=0 then
    (if j=0 then 1 else 2)*(Nat.choose i ((i-j)/2) : ℚ)/(2:ℚ)^i
  else 0

def coefficient (D : ℕ) (p : ℚ[X]) (j : ℕ) : ℚ :=
  ∑ i∈Finset.range (D+1),p.coeff i*monomialCoefficient i j

def series (D : ℕ) (b : ℕ → ℚ) : ℚ[X] :=
  C (b 0)+∑ j : Fin D,C (b (j.val+1))*Polynomial.Chebyshev.T ℚ (j.val+1)

def lower (D : ℕ) (b : ℕ → ℚ) : ℚ := b 0-∑ j : Fin D,|b (j.val+1)|
def upper (D : ℕ) (b : ℕ → ℚ) : ℚ := b 0+∑ j : Fin D,|b (j.val+1)|

def expansion (D : ℕ) (p : ℚ[X]) : ℚ[X] := series D (coefficient D p)
def lowerOn (D : ℕ) (a b : ℚ) (p : ℚ[X]) : ℚ :=
  lower D (coefficient D (centered a b p))
def upperOn (D : ℕ) (a b : ℚ) (p : ℚ[X]) : ℚ :=
  upper D (coefficient D (centered a b p))

theorem scalar_bounds {c t : ℝ} (ht : |t|≤1) : -|c|≤c*t ∧ c*t≤|c| := by
  have h : |c*t|≤|c| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left ht (abs_nonneg c)
  exact abs_le.mp h

theorem series_bounds (D : ℕ) (b : ℕ → ℚ) {u : ℝ} (hu : |u|≤1) :
    (lower D b : ℝ)≤aeval u (series D b) ∧
      aeval u (series D b)≤(upper D b : ℝ) := by
  have hterm : ∀ j : Fin D,
      -|(b (j.val+1) : ℝ)|≤
        (b (j.val+1) : ℝ)*(Polynomial.Chebyshev.T ℝ (j.val+1)).eval u ∧
      (b (j.val+1) : ℝ)*(Polynomial.Chebyshev.T ℝ (j.val+1)).eval u≤
        |(b (j.val+1) : ℝ)| := by
    intro j
    exact scalar_bounds (Polynomial.Chebyshev.abs_eval_T_real_le_one _ hu)
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hterm j).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hterm j).2)
  simp only [series,map_add,map_sum,map_mul,aeval_C,eq_ratCast,
    Polynomial.Chebyshev.aeval_T]
  dsimp [lower,upper]
  push_cast
  rw [Finset.sum_neg_distrib] at hlo
  constructor <;> linarith

theorem interval_bounds {D : ℕ} {a b : ℚ} {p : ℚ[X]}
    (hab : a<b)
    (hidentity : centered a b p=expansion D (centered a b p))
    {x : ℝ} (hx : x∈Set.Icc (a:ℝ) (b:ℝ)) :
    (lowerOn D a b p : ℝ)≤aeval x p ∧ aeval x p≤(upperOn D a b p : ℝ) := by
  have hgap : 0<(b:ℝ)-(a:ℝ) := by exact_mod_cast sub_pos.mpr hab
  let u : ℝ := (2*x-(a:ℝ)-(b:ℝ))/((b:ℝ)-(a:ℝ))
  have hu : |u|≤1 := by
    apply abs_le.mpr
    constructor
    · dsimp [u]
      apply (le_div_iff₀ hgap).2
      linarith [hx.1]
    · dsimp [u]
      apply (div_le_iff₀ hgap).2
      linarith [hx.2]
  have haff : aeval u (affine a b)=x := by
    simp [affine]
    dsimp [u]
    field_simp [hgap.ne']
    ring
  have he := congrArg (fun q : ℚ[X] => aeval u q) hidentity
  rw [centered,aeval_comp,haff] at he
  rw [he]
  exact series_bounds D (coefficient D (centered a b p)) hu

theorem positive_on_interval {D : ℕ} {a b reserve : ℚ} {p : ℚ[X]}
    (hab : a<b) (hidentity : centered a b p=expansion D (centered a b p))
    (hreserve : reserve<lowerOn D a b p) {x : ℝ}
    (hx : x∈Set.Icc (a:ℝ) (b:ℝ)) :
    (reserve:ℝ)<aeval x p := by
  have hcast : (reserve:ℝ)<(lowerOn D a b p:ℝ) := by exact_mod_cast hreserve
  exact hcast.trans_le (interval_bounds hab hidentity hx).1

end SquaresInCircles.Eight.WholeIntervalPolynomial
