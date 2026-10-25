module

public import Mathlib.Tactic

/-!
# Eight squares: A global seventh-degree upper polynomial for the square root

The remainder has an exact algebraic factorization
after writing the argument as a square. Every coefficient of the
remaining factor is positive. Thus the majorant is valid on the entire
nonnegative half-line, with no small-relative-error hypothesis.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SepticRadicalUpper

def H7 (w : ℝ) : ℝ :=
  1+w*(1/2+w*(-1/8+w*(1/16+w*(-5/128+w*(7/256+w*(-21/1024+w*(33/2048)))))))

def remainderFactor (y : ℝ) : ℝ :=
  (429+1384*y+2063*y^2+1776*y^3+915*y^4+264*y^5+33*y^6)/2048

theorem factorization (y : ℝ) :
    H7 (y^2-1)-y=(y-1)^8*remainderFactor y := by
  dsimp [H7,remainderFactor]
  ring

theorem factor_nonneg {y : ℝ} (hy : 0≤y) : 0≤remainderFactor y := by
  dsimp [remainderFactor]
  positivity

theorem square_upper {y : ℝ} (hy : 0≤y) : y≤H7 (y^2-1) := by
  have hh := mul_nonneg (by positivity : 0≤(y-1)^8) (factor_nonneg hy)
  rw [← factorization] at hh
  linarith

/-- An arbitrary positive rational seed may be used. Its numerical
accuracy affects only the size of the later polynomial, not validity. -/
theorem sqrt_upper {v ρ : ℝ} (hv : 0≤v) (hρ : 0<ρ) :
    Real.sqrt v≤ρ*H7 ((v-ρ^2)/ρ^2) := by
  have hy : 0≤Real.sqrt v/ρ := div_nonneg (Real.sqrt_nonneg v) hρ.le
  have hs := Real.sq_sqrt hv
  have hid : (Real.sqrt v/ρ)^2-1=(v-ρ^2)/ρ^2 := by
    field_simp [hρ.ne']
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (square_upper hy) hρ.le
  rw [hid] at hh
  have he : ρ*(Real.sqrt v/ρ)=Real.sqrt v := by field_simp [hρ.ne']
  rwa [he] at hh

end SquaresInCircles.Eight.SepticRadicalUpper
