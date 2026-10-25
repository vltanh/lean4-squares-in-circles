module

public import SquaresInCircles.Eight.Arithmetic.Taylor

/-!
# Exact curvature of a norm with one sinusoidal phase

This calculus identity applies to a complete interval whenever the actual
radicand is positive. The later geometric applications derive positivity
from their circle forces. No derivative or curvature estimate is supplied
as an assumption to those applications.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.CircularNorm

def energy (A B C x : ℝ) : ℝ := A+B*Real.cos x+C*Real.sin x

def slope (B C x : ℝ) : ℝ := -B*Real.sin x+C*Real.cos x

def norm (A B C x : ℝ) : ℝ := Real.sqrt (energy A B C x)

def d1 (A B C x : ℝ) : ℝ := slope B C x/(2*norm A B C x)

def d2 (A B C x : ℝ) : ℝ :=
  (2*energy A B C x*(A-energy A B C x)-(slope B C x)^2)/
    (4*(norm A B C x)^3)

theorem energy_hasDerivAt (A B C x : ℝ) :
    HasDerivAt (energy A B C) (slope B C x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul B).const_add A).add
    ((Real.hasDerivAt_sin x).const_mul C)
  have e : slope B C x=B*-Real.sin x+C*Real.cos x := by unfold slope; ring
  rw [e]
  exact h

theorem slope_hasDerivAt (A B C x : ℝ) :
    HasDerivAt (slope B C) (A-energy A B C x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul (-B)).add
    ((Real.hasDerivAt_cos x).const_mul C)
  have e : A-energy A B C x= -B*Real.cos x+C*-Real.sin x := by unfold energy; ring
  rw [e]
  exact h

theorem norm_pos {A B C x : ℝ} (hp : 0<energy A B C x) :
    0<norm A B C x := Real.sqrt_pos.mpr hp

theorem norm_sq {A B C x : ℝ} (hp : 0≤energy A B C x) :
    (norm A B C x)^2=energy A B C x := Real.sq_sqrt hp

theorem norm_hasDerivAt {A B C x : ℝ} (hp : 0<energy A B C x) :
    HasDerivAt (norm A B C) (d1 A B C x) x :=
  (energy_hasDerivAt A B C x).sqrt hp.ne'

theorem d1_hasDerivAt {A B C x : ℝ} (hp : 0<energy A B C x) :
    HasDerivAt (d1 A B C) (d2 A B C x) x := by
  have hn := (norm_pos hp).ne'
  have he := norm_sq hp.le
  have hraw := (slope_hasDerivAt A B C x).div
    ((norm_hasDerivAt hp).const_mul 2) (mul_ne_zero (by norm_num) hn)
  convert hraw using 1
  · rfl
  · dsimp only [d2,d1]
    rw [← he]
    field_simp [hn]
    ring

/-- The identity is exact; a nonnegative numerator gives the universal
lower curvature bound `N'' ≥ -N/4`. -/
theorem curvature_identity {A B C x : ℝ} (hp : 0<energy A B C x) :
    d2 A B C x+norm A B C x/4=
      (A^2-B^2-C^2)/(4*(norm A B C x)^3) := by
  have hn := (norm_pos hp).ne'
  have he := norm_sq hp.le
  have hid : (energy A B C x)^2+(slope B C x)^2=
      2*A*energy A B C x-A^2+B^2+C^2 := by
    dsimp [energy,slope]
    linear_combination (B^2+C^2)*(Real.sin_sq_add_cos_sq x)
  rw [← he] at hid
  dsimp only [d2]
  rw [← he]
  field_simp [hn]
  nlinarith only [hid]

theorem curvature_lower {A B C x : ℝ} (hp : 0<energy A B C x)
    (hcoef : B^2+C^2≤A^2) :
    -(norm A B C x)/4≤d2 A B C x := by
  have hid := curvature_identity hp
  have hn : 0≤(A^2-B^2-C^2)/(4*(norm A B C x)^3) :=
    div_nonneg (by linarith) (mul_nonneg (by norm_num) (pow_nonneg (norm_pos hp).le 3))
  linarith

end SquaresInCircles.Eight.CircularNorm
