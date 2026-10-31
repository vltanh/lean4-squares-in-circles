module

public import SquaresInCircles.Eight.Arithmetic.PolynomialBounds

/-!
# Eight squares: the polynomials of the central band

Let `u ∈ [0, 1]` be the half-angle tangent of a direction `(c, s) = (cos θ, sin θ)` with
`0 ≤ θ ≤ π/2`, so that `c = (1 - u²) / (1 + u²)` and `s = 2u / (1 + u²)`. The polynomial
`centralBandP C⁻ D` is `(1 + u²)³` times `Y² + Y c (c + s) + (1/2 - Q₀) c²`, with
`Y = 1/2 + C⁻ c - D s` (`centralBandP_normalized`); where it is positive, and if `C⁻ ≥ 0` and
`0 ≤ D < 1/2`, a square in the disk of squared radius `Q₀` with state `(r c, r s)` has `r c < Y`
(`primary_upper` in `Bounds/Containing.lean`). The polynomial `centralBandV A C⁺ D` is
`(1 - u²)(1 + u²)` times `1/2 - C⁺ s - D c + A s / c`, so where it is positive and `u ≤ 3/7`,
`C⁺ s + D c - A s / c < 1/2` (`centralBandV_normalized`).

Three sets of parameters occur: the transverse segment, with `C⁻ = C⁺ = 11/12`, `D = 7/20` and
`A = 1/2`, and the bands A and B, whose constants bound `λ cos h` and `λ sin h` for
`(λ, h) = (10007/10000, 3741/10000)` and `(41/40, 19/50)`, with the lower bounds
`A = 5007/10000` and `A = 107/200` of the primary coordinate. Each polynomial is positive on its
interval. For `P` on `[0,1]`, a quadratic Taylor lower bound and a completed square prove
positivity in each case; the quartic remainder is a sum of terms nonnegative on `[0,1]`
(`PolynomialBounds.lean`). For `V` on `[0,3/7]`, expansion at `u=1/4` gives a quadratic
lower bound (`centralBandV_quadratic_lower`), and the same square-completion argument applies
(`centralBandV_positive_of_quadratic`). The trigonometric bounds use short decimals throughout.
`Bounds/Containing.lean` uses this positivity for the transverse segment (`transverse_segment_sides`)
and for the common points of the two bands (`bandA_sides`, `bandB_sides`), and proves the bounds
of `λ cos h` and `λ sin h` (`bandA_trig`, `bandB_trig`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
open PolynomialBounds

/-- `(1 + u²)³ (Y² + Y c (c + s) + (1/2 - Q₀) c²)` with `Y = 1/2 + C⁻ c - D s`, for the
direction `(c, s)` of half-angle tangent `u`, written with the numerators `1 - u²` and `2u` of
`c` and `s` and their denominator `1 + u²`. -/
def centralBandP (Cminus D u : ℝ) : ℝ :=
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  let H := z/2+Cminus*c-D*s
  H^2*z+H*c*(c+s)+(1/2-(9789 : ℝ)/2500)*c^2*z

/-- `(1 - u²)(1 + u²) (1/2 - C⁺ s - D c + A s / c)` for the direction `(c, s)` of half-angle
tangent `u`, written with the numerators `1 - u²` and `2u` of `c` and `s` and their denominator
`1 + u²`. -/
def centralBandV (A Cplus D u : ℝ) : ℝ :=
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  c*z/2+A*s*z-Cplus*s*c-D*c^2

/-- The lower bound `C⁻` of `λ cos h` in band A, where `λ = 10007/10000` and `h = 3741/10000`. -/
def bandA_Cminus : ℝ := 0.9314
/-- The upper bound `C⁺` of `λ cos h` in band A. -/
def bandA_Cplus : ℝ := 0.9315
/-- The upper bound `D` of `λ sin h` in band A. -/
def bandA_D : ℝ := 0.3657
/-- The lower bound `C⁻` of `λ cos h` in band B, where `λ = 41/40` and `h = 19/50`. -/
def bandB_Cminus : ℝ := 0.951
/-- The upper bound `C⁺` of `λ cos h` in band B. -/
def bandB_Cplus : ℝ := 0.952
/-- The upper bound `D` of `λ sin h` in band B. -/
def bandB_D : ℝ := 0.3805

/-- The coefficients of `P`, expressed in its two geometric bounds. -/
private def bandCoefficients (C D : ℝ) : Fin 7 → ℝ :=
  ![C^2+2*C-2.6656, -4*C*D+2*C-4*D+1,
    -C^2-2*C+4*D^2-4*D+3.6656, -4*C,
    -C^2+2*C+4*D^2+4*D+3.6656, 4*C*D+2*C-4*D-1, C^2-2*C-2.6656]

private theorem band_expansion (C D x : ℝ) : centralBandP C D x = sextic (bandCoefficients C D) x := by
  simp only [centralBandP, sextic, bandCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring


/-- A quadratic lower bound obtained by expanding at `u = 1/4`. -/
theorem centralBandV_quadratic_lower {A C D u : ℝ}
    (hAC : 7/5 ≤ A+C) (hD : 7/20 ≤ D ∧ D ≤ 2/5)
    (hu : 0 ≤ u ∧ u ≤ 3/7) :
    centralBandV A C D (1/4) +
        (19*A/8-13*C/8+15*D/16-1/32)*(u-1/4) +
        (3/2)*(u-1/4)^2 ≤ centralBandV A C D u := by
  let K := u^2+u/2+3/16
  have hu2 : u^2 ≤ 9/49 := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
  have hK : 0 ≤ K ∧ K ≤ 3/5 := by
    dsimp [K]
    constructor
    · nlinarith only [hu.1, sq_nonneg u]
    · linarith only [hu2, hu.2]
  have hlin : (7/5 : ℝ) ≤ (A+C)*(2*u+1) := calc
    (7/5 : ℝ) ≤ A+C := hAC
    _ ≤ (A+C)*(2*u+1) := le_mul_of_one_le_right (by linarith) (by linarith)
  have hneg : (1/2+D)*K ≤ 27/50 := calc
    (1/2+D)*K ≤ (9/10)*K := mul_le_mul_of_nonneg_right (by linarith) hK.1
    _ ≤ 27/50 := by linarith only [hK.2]
  have hcurv : 3/2 ≤ 2*D+(A+C)*(2*u+1)-(1/2+D)*K := by
    linarith only [hD.1,hlin,hneg]
  have hid : centralBandV A C D u = centralBandV A C D (1/4) +
      (19*A/8-13*C/8+15*D/16-1/32)*(u-1/4) +
      (u-1/4)^2*(2*D+(A+C)*(2*u+1)-(1/2+D)*K) := by
    dsimp [centralBandV, K]
    ring
  rw [hid]
  nlinarith only [mul_nonneg (sq_nonneg (u-1/4)) (sub_nonneg.mpr hcurv)]

/-- Positive curvature makes the value at `1/4` and its slope control the interval. -/
theorem centralBandV_positive_of_quadratic {A C D u : ℝ}
    (hAC : 7/5 ≤ A+C) (hD : 7/20 ≤ D ∧ D ≤ 2/5)
    (hmargin : (19*A/8-13*C/8+15*D/16-1/32)^2 <
      6*centralBandV A C D (1/4))
    (hu : 0 ≤ u ∧ u ≤ 3/7) : 0 < centralBandV A C D u := by
  have hlower := centralBandV_quadratic_lower hAC hD hu
  have hsquare := sq_nonneg (3*(u-1/4)+(19*A/8-13*C/8+15*D/16-1/32))
  nlinarith only [hlower, hsquare, hmargin]

/-- The polynomial `P` is positive on `[0,1]` by a quadratic lower bound and a completed square. -/
theorem segment_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP (11/12) (7/20) u := by
  rw [band_expansion]
  apply sextic_positive (a := 2/5) (m := 1/200) (hx := hu) <;>
    norm_num [remainder, slope, sextic, bandCoefficients]

/-- The polynomial `V` of the transverse segment is positive by completing a square. -/
theorem segment_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (1/2) (11/12) (7/20) u := by
  apply centralBandV_positive_of_quadratic (hu := hu) <;> norm_num [centralBandV]

/-- The polynomial `P` is positive on `[0,1]` by a quadratic lower bound and a completed square. -/
theorem bandA_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP bandA_Cminus bandA_D u := by
  rw [band_expansion]
  apply sextic_positive (a := 6/13) (m := 1/4) (hx := hu) <;>
    norm_num [remainder, slope, sextic, bandCoefficients, bandA_Cminus, bandA_D]

/-- The polynomial `V` of band A is positive by completing a square. -/
theorem bandA_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (5007/10000) bandA_Cplus bandA_D u := by
  apply centralBandV_positive_of_quadratic (hu := hu) <;>
    norm_num [centralBandV, bandA_Cplus, bandA_D]

/-- The polynomial `P` is positive on `[0,1]` by a quadratic lower bound and a completed square. -/
theorem bandB_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP bandB_Cminus bandB_D u := by
  rw [band_expansion]
  apply sextic_positive (a := 1/2) (m := 2/5) (hx := hu) <;>
    norm_num [remainder, slope, sextic, bandCoefficients, bandB_Cminus, bandB_D]

/-- The polynomial `V` of band B is positive by completing a square. -/
theorem bandB_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (107/200) bandB_Cplus bandB_D u := by
  apply centralBandV_positive_of_quadratic (hu := hu) <;>
    norm_num [centralBandV, bandB_Cplus, bandB_D]

/-- `centralBandP C⁻ D u / (1 + u²)³` in terms of `c = (1 - u²) / (1 + u²)` and
`s = 2u / (1 + u²)`. -/
theorem centralBandP_normalized (Cminus D u : ℝ) :
    centralBandP Cminus D u/(1+u^2)^3 =
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))^2+
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))*
        ((1-u^2)/(1+u^2))*(((1-u^2)/(1+u^2))+(2*u/(1+u^2)))+
      (1/2-(9789 : ℝ)/2500)*((1-u^2)/(1+u^2))^2 := by
  have hz : (1+u^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold centralBandP
  field_simp [hz]

/-- Where `centralBandV A C⁺ D` is positive and `0 ≤ u ≤ 3/7`, `C⁺ s + D c - A s / c < 1/2`
for `c = (1 - u²) / (1 + u²)`, `s = 2u / (1 + u²)` and `s / c = 2u / (1 - u²)`. -/
theorem centralBandV_normalized {A Cplus D u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7)
    (hp : 0 < centralBandV A Cplus D u) :
    Cplus*(2*u/(1+u^2))+D*((1-u^2)/(1+u^2))-
      A*(2*u/(1-u^2)) < 1/2 := by
  have hu2 : u^2 ≤ 9/49 := by
    nlinarith [mul_nonneg (show 0 ≤ 3/7-u by linarith) (show 0 ≤ 3/7+u by linarith)]
  have hc : 0 < 1-u^2 := by linarith
  have hz : 0 < 1+u^2 := by positivity
  have hid : centralBandV A Cplus D u / ((1-u^2)*(1+u^2)) =
      1/2-Cplus*(2*u/(1+u^2))-D*((1-u^2)/(1+u^2))+A*(2*u/(1-u^2)) := by
    unfold centralBandV
    field_simp [ne_of_gt hc,ne_of_gt hz]
    ring
  have hq := div_pos hp (mul_pos hc hz)
  rw [hid] at hq
  linarith

end SquaresInCircles.Eight.Arithmetic
