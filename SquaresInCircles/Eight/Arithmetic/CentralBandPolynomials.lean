module

public import SquaresInCircles.Eight.Generated.WholePairPolynomials

/-!
# Eight squares: the polynomials of the central band

Let `u ∈ [0, 1]` be the half-angle tangent of a direction `(c, s) = (cos θ, sin θ)` with
`0 ≤ θ ≤ π/2`, so that `c = (1 - u²) / (1 + u²)` and `s = 2u / (1 + u²)`. The polynomial
`centralBandP C⁻ D` is `(1 + u²)³` times `Y² + Y c (c + s) + (1/2 - Q₀) c²`, with
`Y = 1/2 + C⁻ c - D s` (`centralBandP_normalized`); where it is positive, and if `C⁻ ≥ 0` and
`0 ≤ D < 1/2`, a square in the disk of squared radius `Q₀` with state `(r c, r s)` has `r c < Y`
(`primary_upper` in `CentralCore.lean`). The polynomial `centralBandV A C⁺ D` is
`(1 - u²)(1 + u²)` times `1/2 - C⁺ s - D c + A s / c`, so where it is positive and `u ≤ 3/7`,
`C⁺ s + D c - A s / c < 1/2` (`centralBandV_normalized`).

Three sets of parameters occur: the transverse segment, with `C⁻ = C⁺ = 11/12`, `D = 7/20` and
`A = 1/2`, and the bands A and B, whose constants bound `λ cos h` and `λ sin h` for
`(λ, h) = (10007/10000, 3741/10000)` and `(41/40, 19/50)`, with the lower bounds
`A = 5007/10000` and `A = 107/200` of the primary coordinate. Each of the six polynomials is
positive on its interval, `[0, 1]` for `P` and `[0, 3/7]` for `V`: it is the polynomial of its
Bernstein rows in `Generated/WholePairPolynomials000.lean` (`segment_P_identity` and the five
like it), and its interval is split into two to five pieces, nineteen in all, each covered by a
valid row (`Bernstein.lean`).
`CentralCore.lean` uses this positivity for the transverse segment (`transverse_segment_sides`)
and for the common points of the two bands (`bandA_sides`, `bandB_sides`), and proves the bounds
of `λ cos h` and `λ sin h` (`bandA_trig`, `bandB_trig`).
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
open Generated

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
def bandA_Cminus : ℝ := (10007/10000)*(9308368/10000000)
/-- The upper bound `C⁺` of `λ cos h` in band A. -/
def bandA_Cplus : ℝ := (10007/10000)*(9308369/10000000)
/-- The upper bound `D` of `λ sin h` in band A. -/
def bandA_D : ℝ := (10007/10000)*(365435/1000000)
/-- The lower bound `C⁻` of `λ cos h` in band B, where `λ = 41/40` and `h = 19/50`. -/
def bandB_Cminus : ℝ := (41/40)*(9286/10000)
/-- The upper bound `C⁺` of `λ cos h` in band B. -/
def bandB_Cplus : ℝ := (41/40)*(9287/10000)
/-- The upper bound `D` of `λ sin h` in band B. -/
def bandB_D : ℝ := (41/40)*(371/1000)

theorem segment_P_identity (u : ℝ) :
    centralBandP (11/12) (7/20) u = central_segment_P0.polynomial.eval u := by
  norm_num [centralBandP,central_segment_P0,QPoly.eval]
  ring

theorem segment_V_identity (u : ℝ) :
    centralBandV (1/2) (11/12) (7/20) u = central_segment_V0.polynomial.eval u := by
  norm_num [centralBandV,central_segment_V0,QPoly.eval]
  ring

theorem bandA_P_identity (u : ℝ) :
    centralBandP bandA_Cminus bandA_D u = central_bandA_P0.polynomial.eval u := by
  norm_num [centralBandP,bandA_Cminus,bandA_D,central_bandA_P0,QPoly.eval]
  ring

theorem bandA_V_identity (u : ℝ) :
    centralBandV (5007/10000) bandA_Cplus bandA_D u = central_bandA_V0.polynomial.eval u := by
  norm_num [centralBandV,bandA_Cplus,bandA_D,central_bandA_V0,QPoly.eval]
  ring

theorem bandB_P_identity (u : ℝ) :
    centralBandP bandB_Cminus bandB_D u = central_bandB_P0.polynomial.eval u := by
  norm_num [centralBandP,bandB_Cminus,bandB_D,central_bandB_P0,QPoly.eval]
  ring

theorem bandB_V_identity (u : ℝ) :
    centralBandV (107/200) bandB_Cplus bandB_D u = central_bandB_V0.polynomial.eval u := by
  norm_num [centralBandV,bandB_Cplus,bandB_D,central_bandB_V0,QPoly.eval]
  ring

/-- The polynomial `P` of the transverse segment is positive on `[0, 1]`, by three rows. -/
theorem segment_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP (11/12) (7/20) u := by
  rw [segment_P_identity]
  by_cases h₁ : u ≤ 1/4
  · exact central_segment_P0_positive ⟨hu.1,h₁⟩
  · by_cases h₂ : u ≤ 1/2
    · exact central_segment_P1_positive ⟨by linarith,h₂⟩
    · exact central_segment_P2_positive ⟨by linarith,hu.2⟩

/-- The polynomial `V` of the transverse segment is positive on `[0, 3/7]`, by two rows. -/
theorem segment_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (1/2) (11/12) (7/20) u := by
  rw [segment_V_identity]
  by_cases h : u ≤ 3/14
  · exact central_segment_V0_positive ⟨hu.1,h⟩
  · exact central_segment_V1_positive ⟨by linarith,hu.2⟩

/-- The polynomial `P` of band A is positive on `[0, 1]`, by five rows. -/
theorem bandA_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP bandA_Cminus bandA_D u := by
  rw [bandA_P_identity]
  by_cases h₁ : u ≤ 1/4
  · exact central_bandA_P0_positive ⟨hu.1,h₁⟩
  · by_cases h₂ : u ≤ 3/8
    · exact central_bandA_P1_positive ⟨by linarith,h₂⟩
    · by_cases h₃ : u ≤ 7/16
      · exact central_bandA_P2_positive ⟨by linarith,h₃⟩
      · by_cases h₄ : u ≤ 1/2
        · exact central_bandA_P3_positive ⟨by linarith,h₄⟩
        · exact central_bandA_P4_positive ⟨by linarith,hu.2⟩

/-- The polynomial `V` of band A is positive on `[0, 3/7]`, by three rows. -/
theorem bandA_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (5007/10000) bandA_Cplus bandA_D u := by
  rw [bandA_V_identity]
  by_cases h₁ : u ≤ 3/14
  · exact central_bandA_V0_positive ⟨hu.1,h₁⟩
  · by_cases h₂ : u ≤ 9/28
    · exact central_bandA_V1_positive ⟨by linarith,h₂⟩
    · exact central_bandA_V2_positive ⟨by linarith,hu.2⟩

/-- The polynomial `P` of band B is positive on `[0, 1]`, by two rows. -/
theorem bandB_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP bandB_Cminus bandB_D u := by
  rw [bandB_P_identity]
  by_cases h : u ≤ 1/2
  · exact central_bandB_P0_positive ⟨hu.1,h⟩
  · exact central_bandB_P1_positive ⟨by linarith,hu.2⟩

/-- The polynomial `V` of band B is positive on `[0, 3/7]`, by four rows. -/
theorem bandB_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (107/200) bandB_Cplus bandB_D u := by
  rw [bandB_V_identity]
  by_cases h₁ : u ≤ 3/14
  · exact central_bandB_V0_positive ⟨hu.1,h₁⟩
  · by_cases h₂ : u ≤ 15/56
    · exact central_bandB_V1_positive ⟨by linarith,h₂⟩
    · by_cases h₃ : u ≤ 9/28
      · exact central_bandB_V2_positive ⟨by linarith,h₃⟩
      · exact central_bandB_V3_positive ⟨by linarith,hu.2⟩

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
