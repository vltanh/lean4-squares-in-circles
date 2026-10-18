module

public import SquaresInCircles.Eight.Generated.WholePairPolynomials

/-!
# The nineteen central-core polynomial cells

The definitions are exactly manuscript equation (4), before expansion. Every
generated row is linked to that expression by a polynomial identity. Closed
case splits cover the entire stated parameter intervals.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
open Generated

def centralBandP (Cminus D u : ℝ) : ℝ :=
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  let H := z/2+Cminus*c-D*s
  H^2*z+H*c*(c+s)+(1/2-(9789 : ℝ)/2500)*c^2*z

def centralBandV (A Cplus D u : ℝ) : ℝ :=
  let z := 1+u^2
  let c := 1-u^2
  let s := 2*u
  c*z/2+A*s*z-Cplus*s*c-D*c^2

def bandA_Cminus : ℝ := (10007/10000)*(9308368/10000000)
def bandA_Cplus : ℝ := (10007/10000)*(9308369/10000000)
def bandA_D : ℝ := (10007/10000)*(365435/1000000)
def bandB_Cminus : ℝ := (41/40)*(9286/10000)
def bandB_Cplus : ℝ := (41/40)*(9287/10000)
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

theorem segment_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP (11/12) (7/20) u := by
  rw [segment_P_identity]
  by_cases h₁ : u ≤ 1/4
  · exact central_segment_P0_positive ⟨hu.1,h₁⟩
  · by_cases h₂ : u ≤ 1/2
    · exact central_segment_P1_positive ⟨by linarith,h₂⟩
    · exact central_segment_P2_positive ⟨by linarith,hu.2⟩

theorem segment_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (1/2) (11/12) (7/20) u := by
  rw [segment_V_identity]
  by_cases h : u ≤ 3/14
  · exact central_segment_V0_positive ⟨hu.1,h⟩
  · exact central_segment_V1_positive ⟨by linarith,hu.2⟩

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

theorem bandA_V_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 3/7) :
    0 < centralBandV (5007/10000) bandA_Cplus bandA_D u := by
  rw [bandA_V_identity]
  by_cases h₁ : u ≤ 3/14
  · exact central_bandA_V0_positive ⟨hu.1,h₁⟩
  · by_cases h₂ : u ≤ 9/28
    · exact central_bandA_V1_positive ⟨by linarith,h₂⟩
    · exact central_bandA_V2_positive ⟨by linarith,hu.2⟩

theorem bandB_P_positive {u : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < centralBandP bandB_Cminus bandB_D u := by
  rw [bandB_P_identity]
  by_cases h : u ≤ 1/2
  · exact central_bandB_P0_positive ⟨hu.1,h⟩
  · exact central_bandB_P1_positive ⟨by linarith,hu.2⟩

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

theorem centralBandP_normalized (Cminus D u : ℝ) :
    centralBandP Cminus D u/(1+u^2)^3 =
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))^2+
      (1/2+Cminus*((1-u^2)/(1+u^2))-D*(2*u/(1+u^2)))*
        ((1-u^2)/(1+u^2))*(((1-u^2)/(1+u^2))+(2*u/(1+u^2)))+
      (1/2-(9789 : ℝ)/2500)*((1-u^2)/(1+u^2))^2 := by
  have hz : (1+u^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold centralBandP
  field_simp [hz]

/-- Increasing quadratic comparison, with its positive branch explicit. -/
theorem root_lt_of_quadratic_positive {X Y B C : ℝ}
    (hX : 0 ≤ X) (hY : 0 < Y) (hB : 0 ≤ B)
    (hroot : X^2+B*X+C=0) (hpoly : 0 < Y^2+B*Y+C) : X < Y := by
  by_contra h
  have hYX : Y ≤ X := le_of_not_gt h
  have hp := mul_nonneg (sub_nonneg.mpr hYX) (show 0 ≤ X+Y+B by linarith)
  nlinarith

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
