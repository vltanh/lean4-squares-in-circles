module
public import SquaresInCircles.Seven.Analysis

@[expose] public section

/-!
# Rational Taylor bounds used inside scalar proof certificates

Each new bound is obtained by differentiating the preceding nonnegative
remainder. The bounds hold on the whole nonnegative real axis. They are not
assumed numerical estimates, and no floating-point computation enters them.
-/

noncomputable section
namespace SquaresInCircles.Six.ProofTools

private def c8 (x : ℝ) := 1-x^2/2+x^4/24-x^6/720+x^8/40320
private def s9 (x : ℝ) := x-x^3/6+x^5/120-x^7/5040+x^9/362880
private def c10 (x : ℝ) := c8 x-x^10/3628800
private def s11 (x : ℝ) := s9 x-x^11/39916800
private def c12 (x : ℝ) := c10 x+x^12/479001600
private def s13 (x : ℝ) := s11 x+x^13/6227020800
private def c14 (x : ℝ) := c12 x-x^14/87178291200
private def s15 (x : ℝ) := s13 x-x^15/1307674368000
private def c16 (x : ℝ) := c14 x+x^16/20922789888000
private def s17 (x : ℝ) := s15 x+x^17/355687428096000
private def c18 (x : ℝ) := c16 x-x^18/6402373705728000
private def s19 (x : ℝ) := s17 x-x^19/121645100408832000
private def c20 (x : ℝ) := c18 x+x^20/2432902008176640000
private def s21 (x : ℝ) := s19 x+x^21/51090942171709440000
private def c22 (x : ℝ) := c20 x-x^22/1124000727777607680000
private def s23 (x : ℝ) := s21 x-x^23/25852016738884976640000

private lemma c8_bound {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ c8 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => c8 t-Real.cos t)
    (by dsimp [c8]; fun_prop) (by norm_num [c8])
    (fun t ht => by
      simp (disch := fun_prop) [c8]
      linarith [Seven.sin_lower_seven ht]) hx
  linarith

private lemma s9_bound {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ s9 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => s9 t-Real.sin t)
    (by dsimp [s9]; fun_prop) (by norm_num [s9])
    (fun t ht => by
      have hp := c8_bound ht
      dsimp [c8] at hp
      simp (disch := fun_prop) [s9]
      linarith) hx
  linarith

private lemma c10_bound {x : ℝ} (hx : 0 ≤ x) : c10 x ≤ Real.cos x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.cos t-c10 t)
    (by dsimp [c10,c8]; fun_prop) (by norm_num [c10,c8])
    (fun t ht => by
      have hp := s9_bound ht
      dsimp [s9] at hp
      simp (disch := fun_prop) [c10,c8]
      linarith) hx
  linarith

private lemma s11_bound {x : ℝ} (hx : 0 ≤ x) : s11 x ≤ Real.sin x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.sin t-s11 t)
    (by dsimp [s11,s9]; fun_prop) (by norm_num [s11,s9])
    (fun t ht => by
      have hp := c10_bound ht
      dsimp [c10,c8] at hp
      simp (disch := fun_prop) [s11,s9]
      linarith) hx
  linarith

private lemma c12_bound {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ c12 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => c12 t-Real.cos t)
    (by dsimp [c12,c10,c8]; fun_prop) (by norm_num [c12,c10,c8])
    (fun t ht => by
      have hp := s11_bound ht
      dsimp [s11,s9] at hp
      simp (disch := fun_prop) [c12,c10,c8]
      linarith) hx
  linarith

private lemma s13_bound {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ s13 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => s13 t-Real.sin t)
    (by dsimp [s13,s11,s9]; fun_prop) (by norm_num [s13,s11,s9])
    (fun t ht => by
      have hp := c12_bound ht
      dsimp [c12,c10,c8] at hp
      simp (disch := fun_prop) [s13,s11,s9]
      linarith) hx
  linarith

private lemma c14_bound {x : ℝ} (hx : 0 ≤ x) : c14 x ≤ Real.cos x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.cos t-c14 t)
    (by dsimp [c14,c12,c10,c8]; fun_prop) (by norm_num [c14,c12,c10,c8])
    (fun t ht => by
      have hp := s13_bound ht
      dsimp [s13,s11,s9] at hp
      simp (disch := fun_prop) [c14,c12,c10,c8]
      linarith) hx
  linarith

private lemma s15_bound {x : ℝ} (hx : 0 ≤ x) : s15 x ≤ Real.sin x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.sin t-s15 t)
    (by dsimp [s15,s13,s11,s9]; fun_prop) (by norm_num [s15,s13,s11,s9])
    (fun t ht => by
      have hp := c14_bound ht
      dsimp [c14,c12,c10,c8] at hp
      simp (disch := fun_prop) [s15,s13,s11,s9]
      linarith) hx
  linarith

private lemma c16_bound {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ c16 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => c16 t-Real.cos t)
    (by dsimp [c16,c14,c12,c10,c8]; fun_prop) (by norm_num [c16,c14,c12,c10,c8])
    (fun t ht => by
      have hp := s15_bound ht
      dsimp [s15,s13,s11,s9] at hp
      simp (disch := fun_prop) [c16,c14,c12,c10,c8]
      linarith) hx
  linarith

private lemma s17_bound {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ s17 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => s17 t-Real.sin t)
    (by dsimp [s17,s15,s13,s11,s9]; fun_prop) (by norm_num [s17,s15,s13,s11,s9])
    (fun t ht => by
      have hp := c16_bound ht
      dsimp [c16,c14,c12,c10,c8] at hp
      simp (disch := fun_prop) [s17,s15,s13,s11,s9]
      linarith) hx
  linarith

private lemma c18_bound {x : ℝ} (hx : 0 ≤ x) : c18 x ≤ Real.cos x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.cos t-c18 t)
    (by dsimp [c18,c16,c14,c12,c10,c8]; fun_prop)
    (by norm_num [c18,c16,c14,c12,c10,c8])
    (fun t ht => by
      have hp := s17_bound ht
      dsimp [s17,s15,s13,s11,s9] at hp
      simp (disch := fun_prop) [c18,c16,c14,c12,c10,c8]
      linarith) hx
  linarith

private lemma s19_bound {x : ℝ} (hx : 0 ≤ x) : s19 x ≤ Real.sin x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.sin t-s19 t)
    (by dsimp [s19,s17,s15,s13,s11,s9]; fun_prop)
    (by norm_num [s19,s17,s15,s13,s11,s9])
    (fun t ht => by
      have hp := c18_bound ht
      dsimp [c18,c16,c14,c12,c10,c8] at hp
      simp (disch := fun_prop) [s19,s17,s15,s13,s11,s9]
      linarith) hx
  linarith

private lemma c20_bound {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ c20 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => c20 t-Real.cos t)
    (by dsimp [c20,c18,c16,c14,c12,c10,c8]; fun_prop)
    (by norm_num [c20,c18,c16,c14,c12,c10,c8])
    (fun t ht => by
      have hp := s19_bound ht
      dsimp [s19,s17,s15,s13,s11,s9] at hp
      simp (disch := fun_prop) [c20,c18,c16,c14,c12,c10,c8]
      linarith) hx
  linarith

private lemma s21_bound {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ s21 x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => s21 t-Real.sin t)
    (by dsimp [s21,s19,s17,s15,s13,s11,s9]; fun_prop)
    (by norm_num [s21,s19,s17,s15,s13,s11,s9])
    (fun t ht => by
      have hp := c20_bound ht
      dsimp [c20,c18,c16,c14,c12,c10,c8] at hp
      simp (disch := fun_prop) [s21,s19,s17,s15,s13,s11,s9]
      linarith) hx
  linarith

private lemma c22_bound {x : ℝ} (hx : 0 ≤ x) : c22 x ≤ Real.cos x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.cos t-c22 t)
    (by dsimp [c22,c20,c18,c16,c14,c12,c10,c8]; fun_prop)
    (by norm_num [c22,c20,c18,c16,c14,c12,c10,c8])
    (fun t ht => by
      have hp := s21_bound ht
      dsimp [s21,s19,s17,s15,s13,s11,s9] at hp
      simp (disch := fun_prop) [c22,c20,c18,c16,c14,c12,c10,c8]
      linarith) hx
  linarith

private lemma s23_bound {x : ℝ} (hx : 0 ≤ x) : s23 x ≤ Real.sin x := by
  have hh := Seven.nonneg_of_deriv_nonneg (fun t => Real.sin t-s23 t)
    (by dsimp [s23,s21,s19,s17,s15,s13,s11,s9]; fun_prop)
    (by norm_num [s23,s21,s19,s17,s15,s13,s11,s9])
    (fun t ht => by
      have hp := c22_bound ht
      dsimp [c22,c20,c18,c16,c14,c12,c10,c8] at hp
      simp (disch := fun_prop) [s23,s21,s19,s17,s15,s13,s11,s9]
      linarith) hx
  linarith

/-- Ascending coefficients, for Horner evaluation. -/
def sinUpperCoeffs : List ℚ :=
  [0,1,0,-1/6,0,1/120,0,-1/5040,0,1/362880,0,-1/39916800,
   0,1/6227020800,0,-1/1307674368000,0,1/355687428096000,
   0,-1/121645100408832000,0,1/51090942171709440000]

def sinLowerCoeffs : List ℚ := sinUpperCoeffs ++ [0,-1/25852016738884976640000]

def cosUpperCoeffs : List ℚ :=
  [1,0,-1/2,0,1/24,0,-1/720,0,1/40320,0,-1/3628800,
   0,1/479001600,0,-1/87178291200,0,1/20922789888000,
   0,-1/6402373705728000,0,1/2432902008176640000]

def cosLowerCoeffs : List ℚ := cosUpperCoeffs ++ [0,-1/1124000727777607680000]

def evalPoly : List ℚ → ℝ → ℝ
  | [], _ => 0
  | q :: qs, x => (q : ℝ) + x * evalPoly qs x

lemma sin_taylor_bracket {x : ℝ} (hx : 0 ≤ x) :
    evalPoly sinLowerCoeffs x ≤ Real.sin x ∧ Real.sin x ≤ evalPoly sinUpperCoeffs x := by
  have hl := s23_bound hx
  have hu := s21_bound hx
  have hle : evalPoly sinLowerCoeffs x = s23 x := by
    norm_num [evalPoly, sinLowerCoeffs, sinUpperCoeffs, s23,s21,s19,s17,s15,s13,s11,s9]
    ring
  have hue : evalPoly sinUpperCoeffs x = s21 x := by
    norm_num [evalPoly, sinUpperCoeffs, s21,s19,s17,s15,s13,s11,s9]
    ring
  rw [hle, hue]
  exact ⟨hl, hu⟩

lemma cos_taylor_bracket {x : ℝ} (hx : 0 ≤ x) :
    evalPoly cosLowerCoeffs x ≤ Real.cos x ∧ Real.cos x ≤ evalPoly cosUpperCoeffs x := by
  have hl := c22_bound hx
  have hu := c20_bound hx
  have hle : evalPoly cosLowerCoeffs x = c22 x := by
    norm_num [evalPoly, cosLowerCoeffs, cosUpperCoeffs, c22,c20,c18,c16,c14,c12,c10,c8]
    ring
  have hue : evalPoly cosUpperCoeffs x = c20 x := by
    norm_num [evalPoly, cosUpperCoeffs, c20,c18,c16,c14,c12,c10,c8]
    ring
  rw [hle, hue]
  exact ⟨hl, hu⟩

end SquaresInCircles.Six.ProofTools
