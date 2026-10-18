module

public import SquaresInCircles.Eight.Generated.WholePairPolynomials
public import SquaresInCircles.Eight.Arithmetic.ClosedCover

/-!
# Continuous meaning of the low/low polynomial rows

This module attaches the five explicit polynomial certificates to the actual
trigonometric and radical expressions in LOW_LOW_WHOLE_PAIR_HAND_PROOF,
equations (9)--(16).  It supplies a complete closed scalar chain for each
source sign on the positive-target secondary axis.  Geometric source/target
support is supplied separately by the affine-arc kernel.
-/

@[expose] public section

namespace SquaresInCircles.Eight.Arithmetic
open Generated

def lowU : ℝ := 3231/8000
def lowV : ℝ := 217813/200000
def lowQ : ℝ := 9789/2500
def lowBeta : ℝ := 9/50
def lowA0lo : ℝ := 141457/100000
def lowA0hi : ℝ := 70729/50000
def lowA1hi : ℝ := 1039/800
def lowB1lo : ℝ := 64937/200000
def lowL1hi : ℝ := 30683/100000
def lowS3 (x : ℝ) : ℝ := x-x^3/6
def lowS5 (x : ℝ) : ℝ := x-x^3/6+x^5/120
def lowC4 (x : ℝ) : ℝ := 1-x^2/2+x^4/24
def lowC6 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720

def lowT (λ ε x : ℝ) : ℝ := x+9/100+lowU*lowA0lo+
  (lowU+lowV+λ)/2-91/100-ε+(λ-9/100)*lowS3 x-(9/100)*lowC4 x
def lowNormMajorant (λ x : ℝ) : ℝ :=
  lowU^2+lowV^2+λ^2+2*λ*(lowU*lowS5 x-lowV*lowC6 x)
def lowCirclePolynomial (λ ε x : ℝ) : ℝ :=
  (lowT λ ε x)^2-lowQ*lowNormMajorant λ x

def lowEndpointPolynomial (λ ε x : ℝ) : ℝ :=
  x-ε-lowL1hi+(λ+lowBeta)/2-91/100+
    ((λ-lowBeta)/2+λ*lowB1lo)*lowC6 x+
    ((λ-lowBeta)/2-λ*lowA1hi)*lowS5 x

def lowAxialPolynomial (x : ℝ) : ℝ :=
  x-13/1000+(24/25+lowBeta)/2-91/100+
    (39/100)*lowC6 x+((39/100)-(24/25)*lowA0hi)*lowS5 x

theorem low_circle_plus_identity (x : ℝ) :
    lowCirclePolynomial (189/200) (1/50000) x =
      low_low_whole_pair_plus_circle.polynomial.eval x := by
  norm_num [lowCirclePolynomial,lowT,lowNormMajorant,lowU,lowV,lowQ,lowA0lo,
    lowS3,lowS5,lowC4,lowC6,low_low_whole_pair_plus_circle,QPoly.eval]
  ring

theorem low_circle_minus_identity (x : ℝ) :
    lowCirclePolynomial 1 0 x = low_low_whole_pair_minus_circle.polynomial.eval x := by
  norm_num [lowCirclePolynomial,lowT,lowNormMajorant,lowU,lowV,lowQ,lowA0lo,
    lowS3,lowS5,lowC4,lowC6,low_low_whole_pair_minus_circle,QPoly.eval]
  ring

theorem low_endpoint_plus_identity (x : ℝ) :
    lowEndpointPolynomial (189/200) (1/50000) x =
      low_low_whole_pair_plus_endpoint.polynomial.eval x := by
  norm_num [lowEndpointPolynomial,lowL1hi,lowBeta,lowB1lo,lowA1hi,
    lowS5,lowC6,low_low_whole_pair_plus_endpoint,QPoly.eval]
  ring

theorem low_endpoint_minus_identity (x : ℝ) :
    lowEndpointPolynomial 1 0 x = low_low_whole_pair_minus_endpoint.polynomial.eval x := by
  norm_num [lowEndpointPolynomial,lowL1hi,lowBeta,lowB1lo,lowA1hi,
    lowS5,lowC6,low_low_whole_pair_minus_endpoint,QPoly.eval]
  ring

theorem low_axial_identity (x : ℝ) :
    lowAxialPolynomial x = low_low_whole_pair_negative_target_axial.polynomial.eval x := by
  norm_num [lowAxialPolynomial,lowBeta,lowA0hi,lowS5,lowC6,
    low_low_whole_pair_negative_target_axial,QPoly.eval]
  ring

def lowNormSq (λ x : ℝ) : ℝ :=
  lowU^2+lowV^2+λ^2+2*λ*(lowU*Real.sin x-lowV*Real.cos x)

def lowCircleExpression (λ ε a₀ x : ℝ) : ℝ :=
  x+9/100+lowU*a₀+(lowU+lowV+λ)/2-ε+
    (λ-9/100)*Real.sin x-(9/100)*Real.cos x-
    Real.sqrt lowQ*Real.sqrt (lowNormSq λ x)

def lowEndpointExpression (λ ε a₁ b₁ L₁ x : ℝ) : ℝ :=
  x-ε-L₁+(λ+lowBeta)/2+
    ((λ-lowBeta)/2+λ*b₁)*Real.cos x+
    ((λ-lowBeta)/2-λ*a₁)*Real.sin x

theorem lowNormSq_nonneg (λ x : ℝ) : 0 ≤ lowNormSq λ x := by
  have hid : lowNormSq λ x =
      (lowU+λ*Real.sin x)^2+(lowV-λ*Real.cos x)^2 := by
    unfold lowNormSq
    linear_combination -λ^2*(Real.sin_sq_add_cos_sq x)
  rw [hid]
  positivity

theorem lowNormMajorant_sound {λ x : ℝ} (hλ : 0 ≤ λ) (hx : 0 ≤ x) :
    lowNormSq λ x ≤ lowNormMajorant λ x := by
  have hs := sin_upper_five hx
  have hc := cos_lower_six hx
  have hu : 0 ≤ lowU := by norm_num [lowU]
  have hv : 0 ≤ lowV := by norm_num [lowV]
  have h₁ := mul_le_mul_of_nonneg_left hs hu
  have h₂ := mul_le_mul_of_nonneg_left hc hv
  have h₃ := mul_le_mul_of_nonneg_left (sub_le_sub h₁ h₂) (show 0 ≤ 2*λ by linarith)
  dsimp [lowNormSq,lowNormMajorant,lowS5,lowC6]
  linarith

theorem lowT_positive {λ ε x : ℝ} (hλ : 189/200 ≤ λ ∧ λ ≤ 1)
    (hε : 0 ≤ ε ∧ ε ≤ 1/50000) (hx : 0 ≤ x ∧ x ≤ 11/10) :
    0 < lowT λ ε x := by
  have hx2 : x^2 ≤ 121/100 := by
    nlinarith [mul_nonneg (show 0 ≤ 11/10-x by linarith) (show 0 ≤ 11/10+x by linarith)]
  have hs : 0 ≤ lowS3 x := by
    dsimp [lowS3]
    nlinarith [mul_nonneg hx.1 (show 0 ≤ 6-x^2 by linarith)]
  have hc : lowC4 x ≤ 1 := by
    dsimp [lowC4]
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 12-x^2 by linarith)]
  have hm := mul_nonneg (show 0 ≤ λ-9/100 by linarith [hλ.1]) hs
  dsimp [lowT,lowU,lowV,lowA0lo]
  linarith [hλ.1,hε.2,hx.1]

theorem low_circle_semantic {λ ε a₀ x : ℝ}
    (hλ : 189/200 ≤ λ ∧ λ ≤ 1) (hε : 0 ≤ ε ∧ ε ≤ 1/50000)
    (ha₀ : lowA0lo ≤ a₀) (hx : 0 ≤ x ∧ x ≤ 11/10)
    (hp : 0 < lowCirclePolynomial λ ε x) :
    91/100 < lowCircleExpression λ ε a₀ x := by
  have hλ0 : 0 ≤ λ := by linarith [hλ.1]
  have hN := lowNormSq_nonneg λ x
  have hV := lowNormMajorant_sound hλ0 hx.1
  have hQ : 0 ≤ lowQ := by norm_num [lowQ]
  have hprod := mul_le_mul_of_nonneg_left hV hQ
  have hT := lowT_positive hλ hε hx
  have hsquare : (Real.sqrt lowQ*Real.sqrt (lowNormSq λ x))^2 = lowQ*lowNormSq λ x := by
    rw [mul_pow,Real.sq_sqrt hQ,Real.sq_sqrt hN]
  have hn : 0 ≤ Real.sqrt lowQ*Real.sqrt (lowNormSq λ x) := by positivity
  have hstrict : Real.sqrt lowQ*Real.sqrt (lowNormSq λ x) < lowT λ ε x := by
    dsimp [lowCirclePolynomial] at hp
    nlinarith
  have hs := Real.sin_ge_sub_cube hx.1
  have hc := cos_upper_four hx.1
  have ha := mul_le_mul_of_nonneg_left ha₀ (show 0 ≤ lowU by norm_num [lowU])
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ λ-9/100 by linarith [hλ.1])
  dsimp [lowCircleExpression,lowT,lowS3,lowC4] at *
  linarith

theorem low_circle_plus {a₀ x : ℝ} (ha₀ : lowA0lo ≤ a₀) (hx : 0 ≤ x ∧ x ≤ 24/25) :
    91/100 < lowCircleExpression (189/200) (1/50000) a₀ x := by
  apply low_circle_semantic (by norm_num) (by norm_num) ha₀ ⟨hx.1,by linarith [hx.2]⟩
  rw [low_circle_plus_identity]
  exact low_low_whole_pair_plus_circle_positive hx

theorem low_circle_minus {a₀ x : ℝ} (ha₀ : lowA0lo ≤ a₀) (hx : 0 ≤ x ∧ x ≤ 11/10) :
    91/100 < lowCircleExpression 1 0 a₀ x := by
  apply low_circle_semantic (by norm_num) (by norm_num) ha₀ hx
  rw [low_circle_minus_identity]
  exact low_low_whole_pair_minus_circle_positive hx

theorem low_endpoint_semantic {λ ε a₁ b₁ L₁ x : ℝ}
    (hλ : 189/200 ≤ λ ∧ λ ≤ 1) (ha : a₁ ≤ lowA1hi)
    (hb : lowB1lo ≤ b₁) (hL : L₁ ≤ lowL1hi)
    (hx : 0 ≤ x ∧ x ≤ Real.pi/2) (hp : 0 < lowEndpointPolynomial λ ε x) :
    91/100 < lowEndpointExpression λ ε a₁ b₁ L₁ x := by
  have hsc := cos_sin_nonneg hx
  have hλ0 : 0 ≤ λ := by linarith [hλ.1]
  have hC : 0 ≤ (λ-lowBeta)/2+λ*lowB1lo := by
    norm_num [lowBeta,lowB1lo]
    linarith [hλ.1]
  have hS : (λ-lowBeta)/2-λ*lowA1hi ≤ 0 := by
    norm_num [lowBeta,lowA1hi]
    linarith [hλ.1]
  have hc₁ := mul_le_mul_of_nonneg_left (cos_lower_six hx.1) hC
  have hc₂ := mul_le_mul_of_nonneg_right
    (add_le_add_left (mul_le_mul_of_nonneg_left hb hλ0) ((λ-lowBeta)/2)) hsc.1
  have hs₁ := mul_le_mul_of_nonpos_left (sin_upper_five hx.1) hS
  have hs₂ := mul_le_mul_of_nonneg_right
    (sub_le_sub_left (mul_le_mul_of_nonneg_left ha hλ0) ((λ-lowBeta)/2)) hsc.2
  dsimp [lowEndpointPolynomial,lowEndpointExpression,lowC6,lowS5] at *
  linarith

theorem low_endpoint_plus {a₁ b₁ L₁ x : ℝ} (ha : a₁ ≤ lowA1hi)
    (hb : lowB1lo ≤ b₁) (hL : L₁ ≤ lowL1hi)
    (hx : 24/25 ≤ x ∧ x ≤ Real.pi/2) :
    91/100 < lowEndpointExpression (189/200) (1/50000) a₁ b₁ L₁ x := by
  apply low_endpoint_semantic (by norm_num) ha hb hL ⟨by linarith [hx.1],hx.2⟩
  rw [low_endpoint_plus_identity]
  exact low_low_whole_pair_plus_endpoint_positive
    ⟨hx.1,by linarith [hx.2,pi_lt_22_over_7]⟩

theorem low_endpoint_minus {a₁ b₁ L₁ x : ℝ} (ha : a₁ ≤ lowA1hi)
    (hb : lowB1lo ≤ b₁) (hL : L₁ ≤ lowL1hi)
    (hx : 11/10 ≤ x ∧ x ≤ Real.pi/2) :
    91/100 < lowEndpointExpression 1 0 a₁ b₁ L₁ x := by
  apply low_endpoint_semantic (by norm_num) ha hb hL ⟨by linarith [hx.1],hx.2⟩
  rw [low_endpoint_minus_identity]
  exact low_low_whole_pair_minus_endpoint_positive
    ⟨hx.1,by linarith [hx.2,pi_lt_22_over_7]⟩

/-- Closed-domain aggregation includes the common cut exactly once whichever
support comparison the caller retains. -/
theorem low_positive_target_plus_chain {a₀ a₁ b₁ L₁ x cost : ℝ}
    (ha₀ : lowA0lo ≤ a₀) (ha : a₁ ≤ lowA1hi) (hb : lowB1lo ≤ b₁) (hL : L₁ ≤ lowL1hi)
    (hx : 0 ≤ x ∧ x ≤ Real.pi/2)
    (hcircle : x ≤ 24/25 → lowCircleExpression (189/200) (1/50000) a₀ x ≤ cost)
    (hendpoint : 24/25 ≤ x → lowEndpointExpression (189/200) (1/50000) a₁ b₁ L₁ x ≤ cost) :
    91/100 < cost := by
  by_cases hcut : x ≤ 24/25
  · exact (low_circle_plus ha₀ ⟨hx.1,hcut⟩).trans_le (hcircle hcut)
  · have hcut' : 24/25 ≤ x := (lt_of_not_ge hcut).le
    exact (low_endpoint_plus ha hb hL ⟨hcut',hx.2⟩).trans_le (hendpoint hcut')

theorem low_positive_target_minus_chain {a₀ a₁ b₁ L₁ x cost : ℝ}
    (ha₀ : lowA0lo ≤ a₀) (ha : a₁ ≤ lowA1hi) (hb : lowB1lo ≤ b₁) (hL : L₁ ≤ lowL1hi)
    (hx : 0 ≤ x ∧ x ≤ Real.pi/2)
    (hcircle : x ≤ 11/10 → lowCircleExpression 1 0 a₀ x ≤ cost)
    (hendpoint : 11/10 ≤ x → lowEndpointExpression 1 0 a₁ b₁ L₁ x ≤ cost) :
    91/100 < cost := by
  by_cases hcut : x ≤ 11/10
  · exact (low_circle_minus ha₀ ⟨hx.1,hcut⟩).trans_le (hcircle hcut)
  · have hcut' : 11/10 ≤ x := (lt_of_not_ge hcut).le
    exact (low_endpoint_minus ha hb hL ⟨hcut',hx.2⟩).trans_le (hendpoint hcut')

end SquaresInCircles.Eight.Arithmetic
