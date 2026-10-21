module

public import SquaresInCircles.Eight.TableFree.NegativeCaptureData

/-!
# The eight exact cleared polynomials for canonical negative capture

Uncompiled reconstruction of sections 6--7 of
HAND_G5_NEGATIVE_CANONICAL_SMALL_ERROR_CAPTURE.md.

All operations below are ordinary rational polynomial operations.  The
two approximate short-angle constants remain separate: their squared
sum is never replaced by one.  The secant endpoint is cleared by the
actual factor 1-s².  Whole-polynomial coefficient sums, followed by
finite derivative integration, give positivity on both full bands.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.NegativeCapturePolynomials
open CenteredMonomialBounds NegativeCaptureData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def otherA (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 1*mass b j 2*mass b j 3*mass b j 4
def otherB (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 2*mass b j 3*mass b j 4
def otherD (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 3*mass b j 4
def otherH (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 4
def otherE (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 3
def denominator (b : Band) (j : Fin 4) : ℚ[X] :=
  C 4*mass b j 0*mass b j 1*mass b j 2*mass b j 3*mass b j 4
def totalMass (b : Band) (j : Fin 4) : ℚ[X] :=
  mass b j 0+mass b j 1+mass b j 2+mass b j 3+X*mass b j 4
def scale (j : Fin 4) : ℚ[X] := if j=1 then 1-X^2 else 1

def endpointConstant (j : Fin 4) : ℚ[X] :=
  if j=0 ∨ j=1 then C 2 else if j=2 then
    C (chi+1)+C sigma*X else C (1+(1+K*sigma)/chi)+C sigma*X
def endpointCosine (j : Fin 4) : ℚ[X] :=
  if j=0 then 1 else if j=1 then 0 else C chi
def secantSquare (j : Fin 4) : ℚ[X] := if j=3 then C (1/chi^2) else 1

def base (b : Band) (j : Fin 4) : ℚ[X] :=
  C 3+C 2*aP b+C eta+fP b+C (2*k)*X+fP b*X-
    C Q*totalMass b j-C (delta j)+endpointConstant j
def normA (b : Band) (j : Fin 4) : ℚ[X] :=
  if j=0 then 1+(aP b+C eta)^2-C 2*(aP b+C eta)*X
  else if j=2 then C (chi^2+sigma^2)+(aP b+C eta)^2-
    C (2*sigma)*(aP b+C eta)
  else 1+(aP b+C eta)^2
def normB (b : Band) (j : Fin 4) : ℚ[X] :=
  if j=0 ∨ j=1 then 1+(aP b)^2
  else C (chi^2+sigma^2)+(aP b)^2-C (2*chi)*aP b*X
def normBCosine (b : Band) (j : Fin 4) : ℚ[X] :=
  if j=0 ∨ j=1 then 0 else C (2*sigma)*aP b

/-- Constant term in the exact quotient c²=1-s².  Every mass quotient
has already been written as the product of the other four masses. -/
def constantNumerator (b : Band) (j : Fin 4) : ℚ[X] :=
  denominator b j*scale j*base b j-
    otherA b j*scale j*normA b j-
    otherB b j*scale j*normB b j-
    otherD b j*scale j*((fP b)^2+1)-
    otherH b j*(scale j*((fP b)^2*(1-X^2)+C (k^2)*X^2)+secantSquare j)-
    otherE b j*scale j*X*((fP b)^2+C (k^2))

/-- Coefficient of the original cosine after clearing the secant. -/
def cosineNumerator (b : Band) (j : Fin 4) : ℚ[X] :=
  denominator b j*(scale j*(C 2*fP b+endpointCosine j)+
    if j=1 then 1+C K*X else 0)-
    otherB b j*scale j*normBCosine b j-
    otherH b j*scale j*C (2*k)*fP b*X

def cosineSix : ℚ[X] := 1-C (1/2)*X^2-C (1/8)*X^4-C (1/16)*X^6
def cosineReserve : Band → ℚ | .low => 3/50 | .high => 1/20
def P (b : Band) (j : Fin 4) : ℚ[X] :=
  constantNumerator b j+cosineNumerator b j*cosineSix-
    C (cosineReserve b/20)*X^8

def pivot (j : Fin 4) : ℚ := ![47/400,1/10,233/2000,67/500] j

theorem cosine_series : ∀b j,
    translated (lo b) (cosineNumerator b j)=
      series 26 (translated (lo b) (cosineNumerator b j)) := by
  decide

theorem cosine_coefficients : ∀b j,
    upperOn 26 (lo b) (hi b) (cosineNumerator b j)<cosineReserve b := by
  decide

theorem polynomial_series : ∀b j,
    translated (mid b) (P b j)=series 26 (translated (mid b) (P b j)) ∧
    translated (mid b) (P b j).derivative=
      series 26 (translated (mid b) (P b j).derivative) ∧
    translated (mid b) (P b j).derivative.derivative=
      series 26 (translated (mid b) (P b j).derivative.derivative) := by
  decide

theorem low_curvature_coefficients : ∀j : Fin 4, j≠1 →
    (1/200:ℚ)<lowerOn 26 (mid .low) (rad .low) (P .low j).derivative.derivative := by
  decide

theorem low_tangent_values : ∀j : Fin 4, j≠1 →
    (1/200000:ℚ)<(P .low j).eval (pivot j) ∧
      |(P .low j).derivative.eval (pivot j)|<1/100000 := by
  decide

theorem low_secant_coefficients :
    (1/40000:ℚ)<lowerOn 26 (mid .low) (rad .low) (P .low 1) := by
  decide

theorem high_growth_coefficients : ∀j : Fin 4, j≠1 →
    (-1/250000:ℚ)<lowerOn 26 (mid .high) (rad .high) (P .high j).derivative := by
  decide

theorem high_start_values : ∀j : Fin 4, j≠1 →
    (3/500000:ℚ)<(P .high j).eval (7/50) := by
  decide

theorem high_secant_coefficients :
    (1/100000:ℚ)<lowerOn 26 (mid .high) (rad .high) (P .high 1) := by
  decide

theorem rational_eval (p : ℚ[X]) (r : ℚ) :
    aeval (r:ℝ) p=(p.eval r:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [Polynomial.aeval_monomial,Polynomial.eval_monomial]

theorem cosine_upper {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 4) :
    aeval s (cosineNumerator b j)<(cosineReserve b:ℝ) := by
  have hb := interval_upper (cosine_series b j) hs
  have hn : (upperOn 26 (lo b) (hi b) (cosineNumerator b j):ℝ)<(cosineReserve b:ℝ) := by
    exact_mod_cast cosine_coefficients b j
  exact hb.trans_lt hn

theorem low_curvature {s : ℝ} (hs : s∈domain .low) {j : Fin 4} (hj : j≠1) :
    (1/200:ℝ)<aeval s (P .low j).derivative.derivative := by
  have hb := interval_lower (polynomial_series .low j).2.2
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc : (1/200:ℝ)<
      (lowerOn 26 (mid .low) (rad .low) (P .low j).derivative.derivative:ℝ) := by
    exact_mod_cast low_curvature_coefficients j hj
  exact hc.trans_le hb

/-- A complete-square tangent bound on the full first sine interval. -/
theorem low_ordinary_positive {s : ℝ} (hs : s∈domain .low) {j : Fin 4} (hj : j≠1) :
    (499/100000000:ℝ)<aeval s (P .low j) := by
  have hp : (pivot j:ℝ)∈Icc (1499/100000:ℝ) (7/50) := by
    fin_cases j <;> norm_num [pivot]
  have hh := second_derivative_tangent_lower
    (f := fun x : ℝ => aeval x (P .low j))
    (df := fun x : ℝ => aeval x (P .low j).derivative)
    (ddf := fun x : ℝ => aeval x (P .low j).derivative.derivative)
    (l := 1499/100000) (h := 7/50) (x₀ := (pivot j:ℝ)) (x := s) (κ := 1/200)
    (fun x _ => aeval_hasDerivAt _ x) (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (low_curvature hx hj).le) hp hs
  have hv : (1/200000:ℝ)<aeval (pivot j:ℝ) (P .low j) := by
    rw [rational_eval]
    exact_mod_cast (low_tangent_values j hj).1
  have hd : |aeval (pivot j:ℝ) (P .low j).derivative|<1/100000 := by
    rw [rational_eval]
    exact_mod_cast (low_tangent_values j hj).2
  have hd2 : (aeval (pivot j:ℝ) (P .low j).derivative)^2<1/10000000000 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hd
    nlinarith
  have hsq := sq_nonneg
    (s-(pivot j:ℝ)+200*aeval (pivot j:ℝ) (P .low j).derivative)
  nlinarith

theorem low_secant_positive {s : ℝ} (hs : s∈domain .low) :
    (1/40000:ℝ)<aeval s (P .low 1) := by
  have hb := interval_lower (polynomial_series .low 1).1
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hn : (1/40000:ℝ)<(lowerOn 26 (mid .low) (rad .low) (P .low 1):ℝ) := by
    exact_mod_cast low_secant_coefficients
  exact hn.trans_le hb

theorem high_growth {s : ℝ} (hs : s∈domain .high) {j : Fin 4} (hj : j≠1) :
    (-1/250000:ℝ)<aeval s (P .high j).derivative := by
  have hb := interval_lower (polynomial_series .high j).2.1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hc : (-1/250000:ℝ)<
      (lowerOn 26 (mid .high) (rad .high) (P .high j).derivative:ℝ) := by
    exact_mod_cast high_growth_coefficients j hj
  exact hc.trans_le hb

theorem high_ordinary_positive {s : ℝ} (hs : s∈domain .high) {j : Fin 4} (hj : j≠1) :
    (137/25000000:ℝ)<aeval s (P .high j) := by
  have hh := derivative_reserve
    (f := fun x : ℝ => aeval x (P .high j))
    (df := fun x : ℝ => aeval x (P .high j).derivative)
    (l := (7/50:ℝ)) (u := 27/100) (x := 7/50) (y := s) (k := -1/250000)
    (fun x _ => (aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
    (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (high_growth (Ioo_subset_Icc_self hx) hj).le)
    (by norm_num) hs hs.1
  have hv : (3/500000:ℝ)<aeval (7/50:ℝ) (P .high j) := by
    rw [show (7/50:ℝ)=((7/50:ℚ):ℝ) by norm_num,rational_eval]
    exact_mod_cast high_start_values j hj
  have hs' : s≤27/100 := hs.2
  linarith

theorem high_secant_positive {s : ℝ} (hs : s∈domain .high) :
    (1/100000:ℝ)<aeval s (P .high 1) := by
  have hb := interval_lower (polynomial_series .high 1).1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hn : (1/100000:ℝ)<(lowerOn 26 (mid .high) (rad .high) (P .high 1):ℝ) := by
    exact_mod_cast high_secant_coefficients
  exact hn.trans_le hb

/-- All four geometric vertices are positive on both full sine bands. -/
theorem polynomial_positive {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 4) :
    0<aeval s (P b j) := by
  cases b
  · by_cases hj : j=1
    · subst j
      exact lt_trans (by norm_num) (low_secant_positive hs)
    · exact lt_trans (by norm_num) (low_ordinary_positive hs hj)
  · by_cases hj : j=1
    · subst j
      exact lt_trans (by norm_num) (high_secant_positive hs)
    · exact lt_trans (by norm_num) (high_ordinary_positive hs hj)

end SquaresInCircles.Eight.TableFree.NegativeCapturePolynomials
