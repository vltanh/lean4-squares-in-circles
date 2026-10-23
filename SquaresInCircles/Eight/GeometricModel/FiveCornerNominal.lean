module

public import SquaresInCircles.Eight.GeometricModel.FiveCornerHighTilt
public import SquaresInCircles.Eight.ExactFamily.GeometricStationary

/-!
# The single polynomial nominal support and global tilt localization

Uncompiled draft. The completed-circle inequality is applied directly to
the five arbitrary points. Its masses and contact weights are one explicit
family on the full sine interval [0,3/10], including the zero E force at
sine zero. No core or sorted-coordinate hypothesis is present.

Sources: HAND_POSITIVE_TILT_NOMINAL_GAP.md and
HAND_FIVE_CORNER_MODEL_SELECTION.md, Section 4.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.GeometricModel.FiveCorner

open Set

theorem dot_le_completed_circle {m q : ℝ} {p F : Point}
    (hm : 0 < m) (hp : normSq p ≤ q) :
    dot F p ≤ m*q+normSq F/(4*m) := by
  have hbound := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*m^2 by positivity)
  have hx := sq_nonneg (F.1-2*m*p.1)
  have hy := sq_nonneg (F.2-2*m*p.2)
  have hmul : (dot F p-m*q)*(4*m) ≤ normSq F := by
    dsimp [normSq, dot] at *
    nlinarith
  have hdiv : dot F p-m*q ≤ normSq F/(4*m) :=
    (le_div_iff₀ (by positivity : 0 < 4*m)).mpr hmul
  linarith

theorem dot_le_completed_circle_or_zero {m q : ℝ} {p F : Point}
    (hm : 0 ≤ m) (hz : m=0 → F=(0,0)) (hp : normSq p ≤ q) :
    dot F p ≤ m*q+normSq F/(4*m) := by
  by_cases hzero : m=0
  · simp [hzero, hz hzero, dot, normSq]
  · exact dot_le_completed_circle (lt_of_le_of_ne hm (Ne.symm hzero)) hp

namespace Nominal

def ceiling : ℝ := 1957767069/500000000
def alpha (s : ℝ) : ℝ := 24/41+(49/100)*s-s^2/20
def beta (s : ℝ) : ℝ := 1-s/20-s^2/6
def delta (s : ℝ) : ℝ := 36/31-(7/10)*s-s^2/16
def epsilon (s : ℝ) : ℝ := 36/31-s+(11/20)*s^2
def mA (s : ℝ) : ℝ := (12/41)/(1+13*s/60)
def mB (s : ℝ) : ℝ := (12/41)/(1-9*s/50)
def mD (s : ℝ) : ℝ := (12/31)/(1+9*s/25)
def mH (s : ℝ) : ℝ := (12/31)/(1+49*s/100)
def mE (s : ℝ) : ℝ := (3*s/10)/(1+4*s/5)
def mass (s : ℝ) : Fin 5 → ℝ := ![mA s,mB s,mD s,mE s,mH s]
def massSum (s : ℝ) : ℝ := ∑ i : Fin 5, mass s i
def forces (t : ℝ) : Fin 5 → Point :=
  spanForces t (alpha (Real.sin t)) (beta (Real.sin t))
    (delta (Real.sin t)) (epsilon (Real.sin t))
def demand (t : ℝ) : ℝ :=
  spanDemand t (alpha (Real.sin t)) (beta (Real.sin t))
    (delta (Real.sin t)) (epsilon (Real.sin t))
def energy (t : ℝ) : ℝ :=
  ∑ i : Fin 5, normSq (forces t i)/(4*mass (Real.sin t) i)
def gap (q t : ℝ) : ℝ := demand t-energy t-q*massSum (Real.sin t)

theorem denominator_bounds {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 < 1+13*s/60 ∧ 0 < 1-9*s/50 ∧
    0 < 1+9*s/25 ∧ 0 < 1+49*s/100 ∧ 0 < 1+4*s/5 := by
  constructor <;> try constructor <;> try constructor <;> try constructor <;>
    linarith [hs.1, hs.2]

theorem weights_pos {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 < alpha s ∧ 0 < beta s ∧ 0 < delta s ∧ 0 < epsilon s := by
  have hs₂ : s^2 ≤ 9/100 := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  dsimp [alpha, beta, delta, epsilon]
  constructor <;> try constructor <;> try constructor <;>
    nlinarith [hs.1, hs.2, sq_nonneg s]

theorem mass_nonneg {s : ℝ} (hs : s ∈ Icc 0 (3/10)) (i : Fin 5) :
    0 ≤ mass s i := by
  have hs₀ := hs.1
  obtain ⟨hA, hB, hD, hH, hE⟩ := denominator_bounds hs
  fin_cases i <;> simp only [mass, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals
    dsimp [mA, mB, mD, mH, mE]
    positivity

theorem mass_pos {s : ℝ} (hs : s ∈ Icc 0 (3/10)) (hs₀ : 0 < s)
    (i : Fin 5) : 0 < mass s i := by
  obtain ⟨hA, hB, hD, hH, hE⟩ := denominator_bounds hs
  fin_cases i <;> simp only [mass, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals
    dsimp [mA, mB, mD, mH, mE]
    positivity

theorem mass_sum_nonneg {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 ≤ massSum s :=
  Finset.sum_nonneg (fun i _ => mass_nonneg hs i)

theorem mass_force_zero {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4))
    (hs : Real.sin t ∈ Icc 0 (3/10)) (i : Fin 5)
    (hz : mass (Real.sin t) i=0) : forces t i=(0,0) := by
  by_cases hs₀ : Real.sin t=0
  · have hc : Real.cos t=1 := by
      have hunit := Real.sin_sq_add_cos_sq t
      have hc₀ := (angle_trig ht).1
      rw [hs₀] at hunit
      nlinarith
    fin_cases i <;>
      simp [mass, mA, mB, mD, mE, mH, hs₀] at hz
    simp [forces, spanForces, hs₀, hc, delta, epsilon]
  · have hp := mass_pos hs (lt_of_le_of_ne hs.1 (Ne.symm hs₀)) i
    linarith

/-- The nominal stress is valid on arbitrary original point coordinates. -/
theorem gap_nonpos_of_spans {p : FiveCorner} {R : ℝ}
    (hp : p.spans) (hfit : p.fits R) (hs : Real.sin p.angle ≤ 3/10) :
    gap (R^2) p.angle ≤ 0 := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : p.angle ∈ Icc 0 (Real.pi/4) := ⟨h.angle_lower, h.angle_upper⟩
  have hs' : Real.sin p.angle ∈ Icc 0 (3/10) := ⟨(angle_trig ht).2.2.1, hs⟩
  obtain ⟨ha, hb, hd, he⟩ := weights_pos hs'
  have hspan := weighted_spans hp ha.le hb.le hd.le he.le
  have hcircle := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 5))) =>
    dot_le_completed_circle_or_zero (mass_nonneg hs' i)
      (mass_force_zero ht hs' i) (hfit.2 i))
  change (∑ i : Fin 5, dot (forces p.angle i) (p.point i)) ≤
    ∑ i : Fin 5, (mass (Real.sin p.angle) i*R^2+
      normSq (forces p.angle i)/(4*mass (Real.sin p.angle) i)) at hcircle
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hcircle
  change demand p.angle ≤ ∑ i : Fin 5, dot (forces p.angle i) (p.point i) at hspan
  dsimp [gap, energy, massSum]
  linarith

theorem gap_radius_identity (q r t : ℝ) :
    gap q t=gap r t+(r-q)*massSum (Real.sin t) := by
  dsimp [gap]
  ring

def T4 (x : ℝ) : ℝ := 1-x+x^2-x^3+x^4
def B4 (x : ℝ) : ℝ := 1+x+x^2+x^3+(500/473)*x^4
def massUpper (s : ℝ) : ℝ :=
  (12/41)*(T4 (13*s/60)+B4 (9*s/50)) +
  (12/31)*(T4 (9*s/25)+T4 (49*s/100)) +
  (3*s/10)*T4 (4*s/5)

theorem inverse_le_T4 {x : ℝ} (hx : 0 ≤ x) : 1/(1+x) ≤ T4 x := by
  rw [div_le_iff₀ (by linarith : 0 < 1+x)]
  have hpow := pow_nonneg hx 5
  dsimp [T4]
  nlinarith

theorem inverse_le_B4 {x : ℝ} (hx : x ∈ Icc 0 (27/500)) :
    1/(1-x) ≤ B4 x := by
  rw [div_le_iff₀ (by linarith [hx.2] : 0 < 1-x)]
  have hp := mul_nonneg (pow_nonneg hx.1 4)
    (show 0 ≤ 27-500*x by linarith [hx.2])
  dsimp [B4]
  nlinarith

theorem mass_sum_le_upper {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    massSum s ≤ massUpper s := by
  have hs₀ := hs.1
  have hA := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 13*s/60 by positivity)) (by norm_num : (0:ℝ) ≤ 12/41)
  have hB := mul_le_mul_of_nonneg_left
    (inverse_le_B4 (show 9*s/50 ∈ Icc 0 (27/500) by
      constructor <;> linarith [hs.1, hs.2])) (by norm_num : (0:ℝ) ≤ 12/41)
  have hD := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 9*s/25 by positivity)) (by norm_num : (0:ℝ) ≤ 12/31)
  have hH := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 49*s/100 by positivity)) (by norm_num : (0:ℝ) ≤ 12/31)
  have hE := mul_le_mul_of_nonneg_left
    (inverse_le_T4 (show 0 ≤ 4*s/5 by positivity)) (show 0 ≤ 3*s/10 by positivity)
  simp only [massSum, mass, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mA, mB, mD, mE, mH, massUpper]
  simp only [mul_one_div] at hA hB hD hH hE
  linarith

def chiUpper (s : ℝ) : ℝ := s^2/2+s^4/8+s^6/14

theorem cosine_chord {s c : ℝ} (hs : s ∈ Icc 0 (3/10))
    (hc : 0 ≤ c) (hunit : c^2+s^2=1) : 1-c ≤ chiUpper s := by
  let x := s^2
  let P := 1-x/2-x^2/8-x^3/14
  have hx : x ∈ Icc 0 (9/100) := by
    dsimp [x]
    constructor
    · positivity
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hx₂ := pow_le_pow_left₀ hx.1 hx.2 2
  have hx₃ := pow_le_pow_left₀ hx.1 hx.2 3
  have hP : 0 < P := by
    dsimp [P]
    nlinarith [hx.1, hx.2]
  have hbracket : 0 ≤ 56-273*x-56*x^2-16*x^3 := by
    nlinarith [hx.2]
  have hid : 1-x-P^2=x^3*(56-273*x-56*x^2-16*x^3)/3136 := by
    dsimp [P]
    ring
  have hp := div_nonneg (mul_nonneg (pow_nonneg hx.1 3) hbracket)
    (by norm_num : (0:ℝ) ≤ 3136)
  have hPc : P ≤ c := by
    dsimp [x] at hid
    nlinarith
  dsimp [P, x, chiUpper] at hPc ⊢
  nlinarith

def polynomial (s : ℝ) : ℝ :=
  38726637/9929687500-(79/1250)*s+(51/200)*s^2-s^3/100-
    (27/100)*s^4-(3/10)*s^5

/-- Polynomial obtained after the circle-mass and cosine majorants. -/
def lowerPolynomial (s : ℝ) : ℝ :=
  3+2*alpha s+3*beta s+2*delta s+epsilon s+epsilon s*s-ceiling*massUpper s-
  (1+(alpha s)^2-2*alpha s*s)*(41/12)*(1+13*s/60)/4-
  ((beta s)^2+(alpha s)^2)*(41/12)*(1-9*s/50)/4-
  ((delta s)^2+(beta s)^2)*(31/12)*(1+9*s/25)/4-
  ((epsilon s)^2+1)*(31/12)*(1+49*s/100)/4-
  s*(5/6)*(3/10-49*s/80)^2*(1+4*s/5)-
  chiUpper s-
  (5/3)*delta s*epsilon s*(1+4*s/5)*(s/2+s^3/8+s^5/14)

theorem force_norm (t : ℝ) (i : Fin 5) :
    normSq (forces t i) =
      ![1+alpha (Real.sin t)^2-2*alpha (Real.sin t)*Real.sin t,
        beta (Real.sin t)^2+alpha (Real.sin t)^2,
        delta (Real.sin t)^2+beta (Real.sin t)^2,
        (delta (Real.sin t)-epsilon (Real.sin t))^2+
          2*delta (Real.sin t)*epsilon (Real.sin t)*(1-Real.cos t),
        epsilon (Real.sin t)^2+1] i := by
  fin_cases i <;>
    simp only [forces, spanForces, Matrix.cons_val_zero, Matrix.cons_val_succ, normSq]
  · linear_combination Real.sin_sq_add_cos_sq t
  · ring
  · ring
  · linear_combination epsilon (Real.sin t)^2 * Real.sin_sq_add_cos_sq t
  · linear_combination (1+epsilon (Real.sin t)^2) * Real.sin_sq_add_cos_sq t

theorem gap_formula {t : ℝ} (hs : Real.sin t ∈ Icc 0 (3/10))
    (hs₀ : 0 < Real.sin t) :
    gap ceiling t =
      3+2*alpha (Real.sin t)+3*beta (Real.sin t)+2*delta (Real.sin t)+
      epsilon (Real.sin t)+epsilon (Real.sin t)*Real.sin t-
      ceiling*massSum (Real.sin t)-
      (1+alpha (Real.sin t)^2-2*alpha (Real.sin t)*Real.sin t)/(4*mA (Real.sin t))-
      (beta (Real.sin t)^2+alpha (Real.sin t)^2)/(4*mB (Real.sin t))-
      (delta (Real.sin t)^2+beta (Real.sin t)^2)/(4*mD (Real.sin t))-
      (epsilon (Real.sin t)^2+1)/(4*mH (Real.sin t))-
      (delta (Real.sin t)-epsilon (Real.sin t))^2/(4*mE (Real.sin t))-
      (1-Real.cos t)*(1+delta (Real.sin t)*epsilon (Real.sin t)/(2*mE (Real.sin t))) := by
  have hA := ne_of_gt (mass_pos hs hs₀ 0)
  have hB := ne_of_gt (mass_pos hs hs₀ 1)
  have hD := ne_of_gt (mass_pos hs hs₀ 2)
  have hE := ne_of_gt (mass_pos hs hs₀ 3)
  have hH := ne_of_gt (mass_pos hs hs₀ 4)
  change mA (Real.sin t) ≠ 0 at hA
  change mB (Real.sin t) ≠ 0 at hB
  change mD (Real.sin t) ≠ 0 at hD
  change mE (Real.sin t) ≠ 0 at hE
  change mH (Real.sin t) ≠ 0 at hH
  simp only [gap, demand, energy, force_norm, spanDemand,
    Fin.sum_univ_succ, mass, Matrix.cons_val_zero, Matrix.cons_val_succ]
  field_simp [hA, hB, hD, hE, hH]
  ring

theorem lowerPolynomial_bound {t : ℝ} (ht : t ∈ Icc 0 (Real.pi/4))
    (hs : Real.sin t ∈ Icc 0 (3/10)) :
    lowerPolynomial (Real.sin t) ≤ gap ceiling t := by
  by_cases hs₀ : Real.sin t=0
  · have hc : Real.cos t=1 := by
      have hu := Real.sin_sq_add_cos_sq t
      rw [hs₀] at hu
      nlinarith [(angle_trig ht).1]
    norm_num [lowerPolynomial, gap, demand, energy, forces, spanDemand, spanForces,
      massSum, mass, mA, mB, mD, mE, mH, alpha, beta, delta, epsilon,
      chiUpper, massUpper, T4, B4, ceiling, hs₀, hc, Fin.sum_univ_succ, normSq]
  · have hsp : 0 < Real.sin t := lt_of_le_of_ne hs.1 (Ne.symm hs₀)
    have hM := mass_sum_le_upper hs
    have hχ := cosine_chord hs (angle_trig ht).1.le
      (by nlinarith [Real.sin_sq_add_cos_sq t])
    obtain ⟨-, -, hd, he⟩ := weights_pos hs
    have hE : 0 < mE (Real.sin t) := mass_pos hs hsp 3
    have hχc : 0 ≤ 1+delta (Real.sin t)*epsilon (Real.sin t)/(2*mE (Real.sin t)) :=
      by positivity
    have hχm := mul_le_mul_of_nonneg_right hχ hχc
    have hMq := mul_le_mul_of_nonneg_left hM (show 0 ≤ ceiling by norm_num [ceiling])
    have hden := denominator_bounds hs
    have hpoly :
        lowerPolynomial (Real.sin t) =
        3+2*alpha (Real.sin t)+3*beta (Real.sin t)+2*delta (Real.sin t)+
        epsilon (Real.sin t)+epsilon (Real.sin t)*Real.sin t-
        ceiling*massUpper (Real.sin t)-
        (1+alpha (Real.sin t)^2-2*alpha (Real.sin t)*Real.sin t)/(4*mA (Real.sin t))-
        (beta (Real.sin t)^2+alpha (Real.sin t)^2)/(4*mB (Real.sin t))-
        (delta (Real.sin t)^2+beta (Real.sin t)^2)/(4*mD (Real.sin t))-
        (epsilon (Real.sin t)^2+1)/(4*mH (Real.sin t))-
        (delta (Real.sin t)-epsilon (Real.sin t))^2/(4*mE (Real.sin t))-
        chiUpper (Real.sin t)*
          (1+delta (Real.sin t)*epsilon (Real.sin t)/(2*mE (Real.sin t))) := by
      dsimp [lowerPolynomial, mA, mB, mD, mH, mE, chiUpper, delta, epsilon]
      field_simp [hs₀, ne_of_gt hden.1, ne_of_gt hden.2.1,
        ne_of_gt hden.2.2.1, ne_of_gt hden.2.2.2.1, ne_of_gt hden.2.2.2.2]
      ring
    rw [hpoly, gap_formula hs hsp]
    linarith

/-- Exact coefficient comparison for one polynomial on the whole interval.
The coefficients are expanded by ring normalization, not selected by boxes. -/
theorem polynomial_bound {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    polynomial s ≤ lowerPolynomial s := by
  have hs₀ := hs.1
  have hcoeff :
      0 ≤ lowerPolynomial s-polynomial s-
        (s*(26-9*s)/1000000+(27/10000)*s^3+
          (s^4/1000)*(56-132*s-86*s^2-77*s^4)) := by
    dsimp [lowerPolynomial, polynomial, alpha, beta, delta, epsilon,
      massUpper, T4, B4, chiUpper, ceiling]
    ring_nf
    positivity
  have hs₂ : s^2 ≤ 9/100 := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hs₄ : s^4 ≤ 81/10000 := by
    have hproduct := mul_nonneg (sub_nonneg.mpr hs₂)
      (show 0 ≤ (9/100:ℝ)+s^2 by positivity)
    nlinarith
  have hb : 0 ≤ 56-132*s-86*s^2-77*s^4 := by nlinarith [hs.2]
  have h₁ : 0 ≤ s*(26-9*s)/1000000 := by
    apply div_nonneg (mul_nonneg hs.1 (by linarith [hs.2])) (by norm_num)
  have h₂ : 0 ≤ (27/10000:ℝ)*s^3 := by positivity
  have h₃ : 0 ≤ (s^4/1000)*(56-132*s-86*s^2-77*s^4) := by positivity
  linarith

theorem gap_ge_polynomial {q t : ℝ} (hq : q ≤ ceiling)
    (ht : t ∈ Icc 0 (Real.pi/4)) (hs : Real.sin t ∈ Icc 0 (3/10)) :
    polynomial (Real.sin t) ≤ gap q t := by
  have hp := (polynomial_bound hs).trans (lowerPolynomial_bound ht hs)
  have hm := mul_nonneg (sub_nonneg.mpr hq) (mass_sum_nonneg hs)
  rw [gap_radius_identity q ceiling t]
  linarith

def polynomialD (s : ℝ) : ℝ :=
  -79/1250+(51/100)*s-(3/100)*s^2-(27/25)*s^3-(3/2)*s^4
def polynomialDD (s : ℝ) : ℝ :=
  51/100-(3/50)*s-(81/25)*s^2-6*s^3

theorem polynomial_derivative (s : ℝ) :
    HasDerivAt polynomial (polynomialD s) s := by
  have h := (((((hasDerivAt_const s (38726637/9929687500:ℝ)).sub
      ((hasDerivAt_id s).const_mul (79/1250))).add
      (((hasDerivAt_id s).pow 2).const_mul (51/200))).sub
      (((hasDerivAt_id s).pow 3).div_const 100)).sub
      (((hasDerivAt_id s).pow 4).const_mul (27/100))).sub
      (((hasDerivAt_id s).pow 5).const_mul (3/10))
  convert h using 1 <;> dsimp [polynomial, polynomialD] <;> ring

theorem polynomial_second (s : ℝ) :
    HasDerivAt polynomialD (polynomialDD s) s := by
  have h := ((((hasDerivAt_const s (-79/1250:ℝ)).add
      ((hasDerivAt_id s).const_mul (51/100))).sub
      (((hasDerivAt_id s).pow 2).const_mul (3/100))).sub
      (((hasDerivAt_id s).pow 3).const_mul (27/25))).sub
      (((hasDerivAt_id s).pow 4).const_mul (3/2))
  convert h using 1 <;> dsimp [polynomialD, polynomialDD] <;> ring

theorem polynomial_left_positive {s : ℝ} (hs : s ∈ Icc 0 (1/10)) :
    0 < polynomial s := by
  have hmono : AntitoneOn polynomial (Icc 0 (1/10)) :=
    antiOn_of_hasDeriv_nonpos (by dsimp [polynomial]; fun_prop)
      (fun x _ => polynomial_derivative x) (fun x hx => by
        dsimp [polynomialD]
        nlinarith [hx.2, sq_nonneg x, pow_nonneg hx.1.le 3, pow_nonneg hx.1.le 4])
  have hp : 0 < polynomial (1/10) := by norm_num [polynomial]
  exact hp.trans_le (hmono hs (by norm_num) hs.2)

theorem polynomial_curvature_positive {s : ℝ} (hs : s ∈ Icc 0 (3/10)) :
    0 < polynomialDD s := by
  have hs₂ := pow_le_pow_left₀ hs.1 hs.2 2
  have hs₃ := pow_le_pow_left₀ hs.1 hs.2 3
  dsimp [polynomialDD]
  nlinarith [hs.2]

theorem polynomial_right_positive {s : ℝ} (hs : s ∈ Icc (79/500) (3/10)) :
    0 < polynomial s := by
  have hmonoD : MonotoneOn polynomialD (Icc 0 (3/10)) :=
    monoOn_of_hasDeriv_nonneg (by dsimp [polynomialD]; fun_prop)
      (fun x _ => polynomial_second x)
      (fun x hx => (polynomial_curvature_positive ⟨hx.1.le, hx.2.le⟩).le)
  have hD₀ : 0 < polynomialD (3/20) := by norm_num [polynomialD]
  have hmono : MonotoneOn polynomial (Icc (3/20) (3/10)) :=
    monoOn_of_hasDeriv_nonneg (by dsimp [polynomial]; fun_prop)
      (fun x _ => polynomial_derivative x) (fun x hx => by
        have h := hmonoD (by norm_num) ⟨by linarith [hx.1], hx.2.le⟩ hx.1.le
        linarith)
  have hp : 0 < polynomial (79/500) := by norm_num [polynomial]
  exact hp.trans_le (hmono (by norm_num) ⟨by linarith [hs.1], hs.2⟩ hs.1)

theorem sine_localization {p : FiveCorner} {R : ℝ}
    (hp : p.spans) (hfit : p.fits R) (hq : R^2 ≤ ceiling) :
    1/10 < Real.sin p.angle ∧ Real.sin p.angle < 79/500 := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : p.angle ∈ Icc 0 (Real.pi/4) := ⟨h.angle_lower, h.angle_upper⟩
  have hs₀ := (angle_trig ht).2.2.1
  have hs₁ : Real.sin p.angle < 3/10 := by
    by_contra! hs
    exact HighTilt.exclusion hp hfit
      (hq.trans (by norm_num [ceiling, HighTilt.ceiling])) hs
  have hgap := gap_nonpos_of_spans hp hfit hs₁.le
  have hpoly := gap_ge_polynomial hq ht ⟨hs₀, hs₁.le⟩
  constructor
  · by_contra! hs
    have hh := polynomial_left_positive ⟨hs₀, hs⟩
    linarith
  · by_contra! hs
    have hh := polynomial_right_positive ⟨hs, hs₁.le⟩
    linarith

theorem tilt_localization {p : FiveCorner} {R : ℝ}
    (hp : p.spans) (hfit : p.fits R) (hq : R^2 ≤ ceiling) :
    p.angle ∈ ExactFamily.FiveCornerGeometry.tiltInterval := by
  have h := (spans_iff_spanBounds p).1 hp
  have ht : p.angle ∈ Icc 0 (Real.pi/4) := ⟨h.angle_lower, h.angle_upper⟩
  obtain ⟨hsl, hsu⟩ := sine_localization hp hfit hq
  have hc := (angle_trig ht).1
  have hu := Real.sin_sq_add_cos_sq p.angle
  have hs₀ : 0 ≤ Real.sin p.angle := by linarith
  have hs₂ : Real.sin p.angle ^ 2 < (79/500:ℝ)^2 := by
    exact ExactFamily.FiveCornerGeometry.square_strict_mono_nonneg hs₀ hsu
  have htan : Real.sin p.angle / Real.cos p.angle < 1/5 := by
    rw [div_lt_iff₀ hc]
    nlinarith
  have hpos : 0 < p.angle := by
    by_contra! hh
    have he : p.angle=0 := le_antisymm hh h.angle_lower
    rw [he, Real.sin_zero] at hsl
    norm_num at hsl
  refine ⟨hpos, ?_⟩
  by_contra! hh
  have hmem : p.angle ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [h.angle_lower, h.angle_upper, Real.pi_pos]
  have hm := Real.strictMonoOn_tan.monotoneOn
    (Real.arctan_mem_Ioo (1/5:ℝ)) hmem hh
  rw [Real.tan_arctan, Real.tan_eq_sin_div_cos] at hm
  linarith

end Nominal
end SquaresInCircles.Eight.GeometricModel.FiveCorner
