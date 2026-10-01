import SquaresInCircles.Six.Analytic.RootCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The length of a rotating sum

For two vectors of lengths `a` and `b`, one fixed and one turning with `x`, the
squared length `L²` of their sum is `P + Q cos x + T sin x` with `P = a² + b²`
and `Q² + T² = 4a²b²`. Where `L > 0`, the second derivative of `-R L` is
`R (L⁴ - (a² - b²)²)/(4L³)`, which is at most `R ab/(a + b)`, because
`4abL³ - (a + b)(L⁴ - (a² - b²)²)` is `a + b - L` times a polynomial with
nonnegative terms. When `a ≤ b` and `L² ≤ b² - a²` the second derivative is
nonpositive.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

def harmonicArg (P Q T x : ℝ) : ℝ := P+Q*Real.cos x+T*Real.sin x

def harmonicRoot (R P Q T x : ℝ) : ℝ := -R*Real.sqrt (harmonicArg P Q T x)

def harmonicRootD (R P Q T x : ℝ) : ℝ :=
  -R*(-Q*Real.sin x+T*Real.cos x)/(2*Real.sqrt (harmonicArg P Q T x))

def harmonicCurvature (R P Q T x : ℝ) : ℝ :=
  let z := Q*Real.cos x+T*Real.sin x
  R*(z^2+2*P*z+Q^2+T^2)/(4*(P+z)*Real.sqrt (P+z))

lemma harmonicRoot_deriv {R P Q T x : ℝ} (hx : 0<harmonicArg P Q T x) :
    HasDerivAt (harmonicRoot R P Q T) (harmonicRootD R P Q T x) x := by
  have hd : HasDerivAt (harmonicArg P Q T) (-Q*Real.sin x+T*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul Q).add
      ((Real.hasDerivAt_sin x).const_mul T)).const_add P) using 1
    · funext y
      simp only [harmonicArg,Pi.add_apply,add_assoc]
    · ring
  have hroot := hd.sqrt (ne_of_gt hx)
  convert hroot.const_mul (-R) using 1
  · rfl
  · simp only [harmonicRootD]
    ring

lemma harmonicRoot_second {R P Q T x : ℝ} (hx : 0<harmonicArg P Q T x) :
    HasDerivAt (harmonicRootD R P Q T) (harmonicCurvature R P Q T x) x := by
  have hf : HasDerivAt (harmonicArg P Q T) (-Q*Real.sin x+T*Real.cos x) x := by
    convert ((((Real.hasDerivAt_cos x).const_mul Q).add
      ((Real.hasDerivAt_sin x).const_mul T)).const_add P) using 1
    · funext y
      simp only [harmonicArg,Pi.add_apply,add_assoc]
    · ring
  have hd : HasDerivAt (fun y => -Q*Real.sin y+T*Real.cos y)
      (-Q*Real.cos x-T*Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-Q)).add
      ((Real.hasDerivAt_cos x).const_mul T) using 1
    ring
  have hh := hasDerivAt_negative_sqrt (r := R) hf hd hx
  have hid : (-Q*Real.sin x+T*Real.cos x)^2-
      2*harmonicArg P Q T x*(-Q*Real.cos x-T*Real.sin x) =
      (Q*Real.cos x+T*Real.sin x)^2+
        2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 := by
    dsimp [harmonicArg]
    linear_combination (Q^2+T^2)*(Real.sin_sq_add_cos_sq x)
  have hA : harmonicArg P Q T x=P+(Q*Real.cos x+T*Real.sin x) := by
    dsimp only [harmonicArg]
    ring
  convert hh using 1
  · rfl
  · rw [hid,hA]
    rfl

lemma harmonic_wave_bound {a b Q T x : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hQT : Q^2+T^2=4*a^2*b^2) :
    |Q*Real.cos x+T*Real.sin x| ≤ 2*a*b := by
  have hid : (Q*Real.cos x+T*Real.sin x)^2+
      (-Q*Real.sin x+T*Real.cos x)^2=Q^2+T^2 := by
    linear_combination (Q^2+T^2)*(Real.sin_sq_add_cos_sq x)
  have hnonneg : 0≤2*a*b := by positivity
  have hs : (Q*Real.cos x+T*Real.sin x)^2≤(2*a*b)^2 := by
    nlinarith [sq_nonneg (-Q*Real.sin x+T*Real.cos x)]
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma harmonic_arg_positive {a b P Q T x : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hne : a≠b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2) : 0<harmonicArg P Q T x := by
  have hl := (abs_le.mp (harmonic_wave_bound (x := x) ha hb hQT)).1
  have hd : 0<(a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  dsimp [harmonicArg]
  nlinarith

lemma harmonic_length_bound {a b P Q T x : ℝ}
    (ha : 0≤a) (hb : 0≤b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2) :
    Real.sqrt (harmonicArg P Q T x)≤a+b := by
  have hl := (abs_le.mp (harmonic_wave_bound (x := x) ha hb hQT)).1
  have hu := (abs_le.mp (harmonic_wave_bound (x := x) ha hb hQT)).2
  have harg : 0≤harmonicArg P Q T x := by
    dsimp [harmonicArg]
    nlinarith [sq_nonneg (a-b)]
  have hr := Real.sq_sqrt harg
  have hn := Real.sqrt_nonneg (harmonicArg P Q T x)
  dsimp [harmonicArg] at *
  nlinarith

lemma rotating_length_factor (a b L : ℝ) :
    4*a*b*L^3-(a+b)*(L^4-(a^2-b^2)^2) =
      (a+b-L)*((a+b)*L^3+(a-b)^2*L^2+(a+b)*(a-b)^2*L+(a+b)^2*(a-b)^2) := by ring

/-- Where the squared length is positive, the second derivative of `-R` times
the length is at most `R ab/(a + b)`. -/
theorem harmonicCurvature_le_harmonic_mean {R a b P Q T x : ℝ}
    (hR : 0≤R) (ha : 0≤a) (hb : 0≤b) (hab : 0<a+b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2)
    (hx : 0<harmonicArg P Q T x) :
    harmonicCurvature R P Q T x ≤ R*a*b/(a+b) := by
  let L := Real.sqrt (harmonicArg P Q T x)
  have hL : 0<L := Real.sqrt_pos.mpr hx
  have hLup : L≤a+b := harmonic_length_bound ha hb hP hQT
  have hLsq : L^2=harmonicArg P Q T x := Real.sq_sqrt hx.le
  have he : harmonicCurvature R P Q T x =
      R*(L^4-(a^2-b^2)^2)/(4*L^3) := by
    have hs : L^2=P+(Q*Real.cos x+T*Real.sin x) := by
      rw [hLsq]
      dsimp only [harmonicArg]
      ring
    have hid : (Q*Real.cos x+T*Real.sin x)^2+2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 =
        L^4-(a^2-b^2)^2 := by
      linear_combination hQT-(P+a^2+b^2)*hP-(L^2+P+(Q*Real.cos x+T*Real.sin x))*hs
    have hroot : Real.sqrt (P+(Q*Real.cos x+T*Real.sin x))=L := by
      rw [← hs]
      exact Real.sqrt_sq hL.le
    dsimp only [harmonicCurvature]
    rw [hid,hroot,← hs]
    ring
  rw [he]
  have hpositive : 0≤(a+b)*L^3+(a-b)^2*L^2+(a+b)*(a-b)^2*L+(a+b)^2*(a-b)^2 := by
    positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hLup) hpositive
  rw [← rotating_length_factor] at hprod
  have hprodR := mul_nonneg hR hprod
  apply (div_le_div_iff₀ (show 0<4*L^3 by positivity) hab).mpr
  nlinarith only [hprodR]

lemma harmonic_mean_mono {a b A B : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hab : 0<a+b)
    (hA : a≤A) (hB : b≤B) : a*b/(a+b)≤A*B/(A+B) := by
  have hAB : 0<A+B := by linarith
  have hp := mul_nonneg (mul_nonneg ha (ha.trans hA)) (sub_nonneg.mpr hB)
  have hq := mul_nonneg (mul_nonneg hb (hb.trans hB)) (sub_nonneg.mpr hA)
  apply (div_le_div_iff₀ hab hAB).mpr
  nlinarith only [hp,hq]

/-- If `a ≤ b` and `Q cos x + T sin x ≤ -2a²`, so that the squared length is at
most `b² - a²`, the second derivative is nonpositive. -/
theorem harmonicCurvature_nonpos_of_opposition {R a b P Q T x : ℝ}
    (hR : 0≤R) (ha : 0≤a) (hb : a≤b)
    (hP : P=a^2+b^2) (hQT : Q^2+T^2=4*a^2*b^2)
    (hx : 0<harmonicArg P Q T x)
    (hop : Q*Real.cos x+T*Real.sin x≤-2*a^2) :
    harmonicCurvature R P Q T x≤0 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hb) (show 0≤a+b by linarith)
  have hsecond : 0≤Q*Real.cos x+T*Real.sin x+2*b^2 := by
    dsimp [harmonicArg] at hx
    nlinarith
  have hproduct := mul_nonpos_of_nonpos_of_nonneg
    (show Q*Real.cos x+T*Real.sin x+2*a^2≤0 by linarith) hsecond
  have hid : (Q*Real.cos x+T*Real.sin x)^2+
      2*P*(Q*Real.cos x+T*Real.sin x)+Q^2+T^2 =
      (Q*Real.cos x+T*Real.sin x+2*a^2)*(Q*Real.cos x+T*Real.sin x+2*b^2) := by
    linear_combination 2*(Q*Real.cos x+T*Real.sin x)*hP+hQT
  have hA : 0<P+(Q*Real.cos x+T*Real.sin x) := by
    have h := hx
    dsimp only [harmonicArg] at h
    linarith
  dsimp only [harmonicCurvature]
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR hproduct)
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _))

end SquaresInCircles.Six.Analytic
