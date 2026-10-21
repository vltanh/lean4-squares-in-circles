module

public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# The six continuous negative-DE endpoint polynomials

Uncompiled reconstruction of sections 4--7 of
HAND_G5_NEGATIVE_HG_LARGE_TRANSVERSE_DE_ALIGNMENT_EXCLUSION.md.

The two choices below are cubic weight formulas on complete sine
intervals.  Each formula is held fixed at all three vertices of the
original angular simplex.  The endpoint masses enter only after that
exact-norm reduction.  Every arithmetic comparison is an explicit
rational coefficient sum of the displayed polynomials.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.NegativeLargeDEPolynomials
open CenteredMonomialBounds

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

inductive Band where
  | low | high
  deriving DecidableEq, Fintype

def lo : Band → ℚ | .low => 0 | .high => 4/25
def hi : Band → ℚ | .low => 4/25 | .high => 27/100
def mid : Band → ℚ | .low => 2/25 | .high => 43/200
def rad : Band → ℚ | .low => 2/25 | .high => 11/200
def domain (b : Band) : Set ℝ := Icc (lo b:ℝ) (hi b:ℝ)

def cubic (a b c d : ℚ) : ℚ[X] := C a+C b*X+C c*X^2+C d*X^3

def weight : Band → Fin 3 → ℚ[X]
  | .low => ![
      cubic (5882364/10000000) (4934062/10000000) (1427643/10000000) (-5188337/10000000),
      cubic (10080571/10000000) (1130618/10000000) (-9739332/10000000) (26675520/10000000),
      cubic (11668343/10000000) (-9213978/10000000) (709186/10000000) (11644648/10000000)]
  | .high => ![
      cubic (6633158/10000000) (-399489/10000000) (4780194/10000000) (-1700769/10000000),
      cubic (9663412/10000000) (3388059/10000000) (2953896/10000000) (-40769811/10000000),
      cubic (11418718/10000000) (-8017237/10000000) (8506823/10000000) (-23797095/10000000)]

def aP (b : Band) : ℚ[X] := weight b 0
def betaP (b : Band) : ℚ[X] := weight b 1
def epsilonP (b : Band) : ℚ[X] := weight b 2
def a (b : Band) (s : ℝ) : ℝ := aeval s (aP b)
def beta (b : Band) (s : ℝ) : ℝ := aeval s (betaP b)
def epsilon (b : Band) (s : ℝ) : ℝ := aeval s (epsilonP b)

def massARot : Band → ℚ[X]
  | .low => cubic (29347657/100000000) (-6503767/100000000)
      (-7091341/100000000) (-8897024/100000000)
  | .high => cubic (30357263/100000000) (-14570632/100000000)
      (4070833/100000000) (-10732173/100000000)
def massAFixed : Band → ℚ[X]
  | .low => cubic (29348151/100000000) (6325141/100000000)
      (4054196/100000000) (-7689433/100000000)
  | .high => cubic (30355109/100000000) (-526874/100000000)
      (6446582/100000000) (-1674049/100000000)
def massBFixed : Band → ℚ[X]
  | .low => cubic (29492831/100000000) (8686475/100000000)
      (-16973016/100000000) (49966604/100000000)
  | .high => cubic (29572699/100000000) (7226100/100000000)
      (9419652/100000000) (-82051441/100000000)
def massBRot : Band → ℚ[X]
  | .low => cubic (29493219/100000000) (-4166049/100000000)
      (-27993159/100000000) (48192325/100000000)
  | .high => cubic (29526357/100000000) (-5762896/100000000)
      (-160373/100000000) (-75838043/100000000)
def massD : Band → ℚ[X]
  | .low => cubic (38962916/100000000) (-9878934/100000000)
      (-24001063/100000000) (73320919/100000000)
  | .high => cubic (37791971/100000000) (-3967690/100000000)
      (13681627/100000000) (-111961265/100000000)
def massHFixed : Band → ℚ[X]
  | .low => cubic (38830893/100000000) (-17713048/100000000)
      (4857227/100000000) (19769415/100000000)
  | .high => cubic (38317300/100000000) (-14574793/100000000)
      (14011328/100000000) (-36291958/100000000)
def massHSec : Band → ℚ[X]
  | .low => cubic (38830222/100000000) (-17682548/100000000)
      (12596229/100000000) (26750787/100000000)
  | .high => cubic (38277232/100000000) (-13854359/100000000)
      (17734792/100000000) (-21542959/100000000)
def massE : Band → ℚ[X]
  | .low => cubic (30487404/100000000) (-22523113/100000000)
      (2419395/100000000) (28112053/100000000)
  | .high => cubic (29868446/100000000) (-19396183/100000000)
      (20127830/100000000) (-55787176/100000000)

/-- The last entry is M_E; the actual E circle mass is s*M_E. -/
def mass (b : Band) (j : Fin 3) : Fin 5 → ℚ[X] := ![
  if j=0 then massARot b else massAFixed b,
  if j=1 then massBRot b else massBFixed b,
  massD b,
  if j=2 then massHSec b else massHFixed b,
  massE b]

def otherA (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 1*mass b j 2*mass b j 3*mass b j 4
def otherB (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 2*mass b j 3*mass b j 4
def otherD (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 3*mass b j 4
def otherH (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 4
def otherE (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0*mass b j 1*mass b j 2*mass b j 3
def denominator (b : Band) (j : Fin 3) : ℚ[X] :=
  C 4*mass b j 0*mass b j 1*mass b j 2*mass b j 3*mass b j 4

def Q : ℚ := 1957767069/500000000
def eta : ℚ := 1/400
def k : ℚ := 307/1000
def K : ℚ := 13/12
def scale (j : Fin 3) : ℚ[X] := if j=2 then 1-X^2 else 1
def totalMass (b : Band) (j : Fin 3) : ℚ[X] :=
  mass b j 0+mass b j 1+mass b j 2+mass b j 3+X*mass b j 4

def base (b : Band) (j : Fin 3) : ℚ[X] :=
  C (if j=1 then 3 else 2)+C 2*aP b+C eta+
    C (if j=1 then 2 else 3)*betaP b+C (2*k)*X+
    epsilonP b+epsilonP b*X-C Q*totalMass b j

/-- The cosine-free part after multiplication by D_j*v_j². -/
def constantNumerator (b : Band) (j : Fin 3) : ℚ[X] :=
  denominator b j*scale j*base b j-
    otherA b j*scale j*(1+(aP b+C eta)^2-
      if j=0 then C 2*(aP b+C eta)*X else 0)-
    otherB b j*scale j*((betaP b)^2+(aP b)^2-
      if j=1 then C 2*aP b*betaP b*X else 0)-
    otherD b j*scale j*((epsilonP b)^2*(1-X^2)+C (k^2)*X^2+(betaP b)^2)-
    otherH b j*((epsilonP b)^2*scale j+1)-
    otherE b j*scale j*X*((epsilonP b)^2+C (k^2))

/-- The remaining coefficient of c, using c²=1-s² exactly. -/
def cosineNumerator (b : Band) (j : Fin 3) : ℚ[X] :=
  denominator b j*(scale j*(C 2*epsilonP b+
      if j=0 then 1 else if j=1 then betaP b else 0)+
      if j=2 then 1+C K*X else 0)-
    otherD b j*scale j*C (2*k)*epsilonP b*X

def cosineSix : ℚ[X] := 1-C (1/2)*X^2-C (1/8)*X^4-C (1/16)*X^6
def cosineReserve : Band → ℚ | .low => 3/50 | .high => 9/200
def P (b : Band) (j : Fin 3) : ℚ[X] :=
  constantNumerator b j+cosineNumerator b j*cosineSix-
    C (cosineReserve b/20)*X^8

def weightLower : Fin 3 → ℚ := ![58/100,99/100,93/100]
def weightUpper : Fin 3 → ℚ := ![69/100,103/100,117/100]

theorem domain_centered {b : Band} {s : ℝ} (hs : s∈domain b) :
    |s-(mid b:ℝ)|≤(rad b:ℝ) := by
  cases b <;> dsimp [domain,lo,hi,mid,rad] at hs ⊢ <;>
    apply abs_le.mpr <;> constructor <;> linarith [hs.1,hs.2]

theorem domain_full {b : Band} {s : ℝ} (hs : s∈domain b) :
    s∈Icc 0 (27/100 : ℝ) := by
  cases b <;> dsimp [domain,lo,hi] at hs ⊢ <;>
    constructor <;> linarith [hs.1,hs.2]

theorem weight_series : ∀b i,
    translated (mid b) (weight b i)=series 3 (translated (mid b) (weight b i)) ∧
    translated (mid b) (-weight b i)=series 3 (translated (mid b) (-weight b i)) := by
  decide

theorem weight_coefficients : ∀b i,
    weightLower i<lowerOn 3 (mid b) (rad b) (weight b i) ∧
    -weightUpper i<lowerOn 3 (mid b) (rad b) (-weight b i) := by
  decide

theorem mass_series : ∀b j i,
    translated (mid b) (mass b j i)=series 3 (translated (mid b) (mass b j i)) := by
  decide

theorem mass_coefficients : ∀b j i,
    (23/100:ℚ)<lowerOn 3 (mid b) (rad b) (mass b j i) := by
  decide

theorem weight_bounds {b : Band} {s : ℝ} (hs : s∈domain b) (i : Fin 3) :
    (weightLower i:ℝ)<aeval s (weight b i) ∧
      aeval s (weight b i)<(weightUpper i:ℝ) := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hlo := interval_lower (weight_series b i).1 hr (domain_centered hs)
  have hhi := interval_lower (weight_series b i).2 hr (domain_centered hs)
  have hnumlo : (weightLower i:ℝ)<(lowerOn 3 (mid b) (rad b) (weight b i):ℝ) := by
    exact_mod_cast (weight_coefficients b i).1
  have hnumhi : -(weightUpper i:ℝ)<(lowerOn 3 (mid b) (rad b) (-weight b i):ℝ) := by
    exact_mod_cast (weight_coefficients b i).2
  rw [map_neg] at hhi
  exact ⟨hnumlo.trans_le hlo,by linarith⟩

theorem actual_weight_bounds {b : Band} {s : ℝ} (hs : s∈domain b) :
    58/100<a b s ∧ a b s<69/100 ∧
    99/100<beta b s ∧ beta b s<103/100 ∧
    93/100<epsilon b s ∧ epsilon b s<117/100 := by
  have h0 := weight_bounds hs 0
  have h1 := weight_bounds hs 1
  have h2 := weight_bounds hs 2
  simpa [a,beta,epsilon,aP,betaP,epsilonP,weightLower,weightUpper] using
    And.intro h0.1 (And.intro h0.2 (And.intro h1.1 (And.intro h1.2 h2)))

theorem mass_positive {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 3) (i : Fin 5) :
    0<aeval s (mass b j i) := by
  have hr : 0≤rad b := by cases b <;> norm_num [rad]
  have hh := interval_lower (mass_series b j i) hr (domain_centered hs)
  have hn : (23/100:ℝ)<(lowerOn 3 (mid b) (rad b) (mass b j i):ℝ) := by
    exact_mod_cast mass_coefficients b j i
  linarith

theorem cosine_series : ∀b j,
    translated (lo b) (cosineNumerator b j)=
      series 26 (translated (lo b) (cosineNumerator b j)) := by
  decide

theorem cosine_coefficients : ∀b j,
    upperOn 26 (lo b) (hi b) (cosineNumerator b j)<cosineReserve b := by
  decide

theorem cosine_upper {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 3) :
    aeval s (cosineNumerator b j)<(cosineReserve b:ℝ) := by
  have hb := interval_upper (cosine_series b j) hs
  have hn : (upperOn 26 (lo b) (hi b) (cosineNumerator b j):ℝ)<(cosineReserve b:ℝ) := by
    exact_mod_cast cosine_coefficients b j
  exact hb.trans_lt hn

theorem derivative_series : ∀b j,
    translated (mid b) (P b j).derivative=
      series 26 (translated (mid b) (P b j).derivative) ∧
    translated (mid b) (P b j).derivative.derivative=
      series 26 (translated (mid b) (P b j).derivative.derivative) ∧
    translated (mid b) (-(P b j).derivative.derivative)=
      series 26 (translated (mid b) (-(P b j).derivative.derivative)) := by
  decide

theorem low_curvature_coefficients :
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) (P .low 0).derivative.derivative ∧
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) (P .low 1).derivative.derivative ∧
    (1/400:ℚ)<lowerOn 26 (2/25) (2/25) (-(P .low 2).derivative.derivative) := by
  decide

theorem high_growth_coefficients : ∀j,
    (1/12500:ℚ)<lowerOn 26 (43/200) (11/200) (P .high j).derivative := by
  decide

theorem low_tangent_values : ∀j : Fin 2,
    (1/2500000:ℚ)<(P .low j.castSucc).eval (123/1000) ∧
    |(P .low j.castSucc).derivative.eval (123/1000)|<1/1000000 := by
  decide

theorem low_secant_endpoints :
    (1/250000:ℚ)<(P .low 2).eval 0 ∧
    (1/250000:ℚ)<(P .low 2).eval (4/25) := by
  decide

theorem high_start_values : ∀j,
    (1/250000:ℚ)<(P .high j).eval (4/25) := by
  decide

theorem rational_eval (p : ℚ[X]) (r : ℚ) :
    aeval (r:ℝ) p=(p.eval r:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n c => simp [Polynomial.aeval_monomial,Polynomial.eval_monomial]

theorem low_curvature {s : ℝ} (hs : s∈domain .low) (j : Fin 2) :
    (1/250:ℝ)<aeval s (P .low j.castSucc).derivative.derivative := by
  have hb := interval_lower (derivative_series .low j.castSucc).2.1
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc : (1/250:ℚ)<
      lowerOn 26 (mid .low) (rad .low) (P .low j.castSucc).derivative.derivative := by
    fin_cases j
    · exact low_curvature_coefficients.1
    · exact low_curvature_coefficients.2.1
  have hc' : (1/250:ℝ)<
      (lowerOn 26 (mid .low) (rad .low) (P .low j.castSucc).derivative.derivative:ℝ) := by
    exact_mod_cast hc
  exact hc'.trans_le hb

theorem low_secant_curvature {s : ℝ} (hs : s∈domain .low) :
    aeval s (P .low 2).derivative.derivative<-(1/400:ℝ) := by
  have hb := interval_lower (derivative_series .low 2).2.2
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc : (1/400:ℝ)<
      (lowerOn 26 (mid .low) (rad .low) (-(P .low 2).derivative.derivative):ℝ) := by
    exact_mod_cast low_curvature_coefficients.2.2
  rw [map_neg] at hb
  linarith

theorem high_growth {s : ℝ} (hs : s∈domain .high) (j : Fin 3) :
    (1/12500:ℝ)<aeval s (P .high j).derivative := by
  have hb := interval_lower (derivative_series .high j).1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hc : (1/12500:ℝ)<
      (lowerOn 26 (mid .high) (rad .high) (P .high j).derivative:ℝ) := by
    exact_mod_cast high_growth_coefficients j
  exact hc.trans_le hb

/-- The first two low-band polynomials retain their actual tangent at
.123 and the whole-interval curvature reserve. -/
theorem low_ordinary_positive {s : ℝ} (hs : s∈domain .low) (j : Fin 2) :
    0<aeval s (P .low j.castSucc) := by
  have hh := second_derivative_tangent_lower
    (f := fun x : ℝ => aeval x (P .low j.castSucc))
    (df := fun x : ℝ => aeval x (P .low j.castSucc).derivative)
    (ddf := fun x : ℝ => aeval x (P .low j.castSucc).derivative.derivative)
    (l := 0) (h := 4/25) (x₀ := 123/1000) (x := s) (κ := 1/250)
    (fun x _ => aeval_hasDerivAt _ x) (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (low_curvature hx j).le) (by norm_num) hs
  have hv : (1/2500000:ℝ)<aeval (123/1000:ℝ) (P .low j.castSucc) := by
    rw [show (123/1000:ℝ)=((123/1000:ℚ):ℝ) by norm_num,rational_eval]
    exact_mod_cast (low_tangent_values j).1
  have hd : |aeval (123/1000:ℝ) (P .low j.castSucc).derivative|<1/1000000 := by
    rw [show (123/1000:ℝ)=((123/1000:ℚ):ℝ) by norm_num,rational_eval]
    exact_mod_cast (low_tangent_values j).2
  have hd2 : (aeval (123/1000:ℝ) (P .low j.castSucc).derivative)^2<1/1000000000000 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hd
    nlinarith
  have hsq := sq_nonneg
    (s-123/1000+250*aeval (123/1000:ℝ) (P .low j.castSucc).derivative)
  nlinarith

theorem low_secant_positive {s : ℝ} (hs : s∈domain .low) :
    0<aeval s (P .low 2) := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (4/25)) (fun x : ℝ => aeval x (P .low 2)) := by
    apply concave_of_deriv2
      (f' := fun x => aeval x (P .low 2).derivative)
      (f'' := fun x => aeval x (P .low 2).derivative.derivative)
    · exact fun x _ => aeval_hasDerivAt _ x
    · exact fun x _ => aeval_hasDerivAt _ x
    · intro x hx
      linarith [low_secant_curvature hx]
  have hh := concave_endpoint_reserve (f := fun x : ℝ => aeval x (P .low 2))
    (k := (0:ℝ)) (by norm_num) hs (by simpa using hc)
  have hl : (0:ℝ)<aeval 0 (P .low 2) := by
    rw [show (0:ℝ)=((0:ℚ):ℝ) by norm_num,rational_eval]
    have h : (0:ℚ)<(P .low 2).eval 0 := lt_trans (by norm_num) low_secant_endpoints.1
    exact_mod_cast h
  have hu : (0:ℝ)<aeval (4/25:ℝ) (P .low 2) := by
    rw [show (4/25:ℝ)=((4/25:ℚ):ℝ) by norm_num,rational_eval]
    have h : (0:ℚ)<(P .low 2).eval (4/25) := lt_trans (by norm_num) low_secant_endpoints.2
    exact_mod_cast h
  have hm := lt_min hl hu
  simpa using hm.trans_le hh

theorem high_positive {s : ℝ} (hs : s∈domain .high) (j : Fin 3) :
    0<aeval s (P .high j) := by
  have hh := derivative_reserve
    (f := fun x : ℝ => aeval x (P .high j))
    (df := fun x : ℝ => aeval x (P .high j).derivative)
    (l := (4/25:ℝ)) (u := 27/100) (x := 4/25) (y := s) (k := 0)
    (fun x _ => (aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
    (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => by linarith [high_growth (Ioo_subset_Icc_self hx) j])
    (by norm_num) hs hs.1
  have hv : (0:ℝ)<aeval (4/25:ℝ) (P .high j) := by
    rw [show (4/25:ℝ)=((4/25:ℚ):ℝ) by norm_num,rational_eval]
    have h : (0:ℚ)<(P .high j).eval (4/25) := lt_trans (by norm_num) (high_start_values j)
    exact_mod_cast h
  linarith

/-- Every actual sine in either complete interval has a positive cleared
endpoint polynomial; all three geometric simplex vertices are included. -/
theorem polynomial_positive {b : Band} {s : ℝ} (hs : s∈domain b) (j : Fin 3) :
    0<aeval s (P b j) := by
  cases b
  · fin_cases j
    · exact low_ordinary_positive hs 0
    · exact low_ordinary_positive hs 1
    · exact low_secant_positive hs
  · exact high_positive hs j

end SquaresInCircles.Eight.TableFree.NegativeLargeDEPolynomials
