module

public import SquaresInCircles.Eight.Arithmetic.PolynomialExpressions

/-!
# Eight squares: the six continuous negative-DE endpoint polynomials

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
namespace SquaresInCircles.Eight.NegativeLargeDEPolynomials
open CenteredMonomialBounds PolynomialExpressions


inductive Band where
  | low | high
  deriving DecidableEq

instance : Fintype Band where
  elems := {.low, .high}
  complete x := by cases x <;> decide

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

/-! ### Integer values

`reify` writes a polynomial of this file as `PolyExpr.poly` of an expression, whose integer value
(a coefficient list with a common denominator) the kernel computes. -/

/-- Unfold the polynomials of this file into expressions. -/
local macro "reify" : tactic => `(tactic| simp only [P,constantNumerator,cosineNumerator,
  cosineSix,otherA,otherB,otherD,otherH,otherE,denominator,totalMass,scale,base,mass,aP,
  betaP,epsilonP,weight,cubic,massARot,massAFixed,massBFixed,massBRot,massD,massHFixed,
  massHSec,massE,Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,Matrix.cons_val_zero,
  Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
  Matrix.head_cons,Matrix.tail_cons,eq_self_iff_true,true_or,or_true,false_or,or_false,
  Bool.false_eq_true,↓reduceIte,reify_C,reify_X,reify_one,reify_zero,reify_add,reify_sub,
  reify_neg,reify_mul,reify_pow])

/-! ### One kernel evaluation per band and vertex

Each certificate below evaluates the cleared polynomial of one band and one
vertex once, and checks every finite fact used about it: the degree bounds,
the cosine coefficient bound and the band's own reserves. -/

private def shapeOK (b : Band) (e ec : PolyExpr) : Bool :=
  cmSeries 26 e.deriv && (cmSeries 26 ec && cmUpperLt 26 (lo b) (hi b) (cosineReserve b) ec)

private def lowOrdOK (e : PolyExpr) : Bool :=
  cmLowerGt 26 (2/25) (2/25) (1/250) e.deriv.deriv &&
    (valueGt (123/1000) (1/2500000) e && valueAbsLt (123/1000) (1/1000000) e.deriv)

private def lowSecOK (e : PolyExpr) : Bool :=
  cmLowerGt 26 (2/25) (2/25) (1/400) (-e.deriv.deriv) &&
    (valueGt 0 (1/250000) e && valueGt (4/25) (1/250000) e)

private def highOrdOK (e : PolyExpr) : Bool :=
  cmLowerGt 26 (43/200) (11/200) (1/12500) e.deriv && valueGt (4/25) (1/250000) e

private theorem cert_low0 : ∃ e ec : PolyExpr, P .low 0=e.poly ∧
    cosineNumerator .low 0=ec.poly ∧ (shapeOK .low e ec && lowOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low1 : ∃ e ec : PolyExpr, P .low 1=e.poly ∧
    cosineNumerator .low 1=ec.poly ∧ (shapeOK .low e ec && lowOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low2 : ∃ e ec : PolyExpr, P .low 2=e.poly ∧
    cosineNumerator .low 2=ec.poly ∧ (shapeOK .low e ec && lowSecOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high0 : ∃ e ec : PolyExpr, P .high 0=e.poly ∧
    cosineNumerator .high 0=ec.poly ∧ (shapeOK .high e ec && highOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high1 : ∃ e ec : PolyExpr, P .high 1=e.poly ∧
    cosineNumerator .high 1=ec.poly ∧ (shapeOK .high e ec && highOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high2 : ∃ e ec : PolyExpr, P .high 2=e.poly ∧
    cosineNumerator .high 2=ec.poly ∧ (shapeOK .high e ec && highOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem shape_of {b : Band} {c : PolyExpr → Bool} {p pc : ℚ[X]}
    (h : ∃ e ec : PolyExpr,p=e.poly ∧ pc=ec.poly ∧ (shapeOK b e ec && c e)=true) :
    ∃ e ec : PolyExpr,p=e.poly ∧ pc=ec.poly ∧ shapeOK b e ec=true := by
  obtain ⟨e,ec,h1,h2,h3⟩ := h
  exact ⟨e,ec,h1,h2,((Bool.and_eq_true _ _).mp h3).1⟩

private theorem shape (b : Band) (j : Fin 3) : ∃ e ec : PolyExpr, P b j=e.poly ∧
    cosineNumerator b j=ec.poly ∧ shapeOK b e ec=true := by
  cases b <;> fin_cases j
  exacts [shape_of cert_low0,shape_of cert_low1,shape_of cert_low2,shape_of cert_high0,
    shape_of cert_high1,shape_of cert_high2]

private theorem low_ord {e : PolyExpr} (h : lowOrdOK e=true) :
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) e.poly.derivative.derivative ∧
      (1/2500000:ℚ)<e.poly.eval (123/1000) ∧ |e.poly.derivative.eval (123/1000)|<1/1000000 := by
  simp only [lowOrdOK,Bool.and_eq_true] at h
  have h1 := lowerOn_of_check h.1
  have h3 := value_abs_of_check h.2.2
  rw [PolyExpr.poly_deriv,PolyExpr.poly_deriv] at h1
  rw [PolyExpr.poly_deriv] at h3
  exact ⟨h1,value_of_check h.2.1,h3⟩

private theorem high_ord {e : PolyExpr} (h : highOrdOK e=true) :
    (1/12500:ℚ)<lowerOn 26 (43/200) (11/200) e.poly.derivative ∧
      (1/250000:ℚ)<e.poly.eval (4/25) := by
  simp only [highOrdOK,Bool.and_eq_true] at h
  have h1 := lowerOn_of_check h.1
  rw [PolyExpr.poly_deriv] at h1
  exact ⟨h1,value_of_check h.2⟩

private theorem natDegree_weight (b : Band) (i : Fin 3) : (weight b i).natDegree≤3 := by
  cases b <;> fin_cases i <;> exact natDegree_cubic_le _ _ _ _

private theorem natDegree_mass (b : Band) (j : Fin 3) (i : Fin 5) : (mass b j i).natDegree≤3 := by
  fin_cases i <;> simp only [mass,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_one] <;> (try split_ifs) <;> cases b <;>
    exact natDegree_cubic_le _ _ _ _

private theorem fin3_cases (j : Fin 3) : j=0 ∨ j=1 ∨ j=2 := by
  fin_cases j <;> simp

private theorem r34_domain_low : domain .low=Icc (0:ℝ) (4/25) := by
  simp only [domain,lo,hi]
  norm_num

private theorem r34_domain_high : domain .high=Icc (4/25:ℝ) (27/100) := by
  simp only [domain,lo,hi]
  norm_num


theorem domain_centered {b : Band} {s : ℝ} (hs : s∈domain b) :
    |s-(mid b:ℝ)|≤(rad b:ℝ) := by
  cases b
  · rw [r34_domain_low] at hs
    rw [abs_le]
    simp only [mid,rad]
    push_cast
    constructor <;> linarith [hs.1,hs.2]
  · rw [r34_domain_high] at hs
    rw [abs_le]
    simp only [mid,rad]
    push_cast
    constructor <;> linarith [hs.1,hs.2]

theorem domain_full {b : Band} {s : ℝ} (hs : s∈domain b) :
    s∈Icc 0 (27/100 : ℝ) := by
  cases b
  · rw [r34_domain_low] at hs
    constructor <;> linarith [hs.1,hs.2]
  · rw [r34_domain_high] at hs
    constructor <;> linarith [hs.1,hs.2]

theorem weight_series : ∀b i,
    translated (mid b) (weight b i)=series 3 (translated (mid b) (weight b i)) ∧
    translated (mid b) (-weight b i)=series 3 (translated (mid b) (-weight b i)) := by
  intro b i
  exact ⟨series_of_natDegree (natDegree_weight b i) _,
    series_of_natDegree ((natDegree_neg _).le.trans (natDegree_weight b i)) _⟩

theorem weight_coefficients : ∀b i,
    weightLower i<lowerOn 3 (mid b) (rad b) (weight b i) ∧
    -weightUpper i<lowerOn 3 (mid b) (rad b) (-weight b i) := by
  intro b i
  cases b <;> fin_cases i <;>
    simp only [weight,cubic,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val,
      Matrix.cons_val_zero,Matrix.cons_val_one,neg_cubic,lowerOn_cubic,weightLower,weightUpper,
      mid,rad] <;>
    norm_num [abs_eq_max_neg,max_def,min_def]

theorem mass_series : ∀b j i,
    translated (mid b) (mass b j i)=series 3 (translated (mid b) (mass b j i)) :=
  fun b j i => series_of_natDegree (natDegree_mass b j i) _

theorem mass_coefficients : ∀b j i,
    (23/100:ℚ)<lowerOn 3 (mid b) (rad b) (mass b j i) := by
  intro b j i
  fin_cases i <;> simp only [mass,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_one] <;>
    (try split_ifs) <;> cases b <;>
    simp only [massARot,massAFixed,massBFixed,massBRot,massD,massHFixed,massHSec,massE,cubic,
      lowerOn_cubic,mid,rad] <;>
    norm_num [abs_eq_max_neg,max_def,min_def]

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
  have hn := (Rat.cast_lt (K := ℝ)).mpr (mass_coefficients b j i)
  rw [show ((23/100:ℚ):ℝ)=23/100 by norm_num] at hn
  linarith

theorem cosine_series : ∀b j,
    translated (lo b) (cosineNumerator b j)=
      series 26 (translated (lo b) (cosineNumerator b j)) := by
  intro b j
  obtain ⟨e,ec,-,hc,hs⟩ := shape b j
  simp only [shapeOK,Bool.and_eq_true] at hs
  rw [hc]
  exact series_of_check hs.2.1 _

theorem cosine_coefficients : ∀b j,
    upperOn 26 (lo b) (hi b) (cosineNumerator b j)<cosineReserve b := by
  intro b j
  obtain ⟨e,ec,-,hc,hs⟩ := shape b j
  simp only [shapeOK,Bool.and_eq_true] at hs
  rw [hc]
  exact upperOn_of_check hs.2.2

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
  intro b j
  obtain ⟨e,ec,hL,-,hs⟩ := shape b j
  simp only [shapeOK,Bool.and_eq_true] at hs
  have hd := natDegree_of_check hs.1
  rw [PolyExpr.poly_deriv] at hd
  rw [hL]
  exact ⟨series_of_natDegree hd _,series_of_natDegree (natDegree_derivative_of_le hd) _,
    series_of_natDegree ((natDegree_neg _).le.trans (natDegree_derivative_of_le hd)) _⟩

theorem low_curvature_coefficients :
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) (P .low 0).derivative.derivative ∧
    (1/250:ℚ)<lowerOn 26 (2/25) (2/25) (P .low 1).derivative.derivative ∧
    (1/400:ℚ)<lowerOn 26 (2/25) (2/25) (-(P .low 2).derivative.derivative) := by
  refine ⟨?_,?_,?_⟩
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low0
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).1
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low1
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).1
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low2
    simp only [lowSecOK,Bool.and_eq_true] at h
    have h1 := lowerOn_of_check h.2.1
    rw [PolyExpr.poly_neg,PolyExpr.poly_deriv,PolyExpr.poly_deriv] at h1
    rw [hL]
    exact h1

theorem high_growth_coefficients : ∀j,
    (1/12500:ℚ)<lowerOn 26 (43/200) (11/200) (P .high j).derivative := by
  intro j
  obtain rfl | rfl | rfl := fin3_cases j
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high0
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).1
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high1
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).1
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high2
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).1

theorem low_tangent_values : ∀j : Fin 2,
    (1/2500000:ℚ)<(P .low j.castSucc).eval (123/1000) ∧
    |(P .low j.castSucc).derivative.eval (123/1000)|<1/1000000 := by
  intro j
  obtain rfl | rfl : j=0 ∨ j=1 := by fin_cases j <;> simp
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low0
    rw [Fin.castSucc_zero,hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).2
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low1
    rw [Fin.castSucc_one,hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).2

theorem low_secant_endpoints :
    (1/250000:ℚ)<(P .low 2).eval 0 ∧
    (1/250000:ℚ)<(P .low 2).eval (4/25) := by
  obtain ⟨e,ec,hL,-,h⟩ := cert_low2
  simp only [lowSecOK,Bool.and_eq_true] at h
  rw [hL]
  exact ⟨value_of_check h.2.2.1,value_of_check h.2.2.2⟩

theorem high_start_values : ∀j,
    (1/250000:ℚ)<(P .high j).eval (4/25) := by
  intro j
  obtain rfl | rfl | rfl := fin3_cases j
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high0
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).2
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high1
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).2
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high2
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).2

theorem rational_eval (p : ℚ[X]) (r : ℚ) :
    aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
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
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  rw [show ((1/250:ℚ):ℝ)=1/250 by norm_num] at hc'
  exact hc'.trans_le hb

theorem low_secant_curvature {s : ℝ} (hs : s∈domain .low) :
    aeval s (P .low 2).derivative.derivative< -(1/400:ℝ) := by
  have hb := interval_lower (derivative_series .low 2).2.2
    (by norm_num [rad] : 0≤rad Band.low) (domain_centered hs)
  have hc := (Rat.cast_lt (K := ℝ)).mpr low_curvature_coefficients.2.2
  rw [show ((1/400:ℚ):ℝ)=1/400 by norm_num] at hc
  rw [map_neg] at hb
  have hc' : (1/400:ℝ)<(lowerOn 26 (mid .low) (rad .low) (-(P .low 2).derivative.derivative):ℝ) :=
    hc
  linarith

theorem high_growth {s : ℝ} (hs : s∈domain .high) (j : Fin 3) :
    (1/12500:ℝ)<aeval s (P .high j).derivative := by
  have hb := interval_lower (derivative_series .high j).1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hc := (Rat.cast_lt (K := ℝ)).mpr (high_growth_coefficients j)
  rw [show ((1/12500:ℚ):ℝ)=1/12500 by norm_num] at hc
  exact hc.trans_le hb

/-- The first two low-band polynomials retain their actual tangent at
.123 and the whole-interval curvature reserve. -/
theorem low_ordinary_positive {s : ℝ} (hs : s∈domain .low) (j : Fin 2) :
    0<aeval s (P .low j.castSucc) := by
  rw [r34_domain_low] at hs
  have hh := second_derivative_tangent_lower
    (f := fun x : ℝ => aeval x (P .low j.castSucc))
    (df := fun x : ℝ => aeval x (P .low j.castSucc).derivative)
    (ddf := fun x : ℝ => aeval x (P .low j.castSucc).derivative.derivative)
    (l := 0) (h := 4/25) (x₀ := 123/1000) (x := s) (κ := 1/250)
    (fun x _ => aeval_hasDerivAt _ x) (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (low_curvature (by rw [r34_domain_low]; exact hx) j).le) (by norm_num) hs
  have hv : (1/2500000:ℝ)<aeval (123/1000:ℝ) (P .low j.castSucc) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j).1
    rw [show (123/1000:ℝ)=((123/1000:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hd : |aeval (123/1000:ℝ) (P .low j.castSucc).derivative|<1/1000000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j).2
    rw [show (123/1000:ℝ)=((123/1000:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hd2 : (aeval (123/1000:ℝ) (P .low j.castSucc).derivative)^2<1/1000000000000 := by
    obtain ⟨hl,hu⟩ := abs_lt.mp hd
    nlinarith
  have hsq := sq_nonneg
    (s-123/1000+250*aeval (123/1000:ℝ) (P .low j.castSucc).derivative)
  nlinarith

theorem low_secant_positive {s : ℝ} (hs : s∈domain .low) :
    0<aeval s (P .low 2) := by
  rw [r34_domain_low] at hs
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (4/25)) (fun x : ℝ => aeval x (P .low 2)) := by
    apply concave_of_deriv2
      (f' := fun x => aeval x (P .low 2).derivative)
      (f'' := fun x => aeval x (P .low 2).derivative.derivative)
    · exact fun x _ => aeval_hasDerivAt _ x
    · exact fun x _ => aeval_hasDerivAt _ x
    · intro x hx
      linarith [low_secant_curvature (by rw [r34_domain_low]; exact hx)]
  have hh := concave_endpoint_reserve (f := fun x : ℝ => aeval x (P .low 2))
    (k := (0:ℝ)) (by norm_num) hs (by simpa using hc)
  have hl : (0:ℝ)<aeval 0 (P .low 2) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_trans (by norm_num : (0:ℚ)<1/250000) low_secant_endpoints.1)
    rw [show (0:ℝ)=((0:ℚ):ℝ) by norm_num,rational_eval]
    exact h
  have hu : (0:ℝ)<aeval (4/25:ℝ) (P .low 2) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_trans (by norm_num : (0:ℚ)<1/250000) low_secant_endpoints.2)
    rw [show (4/25:ℝ)=((4/25:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hm := lt_min hl hu
  simp only [zero_div,zero_mul,add_zero] at hh
  exact hm.trans_le hh

theorem high_positive {s : ℝ} (hs : s∈domain .high) (j : Fin 3) :
    0<aeval s (P .high j) := by
  rw [r34_domain_high] at hs
  have hh := derivative_reserve
    (f := fun x : ℝ => aeval x (P .high j))
    (df := fun x : ℝ => aeval x (P .high j).derivative)
    (l := (4/25:ℝ)) (u := 27/100) (x := 4/25) (y := s) (k := 0)
    (fun x _ => (aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
    (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => by
      linarith [high_growth (by rw [r34_domain_high]; exact Ioo_subset_Icc_self hx) j])
    (by norm_num) hs hs.1
  have hv : (0:ℝ)<aeval (4/25:ℝ) (P .high j) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_trans (by norm_num : (0:ℚ)<1/250000) (high_start_values j))
    rw [show (4/25:ℝ)=((4/25:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  simp only [zero_mul] at hh
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

end SquaresInCircles.Eight.NegativeLargeDEPolynomials
