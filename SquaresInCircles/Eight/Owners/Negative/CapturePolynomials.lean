module

public import SquaresInCircles.Eight.Arithmetic.PolynomialExpressions
public import SquaresInCircles.Eight.Owners.Negative.CaptureData

/-!
# Eight squares: the eight exact cleared polynomials for canonical negative capture

All operations below are ordinary rational polynomial operations.  The
two approximate short-angle constants remain separate: their squared
sum is never replaced by one.  The secant endpoint is cleared by the
actual factor 1-s².  Whole-polynomial coefficient sums, followed by
finite derivative integration, give positivity on both full bands.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.NegativeCapturePolynomials
open CenteredMonomialBounds NegativeCaptureData PolynomialExpressions


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

/-! ### Integer values

`reify` writes a polynomial of this file as `PolyExpr.poly` of an expression, whose integer value
(a coefficient list with a common denominator) the kernel computes. -/

/-- Unfold the polynomials of this file into expressions. -/
local macro "reify" : tactic => `(tactic| simp only [P,constantNumerator,cosineNumerator,
  cosineSix,otherA,otherB,otherD,otherH,otherE,denominator,totalMass,scale,endpointConstant,
  endpointCosine,secantSquare,base,normA,normB,normBCosine,mass,aP,fP,weight,cubic,massARot,
  massAFixed,massAShort,massBFixed,massBShift,massD,massHFixed,massHSec,massHShort,massE,
  Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,Matrix.cons_val_zero,Matrix.cons_val_one,
  Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,
  Matrix.tail_cons,eq_self_iff_true,true_or,or_true,false_or,or_false,Bool.false_eq_true,
  ↓reduceIte,reify_C,reify_X,reify_one,reify_zero,reify_add,reify_sub,reify_neg,reify_mul,
  reify_pow])

/-! ### One kernel evaluation per band and vertex

Each certificate below evaluates the cleared polynomial of one band and one
vertex once, and checks every finite fact used about it: the degree bounds,
the cosine coefficient bound and the band's own reserves. -/

private def shapeOK (b : Band) (e ec : PolyExpr) : Bool :=
  cmSeries 26 e && (cmSeries 26 ec && cmUpperLt 26 (lo b) (hi b) (cosineReserve b) ec)

private def lowOrdOK (j : Fin 4) (e : PolyExpr) : Bool :=
  cmLowerGt 26 (mid .low) (rad .low) (1/200) e.deriv.deriv &&
    (valueGt (pivot j) (1/200000) e && valueAbsLt (pivot j) (1/100000) e.deriv)

private def lowSecOK (e : PolyExpr) : Bool := cmLowerGt 26 (mid .low) (rad .low) (1/40000) e

private def highOrdOK (e : PolyExpr) : Bool :=
  cmLowerGt 26 (mid .high) (rad .high) (-1/250000) e.deriv && valueGt (7/50) (3/500000) e

private def highSecOK (e : PolyExpr) : Bool :=
  cmLowerGt 26 (mid .high) (rad .high) (1/100000) e

private theorem cert_low0 : ∃ e ec : PolyExpr, P .low 0=e.poly ∧
    cosineNumerator .low 0=ec.poly ∧ (shapeOK .low e ec && lowOrdOK 0 e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low1 : ∃ e ec : PolyExpr, P .low 1=e.poly ∧
    cosineNumerator .low 1=ec.poly ∧ (shapeOK .low e ec && lowSecOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low2 : ∃ e ec : PolyExpr, P .low 2=e.poly ∧
    cosineNumerator .low 2=ec.poly ∧ (shapeOK .low e ec && lowOrdOK 2 e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_low3 : ∃ e ec : PolyExpr, P .low 3=e.poly ∧
    cosineNumerator .low 3=ec.poly ∧ (shapeOK .low e ec && lowOrdOK 3 e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high0 : ∃ e ec : PolyExpr, P .high 0=e.poly ∧
    cosineNumerator .high 0=ec.poly ∧ (shapeOK .high e ec && highOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high1 : ∃ e ec : PolyExpr, P .high 1=e.poly ∧
    cosineNumerator .high 1=ec.poly ∧ (shapeOK .high e ec && highSecOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high2 : ∃ e ec : PolyExpr, P .high 2=e.poly ∧
    cosineNumerator .high 2=ec.poly ∧ (shapeOK .high e ec && highOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem cert_high3 : ∃ e ec : PolyExpr, P .high 3=e.poly ∧
    cosineNumerator .high 3=ec.poly ∧ (shapeOK .high e ec && highOrdOK e)=true := by
  refine ⟨_,_,by reify; rfl,by reify; rfl,?_⟩
  decide +kernel

private theorem shape_of {b : Band} {c : PolyExpr → Bool} {p pc : ℚ[X]}
    (h : ∃ e ec : PolyExpr,p=e.poly ∧ pc=ec.poly ∧ (shapeOK b e ec && c e)=true) :
    ∃ e ec : PolyExpr,p=e.poly ∧ pc=ec.poly ∧ shapeOK b e ec=true := by
  obtain ⟨e,ec,h1,h2,h3⟩ := h
  exact ⟨e,ec,h1,h2,((Bool.and_eq_true _ _).mp h3).1⟩

private theorem shape (b : Band) (j : Fin 4) : ∃ e ec : PolyExpr, P b j=e.poly ∧
    cosineNumerator b j=ec.poly ∧ shapeOK b e ec=true := by
  cases b <;> fin_cases j
  exacts [shape_of cert_low0,shape_of cert_low1,shape_of cert_low2,shape_of cert_low3,
    shape_of cert_high0,shape_of cert_high1,shape_of cert_high2,shape_of cert_high3]

private theorem fin4_cases (j : Fin 4) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by
  fin_cases j <;> simp

private theorem r34_domain_low : domain .low=Icc (1499/100000:ℝ) (7/50) := by
  simp only [domain,lo,hi]
  norm_num

private theorem r34_domain_high : domain .high=Icc (7/50:ℝ) (27/100) := by
  simp only [domain,lo,hi]
  norm_num


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

theorem polynomial_series : ∀b j,
    translated (mid b) (P b j)=series 26 (translated (mid b) (P b j)) ∧
    translated (mid b) (P b j).derivative=
      series 26 (translated (mid b) (P b j).derivative) ∧
    translated (mid b) (P b j).derivative.derivative=
      series 26 (translated (mid b) (P b j).derivative.derivative) := by
  intro b j
  obtain ⟨e,ec,hL,-,hs⟩ := shape b j
  simp only [shapeOK,Bool.and_eq_true] at hs
  have hd := natDegree_of_check hs.1
  rw [hL]
  exact ⟨series_of_natDegree hd _,series_of_natDegree (natDegree_derivative_of_le hd) _,
    series_of_natDegree (natDegree_derivative_of_le (natDegree_derivative_of_le hd)) _⟩

private theorem low_ord {j : Fin 4} {e : PolyExpr} (h : lowOrdOK j e=true) :
    (1/200:ℚ)<lowerOn 26 (mid .low) (rad .low) e.poly.derivative.derivative ∧
      (1/200000:ℚ)<e.poly.eval (pivot j) ∧ |e.poly.derivative.eval (pivot j)|<1/100000 := by
  simp only [lowOrdOK,Bool.and_eq_true] at h
  have h1 := lowerOn_of_check h.1
  have h3 := value_abs_of_check h.2.2
  rw [PolyExpr.poly_deriv,PolyExpr.poly_deriv] at h1
  rw [PolyExpr.poly_deriv] at h3
  exact ⟨h1,value_of_check h.2.1,h3⟩

private theorem high_ord {e : PolyExpr} (h : highOrdOK e=true) :
    (-1/250000:ℚ)<lowerOn 26 (mid .high) (rad .high) e.poly.derivative ∧
      (3/500000:ℚ)<e.poly.eval (7/50) := by
  simp only [highOrdOK,Bool.and_eq_true] at h
  have h1 := lowerOn_of_check h.1
  rw [PolyExpr.poly_deriv] at h1
  exact ⟨h1,value_of_check h.2⟩

theorem low_curvature_coefficients : ∀j : Fin 4, j≠1 →
    (1/200:ℚ)<lowerOn 26 (mid .low) (rad .low) (P .low j).derivative.derivative := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low0
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).1
  · exact absurd rfl hj
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low2
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).1
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low3
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).1

theorem low_tangent_values : ∀j : Fin 4, j≠1 →
    (1/200000:ℚ)<(P .low j).eval (pivot j) ∧
      |(P .low j).derivative.eval (pivot j)|<1/100000 := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low0
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).2
  · exact absurd rfl hj
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low2
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).2
  · obtain ⟨e,ec,hL,-,h⟩ := cert_low3
    rw [hL]
    exact (low_ord ((Bool.and_eq_true _ _).mp h).2).2

theorem low_secant_coefficients :
    (1/40000:ℚ)<lowerOn 26 (mid .low) (rad .low) (P .low 1) := by
  obtain ⟨e,ec,hL,-,h⟩ := cert_low1
  rw [hL]
  exact lowerOn_of_check ((Bool.and_eq_true _ _).mp h).2

theorem high_growth_coefficients : ∀j : Fin 4, j≠1 →
    (-1/250000:ℚ)<lowerOn 26 (mid .high) (rad .high) (P .high j).derivative := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high0
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).1
  · exact absurd rfl hj
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high2
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).1
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high3
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).1

theorem high_start_values : ∀j : Fin 4, j≠1 →
    (3/500000:ℚ)<(P .high j).eval (7/50) := by
  intro j hj
  obtain rfl | rfl | rfl | rfl := fin4_cases j
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high0
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).2
  · exact absurd rfl hj
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high2
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).2
  · obtain ⟨e,ec,hL,-,h⟩ := cert_high3
    rw [hL]
    exact (high_ord ((Bool.and_eq_true _ _).mp h).2).2

theorem high_secant_coefficients :
    (1/100000:ℚ)<lowerOn 26 (mid .high) (rad .high) (P .high 1) := by
  obtain ⟨e,ec,hL,-,h⟩ := cert_high1
  rw [hL]
  exact lowerOn_of_check ((Bool.and_eq_true _ _).mp h).2

theorem rational_eval (p : ℚ[X]) (r : ℚ) :
    aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
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
  have hc := (Rat.cast_lt (K := ℝ)).mpr (low_curvature_coefficients j hj)
  rw [show ((1/200:ℚ):ℝ)=1/200 by norm_num] at hc
  exact hc.trans_le hb

/-- A complete-square tangent bound on the full first sine interval. -/
theorem low_ordinary_positive {s : ℝ} (hs : s∈domain .low) {j : Fin 4} (hj : j≠1) :
    (499/100000000:ℝ)<aeval s (P .low j) := by
  have hp : (pivot j:ℝ)∈Icc (1499/100000:ℝ) (7/50) := by
    fin_cases j <;> norm_num [pivot]
  rw [r34_domain_low] at hs
  have hh := second_derivative_tangent_lower
    (f := fun x : ℝ => aeval x (P .low j))
    (df := fun x : ℝ => aeval x (P .low j).derivative)
    (ddf := fun x : ℝ => aeval x (P .low j).derivative.derivative)
    (l := 1499/100000) (h := 7/50) (x₀ := (pivot j:ℝ)) (x := s) (κ := 1/200)
    (fun x _ => aeval_hasDerivAt _ x) (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (low_curvature (by rw [r34_domain_low]; exact hx) hj).le) hp hs
  have hv : (1/200000:ℝ)<aeval (pivot j:ℝ) (P .low j) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j hj).1
    rw [rational_eval]
    push_cast at h
    exact h
  have hd : |aeval (pivot j:ℝ) (P .low j).derivative|<1/100000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (low_tangent_values j hj).2
    rw [rational_eval]
    push_cast at h
    exact h
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
  have hn := (Rat.cast_lt (K := ℝ)).mpr low_secant_coefficients
  rw [show ((1/40000:ℚ):ℝ)=1/40000 by norm_num] at hn
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
  rw [r34_domain_high] at hs
  have hh := derivative_reserve
    (f := fun x : ℝ => aeval x (P .high j))
    (df := fun x : ℝ => aeval x (P .high j).derivative)
    (l := (7/50:ℝ)) (u := 27/100) (x := 7/50) (y := s) (k := -1/250000)
    (fun x _ => (aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
    (fun x _ => aeval_hasDerivAt _ x)
    (fun x hx => (high_growth (by rw [r34_domain_high]; exact Ioo_subset_Icc_self hx) hj).le)
    (by norm_num) hs hs.1
  have hv : (3/500000:ℝ)<aeval (7/50:ℝ) (P .high j) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (high_start_values j hj)
    rw [show (7/50:ℝ)=((7/50:ℚ):ℝ) by norm_num,rational_eval]
    push_cast at h
    exact h
  have hs' : s≤27/100 := hs.2
  have hs'' : 7/50≤s := hs.1
  nlinarith

theorem high_secant_positive {s : ℝ} (hs : s∈domain .high) :
    (1/100000:ℝ)<aeval s (P .high 1) := by
  have hb := interval_lower (polynomial_series .high 1).1
    (by norm_num [rad] : 0≤rad Band.high) (domain_centered hs)
  have hn := (Rat.cast_lt (K := ℝ)).mpr high_secant_coefficients
  rw [show ((1/100000:ℚ):ℝ)=1/100000 by norm_num] at hn
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

end SquaresInCircles.Eight.NegativeCapturePolynomials
