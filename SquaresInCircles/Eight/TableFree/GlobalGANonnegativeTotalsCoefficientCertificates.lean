module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsPolynomial
public import SquaresInCircles.Eight.TableFree.ChebyshevLeadingBounds

/-!
# Whole-domain coefficient bounds for the two A/E weight families

Uncompiled transcription of Section 4. The triangle's affine secondary
coordinate is reduced to its two original edges. The two q-star bounds
retain the specified center 1/5, radius 1/3, and completed-square tail.
The rectangle's largest coefficient uses the single polynomial (31).
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Coefficients
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev d : ℚ := 8/15

def edge (far : Bool) (p : Bivar) : ℚ[X] :=
  restrict p X (if far then C d-X else 0)
def difference : Fin 4→Bivar :=
  ![Certificate.l .triangle-Certificate.k .triangle,
    Certificate.c .triangle-Certificate.k .triangle,
    Certificate.c .triangle-scalar (9/10)*Certificate.l .triangle,
    scalar (11/10)*Certificate.l .triangle-Certificate.c .triangle]
def differenceReserve : Fin 4→ℚ := ![3/200,7/1000,2/25,39/500]

def lowerM : Bivar := Certificate.c .triangle*
  (lift (Certificate.theta .triangle) PositiveTD.Certificate.C10+
    scalar (293/1000)*lift (Certificate.theta .triangle) PositiveTD.Certificate.S11)
def lowerGap (far : Bool) : ℚ[X] := edge far (lowerM-Certificate.k .triangle)
def upperGap (far : Bool) : ℚ[X] :=
  edge far (Certificate.qStar .triangle-Certificate.M .triangle .atT)
def centeredGap (far : Bool) : ℚ[X] := (upperGap far).comp (C (1/5)+X)
def gapCoefficient (far : Bool) (j : ℕ) : ℚ := (centeredGap far).coeff j
def gapTail (far : Bool) : ℚ :=
  ∑j : Fin 13,|gapCoefficient far (j.val+3)|*(1/3)^(j.val+1)
def gapCurvature (far : Bool) : ℚ := gapCoefficient far 2-gapTail far
def gapReserve : Bool→ℚ | false => 239/50000 | true => 1/625

def rectangleMaximum : ℚ[X] :=
  (C (11913/10000)-C (1/4)*X)*
    (PositiveTD.Certificate.C12+C (293/1000)*PositiveTD.Certificate.S9)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem l_lower_certificate :
    WholeIntervalPolynomial.centered 0 d (edge false (Certificate.l .triangle))=
      WholeIntervalPolynomial.expansion 3
        (WholeIntervalPolynomial.centered 0 d (edge false (Certificate.l .triangle))) ∧
    (22/25:ℚ)<WholeIntervalPolynomial.lowerOn 3 0 d (edge false (Certificate.l .triangle)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem c_lower_certificate :
    WholeIntervalPolynomial.centered 0 d (edge false (Certificate.c .triangle))=
      WholeIntervalPolynomial.expansion 3
        (WholeIntervalPolynomial.centered 0 d (edge false (Certificate.c .triangle))) ∧
    (439/500:ℚ)<WholeIntervalPolynomial.lowerOn 3 0 d (edge false (Certificate.c .triangle)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem difference_certificate (i : Fin 4) :
    Certificate.transform .triangle (difference i)=
      expansion 3 (Certificate.transform .triangle (difference i)) ∧
    differenceReserve i<Certificate.lowerOn .triangle 3 (difference i) := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem lowerGap_certificate (far : Bool) :
    WholeIntervalPolynomial.centered 0 d (lowerGap far).derivative=
      WholeIntervalPolynomial.expansion 14
        (WholeIntervalPolynomial.centered 0 d (lowerGap far).derivative) ∧
    WholeIntervalPolynomial.upperOn 14 0 d (lowerGap far).derivative<-(37/100:ℚ) ∧
    (21/2500:ℚ)<(lowerGap far).eval d := by
  cases far <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upperGap_certificate (far : Bool) :
    centeredGap far=C (gapCoefficient far 0)+C (gapCoefficient far 1)*X+
      C (gapCoefficient far 2)*X^2+
        ∑j : Fin 13,C (gapCoefficient far (j.val+3))*X^(j.val+3) ∧
    0<gapCurvature far ∧
    gapReserve far<gapCoefficient far 0-(gapCoefficient far 1)^2/(4*gapCurvature far) := by
  cases far <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem rectangle_maximum_certificate :
    WholeIntervalPolynomial.centered 0 (1/6) rectangleMaximum=
      WholeIntervalPolynomial.expansion 13
        (WholeIntervalPolynomial.centered 0 (1/6) rectangleMaximum) ∧
    WholeIntervalPolynomial.upperOn 13 0 (1/6) rectangleMaximum<(299/250:ℚ) := by decide

theorem difference_lower (i : Fin 4) {x y : ℝ}
    (hd : Explicit.Domain .triangle x y) :
    (differenceReserve i:ℝ)<evaluate x y (difference i) :=
  Certificate.positive_on_domain (difference_certificate i).1 (difference_certificate i).2 hd

theorem lowerGap_lower (far : Bool) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    (21/2500:ℝ)<aeval x (lowerGap far) := by
  have hc := lowerGap_certificate far
  have hm : AntitoneOn (fun x : ℝ => aeval x (lowerGap far)) (Icc (0:ℝ) (8/15)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt (lowerGap far) x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt (lowerGap far) x)
    intro x hx
    have hh := (WholeIntervalPolynomial.interval_bounds (by norm_num : (0:ℚ)<d)
      hc.1 (Ioo_subset_Icc_self hx)).2
    have hbound : (WholeIntervalPolynomial.upperOn 14 0 d (lowerGap far).derivative:ℝ)<-(37/100:ℝ) := by
      exact_mod_cast hc.2.1
    linarith
  have hh := hm hx (show (8/15:ℝ)∈Icc 0 (8/15) by norm_num) hx.2
  have he : (21/2500:ℝ)<aeval (8/15:ℝ) (lowerGap far) := by
    have hcast : (21/2500:ℝ)<((lowerGap far).eval d:ℝ) := by exact_mod_cast hc.2.2
    simpa only [←Certificate.eval_rat,d] using hcast
  exact he.trans_le hh

theorem upperGap_tail (far : Bool) {u : ℝ} (hu : |u|≤1/3) (j : Fin 13) :
    -(|(gapCoefficient far (j.val+3):ℝ)|*(1/3)^(j.val+1))*u^2≤
      (gapCoefficient far (j.val+3):ℝ)*u^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg u) hu (j.val+1)
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg (gapCoefficient far (j.val+3):ℝ))
  have hbound : |(gapCoefficient far (j.val+3):ℝ)*u^(j.val+1)|≤
      |(gapCoefficient far (j.val+3):ℝ)|*(1/3)^(j.val+1) := by
    simpa [abs_mul,abs_pow] using hh
  have hscaled := mul_le_mul_of_nonneg_right (abs_le.mp hbound).1 (sq_nonneg u)
  rw [show u^(j.val+3)=u^(j.val+1)*u^2 by rw [←pow_add]; congr 1; omega]
  nlinarith

theorem upperGap_lower (far : Bool) {x : ℝ} (hx : x∈Icc 0 (8/15:ℝ)) :
    (gapReserve far:ℝ)<aeval x (upperGap far) := by
  let u : ℝ := x-1/5
  have hu : |u|≤1/3 := by
    apply abs_le.mpr
    dsimp [u]
    constructor <;> linarith [hx.1,hx.2]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => upperGap_tail far hu j)
  have he : (∑j : Fin 13,-(|(gapCoefficient far (j.val+3):ℝ)|*(1/3)^(j.val+1))*u^2)=
      -(gapTail far:ℝ)*u^2 := by
    simp [gapTail,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hsum
  have hid := congrArg (fun p : ℚ[X] => aeval u p) (upperGap_certificate far).1
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X] at hid
  have hlower : (gapCoefficient far 0:ℝ)+(gapCoefficient far 1:ℝ)*u+
      (gapCurvature far:ℝ)*u^2≤aeval u (centeredGap far) := by
    dsimp [gapCurvature]
    push_cast
    linarith
  have hκ : (0:ℝ)<(gapCurvature far:ℝ) := by exact_mod_cast (upperGap_certificate far).2.1
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(gapCoefficient far 0:ℝ)) (b:=(gapCoefficient far 1:ℝ)) (x:=u) hκ
  have hreserve : (gapReserve far:ℝ)<(gapCoefficient far 0:ℝ)-
      (gapCoefficient far 1:ℝ)^2/(4*(gapCurvature far:ℝ)) := by
    exact_mod_cast (upperGap_certificate far).2.2
  have hvalue : aeval u (centeredGap far)=aeval x (upperGap far) := by
    simp [centeredGap,aeval_comp,u]
  rw [hvalue] at hlower
  linarith

theorem rectangle_maximum_upper {x : ℝ} (hx : x∈Icc 0 (1/6:ℝ)) :
    aeval x rectangleMaximum<(299/250:ℝ) := by
  have hh := (WholeIntervalPolynomial.interval_bounds (by norm_num : (0:ℚ)<1/6)
    rectangle_maximum_certificate.1 hx).2
  have hc : (WholeIntervalPolynomial.upperOn 13 0 (1/6) rectangleMaximum:ℝ)<299/250 := by
    exact_mod_cast rectangle_maximum_certificate.2
  exact hh.trans_lt hc

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Coefficients
