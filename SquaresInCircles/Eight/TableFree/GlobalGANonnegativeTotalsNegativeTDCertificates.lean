module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDPolynomialData
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates
public import SquaresInCircles.Eight.TableFree.CertificateRestrictions
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDMassCertificate
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDWholeCertificate

/-!
# Exact finite coefficients for the negative-TD2 endpoints

Uncompiled transcription of equations (21) and (37)--(42). Each
trapezoid is transformed once. The two top-edge H/G bounds retain
their prescribed center 7/20 and full radius 7/20; the remaining seven
boundary polynomials use their complete original intervals.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

open CertificateRestrictions

/-- Proves all integer facts of a certificate by one kernel computation: the conjuncts of `P`
are left open and fixed by the goals they close. -/
private theorem h_all {P R : Prop} (hP : P) (h : P → R) : R := h hP

/-- Uses representations of the three masses of a numerator, each built once. -/
private theorem h_withMasses (φ : Bivar →+* ℚ[X]) (p0 p1 p2 : Bivar)
    {a0 a1 a2 : WholeIntervalPolynomial.Certificate.Scaled} {G : Prop}
    (h0 : RepOn φ a0 p0) (h1 : RepOn φ a1 p1) (h2 : RepOn φ a2 p2)
    (h : RepOn φ a0 p0 → RepOn φ a1 p1 → RepOn φ a2 p2 → G) : G :=
  h h0 h1 h2

/-- Unfolds the parts of a numerator into ring expressions in `X`, `C X`, scalars, `lift` and
`cubicMass`. -/
macro "h_negtd_unfold" : tactic => `(tactic| simp only [
    NonnegativeTotals.NegativeTD.Certificate.A,NonnegativeTotals.NegativeTD.Certificate.A0,
    NonnegativeTotals.NegativeTD.Certificate.P,NonnegativeTotals.NegativeTD.Certificate.P0,
    NonnegativeTotals.NegativeTD.Certificate.p,NonnegativeTotals.NegativeTD.Certificate.q,
    NonnegativeTotals.NegativeTD.Certificate.k,NonnegativeTotals.NegativeTD.Certificate.l,
    NonnegativeTotals.NegativeTD.Certificate.e,NonnegativeTotals.NegativeTD.Certificate.delta,
    NonnegativeTotals.NegativeTD.Certificate.a,NonnegativeTotals.NegativeTD.Certificate.J,
    NonnegativeTotals.NegativeTD.Certificate.rho,NonnegativeTotals.NegativeTD.Certificate.rhoBase,
    NonnegativeTotals.NegativeTD.Certificate.rhoNegative,Matrix.cons_val,Fin.isValue,↓reduceIte,
    Fin.reduceEq,true_and,and_true,false_and,and_false])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_low_0 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .low)
        (boundary .low (numerator (.negative 0)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .low)
          (boundary .low (numerator (.negative 0)))) ∧
    (101/1250:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .low)
      (boundary .low (numerator (.negative 0))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .low) 1 12 (by norm_num)
      (by norm_num [boundaryLength,L]) 20 (101/1250:ℚ) 101 1250 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2
    case ha =>
      rw [show boundary .low (numerator (.negative 0))=xZero (numerator (.negative 0)) from
        baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass (.negative 0) 0) (mass (.negative 0) 1)
        (mass (.negative 0) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_low_1 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .low)
        (boundary .low (numerator (.negative 1)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .low)
          (boundary .low (numerator (.negative 1)))) ∧
    (667/10000:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .low)
      (boundary .low (numerator (.negative 1))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .low) 1 12 (by norm_num)
      (by norm_num [boundaryLength,L]) 20 (667/10000:ℚ) 667 10000 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2
    case ha =>
      rw [show boundary .low (numerator (.negative 1))=xZero (numerator (.negative 1)) from
        baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass (.negative 1) 0) (mass (.negative 1) 1)
        (mass (.negative 1) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_low_2 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .low)
        (boundary .low (numerator (.negative 2)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .low)
          (boundary .low (numerator (.negative 2)))) ∧
    (3357/10000:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .low)
      (boundary .low (numerator (.negative 2))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .low) 1 12 (by norm_num)
      (by norm_num [boundaryLength,L]) 20 (3357/10000:ℚ) 3357 10000 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2
    case ha =>
      rw [show boundary .low (numerator (.negative 2))=xZero (numerator (.negative 2)) from
        baseX_eq_xZero _]
      change RepOn xZero _ _
      apply h_withMasses (xZero) (mass (.negative 2) 0) (mass (.negative 2) 1)
        (mass (.negative 2) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_equal_0 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .equal)
        (boundary .equal (numerator (.negative 0)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .equal)
          (boundary .equal (numerator (.negative 0)))) ∧
    (609/5000:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .equal)
      (boundary .equal (numerator (.negative 0))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .equal) 4 15 (by norm_num)
      (by norm_num [boundaryLength,d]) 20 (609/5000:ℚ) 609 5000 (by norm_num) (by norm_num)
        hall.2.2.2
    case ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const L).add Scaled.var).Rep (C L+X : ℚ[X]) :=
        (Scaled.rep_const L).add Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve X (C L+X)) (mass (.negative 0) 0) (mass (.negative 0) 1)
        (mass (.negative 0) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_equal_1 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .equal)
        (boundary .equal (numerator (.negative 1)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .equal)
          (boundary .equal (numerator (.negative 1)))) ∧
    (123/1000:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .equal)
      (boundary .equal (numerator (.negative 1))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .equal) 4 15 (by norm_num)
      (by norm_num [boundaryLength,d]) 20 (123/1000:ℚ) 123 1000 (by norm_num) (by norm_num)
        hall.2.2.2
    case ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const L).add Scaled.var).Rep (C L+X : ℚ[X]) :=
        (Scaled.rep_const L).add Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve X (C L+X)) (mass (.negative 1) 0) (mass (.negative 1) 1)
        (mass (.negative 1) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_equal_2 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .equal)
        (boundary .equal (numerator (.negative 2)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .equal)
          (boundary .equal (numerator (.negative 2)))) ∧
    (2207/5000:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .equal)
      (boundary .equal (numerator (.negative 2))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .equal) 4 15 (by norm_num)
      (by norm_num [boundaryLength,d]) 20 (2207/5000:ℚ) 2207 5000 (by norm_num) (by norm_num)
        hall.2.2.2
    case ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const L).add Scaled.var).Rep (C L+X : ℚ[X]) :=
        (Scaled.rep_const L).add Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve X (C L+X)) (mass (.negative 2) 0) (mass (.negative 2) 1)
        (mass (.negative 2) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_boundary_high_2 :
    WholeIntervalPolynomial.centered 0 (boundaryLength .high)
        (boundary .high (numerator (.negative 2)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength .high)
          (boundary .high (numerator (.negative 2)))) ∧
    (51/100:ℚ)<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength .high)
      (boundary .high (numerator (.negative 2))) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha (boundaryLength .high) 7 20 (by norm_num)
      (by norm_num [boundaryLength,h]) 20 (51/100:ℚ) 51 100 (by norm_num) (by norm_num) hall.2.2.2
    case ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (Scaled.const d).Rep (C d : ℚ[X]) := Scaled.rep_const d
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      apply h_withMasses (onCurve (C d) X) (mass (.negative 2) 0) (mass (.negative 2) 1)
        (mass (.negative 2) 2)
      case h0 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.1
      case h1 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.1
      case h2 =>
        simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
        exact hall.2.2.1
      case h =>
        intro hw0 hw1 hw2
        simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
        h_negtd_unfold
        build_rep_curve
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem boundary_certificate (b : Boundary) (i : Fin 3) (hdirect : b≠.high ∨ i=2) :
    WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))) ∧
    boundaryReserve b i<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength b)
      (boundary b (numerator (.negative i))) := by
  cases b <;> fin_cases i
  · exact h_boundary_low_0
  · exact h_boundary_low_1
  · exact h_boundary_low_2
  · exact h_boundary_equal_0
  · exact h_boundary_equal_1
  · exact h_boundary_equal_2
  · simp at hdirect
  · simp at hdirect
  · exact h_boundary_high_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_high_0 :
    highCentered 0=C (highCoefficient 0 0)+C (highCoefficient 0 1)*X+
      C (highCoefficient 0 2)*X^2+∑j : Fin 18,C (highCoefficient 0 (j.val+3))*X^(j.val+3) ∧
    0<highCurvature 0 ∧
    (117/5000:ℚ)<highCoefficient 0 0-(highCoefficient 0 1)^2/(4*highCurvature 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply quadratic_tail_cert ?ha 18 (7/20) 7 20 (by norm_num) (by norm_num) 0 0 1 (by norm_num)
      (by norm_num) (117/5000:ℚ) 117 5000 (by norm_num) (by norm_num) hall.2.2.2
    case ha =>
      unfold highCentered
      apply rep_comp_shift ?hb 1 20 7 20 (7/20) (by norm_num) (by norm_num) (by norm_num)
      case hb =>
        simp only [boundary,restrict_eq_onCurve]
        have hU : (Scaled.const d).Rep (C d : ℚ[X]) := Scaled.rep_const d
        have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        change RepOn _ _ _
        apply h_withMasses (onCurve (C d) X) (mass (.negative 0) 0) (mass (.negative 0) 1)
          (mass (.negative 0) 2)
        case h0 =>
          simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
          exact hall.2.2.1
        case h =>
          intro hw0 hw1 hw2
          simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
          h_negtd_unfold
          build_rep_curve
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_high_1 :
    highCentered 1=C (highCoefficient 1 0)+C (highCoefficient 1 1)*X+
      C (highCoefficient 1 2)*X^2+∑j : Fin 18,C (highCoefficient 1 (j.val+3))*X^(j.val+3) ∧
    0<highCurvature 1 ∧
    (179/10000:ℚ)<highCoefficient 1 0-(highCoefficient 1 1)^2/(4*highCurvature 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply quadratic_tail_cert ?ha 18 (7/20) 7 20 (by norm_num) (by norm_num) 0 0 1 (by norm_num)
      (by norm_num) (179/10000:ℚ) 179 10000 (by norm_num) (by norm_num) hall.2.2.2
    case ha =>
      unfold highCentered
      apply rep_comp_shift ?hb 1 20 7 20 (7/20) (by norm_num) (by norm_num) (by norm_num)
      case hb =>
        simp only [boundary,restrict_eq_onCurve]
        have hU : (Scaled.const d).Rep (C d : ℚ[X]) := Scaled.rep_const d
        have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        change RepOn _ _ _
        apply h_withMasses (onCurve (C d) X) (mass (.negative 1) 0) (mass (.negative 1) 1)
          (mass (.negative 1) 2)
        case h0 =>
          simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.NegativeTD.Certificate.mass]; h_negtd_unfold; build_rep_curve
          exact hall.2.2.1
        case h =>
          intro hw0 hw1 hw2
          simp only [NonnegativeTotals.NegativeTD.Certificate.numerator]
          h_negtd_unfold
          build_rep_curve
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem high_certificate (i : Fin 2) :
    highCentered i.castSucc=C (highCoefficient i.castSucc 0)+C (highCoefficient i.castSucc 1)*X+
      C (highCoefficient i.castSucc 2)*X^2+
        ∑j : Fin 18,C (highCoefficient i.castSucc (j.val+3))*X^(j.val+3) ∧
    0<highCurvature i.castSucc ∧
    boundaryReserve .high i.castSucc<highCoefficient i.castSucc 0-
      (highCoefficient i.castSucc 1)^2/(4*highCurvature i.castSucc) := by
  fin_cases i
  · exact h_high_0
  · exact h_high_1

private theorem r79_C6_h : C6.eval h=550685351/720000000 := by
  norm_num [C6,h]

private theorem r79_S9_h : PositiveTD.Certificate.S9.eval h=33396244932001/51840000000000 := by
  norm_num [PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,h]

private theorem r79_S11_h :
    PositiveTD.Certificate.S11.eval h=367358693969535751/570240000000000000 := by
  norm_num [PositiveTD.Certificate.S11,PositiveTD.Certificate.S9,PositiveTD.Certificate.S5,h]

open WholeIntervalPolynomial.Certificate in
private def r79_slopeS : Scaled :=
  let K := (Scaled.const (3/4)).add ((Scaled.const (7/50)).mul Scaled.var)
  let L := (Scaled.const (19/20)).add ((Scaled.const (9/20)).mul Scaled.var)
  ((((Scaled.const (9789/2500)).mul (K.pow 2)).mul (L.pow 2)).mul
      (Scaled.const ((550685351/720000000)^2))).sub
    ((((Scaled.const (4/5)).add (L.mul (Scaled.const (33396244932001/51840000000000)))).pow 2).mul
      (((K.pow 2).add (L.pow 2)).sub
        ((Scaled.const (2*(367358693969535751/570240000000000000))).mul K |>.mul L)))

open WholeIntervalPolynomial.Certificate in
private theorem r79_rep_slope : r79_slopeS.Rep slopePolynomial := by
  have hK : (Scaled.const (3/4)).add ((Scaled.const (7/50)).mul Scaled.var)|>.Rep slopeK :=
    (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
  have hL : (Scaled.const (19/20)).add ((Scaled.const (9/20)).mul Scaled.var)|>.Rep slopeL :=
    (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
  rw [slopePolynomial,r79_C6_h,r79_S9_h,r79_S11_h]
  exact ((((Scaled.rep_const _).mul (hK.pow 2)).mul (hL.pow 2)).mul (Scaled.rep_const _)).sub
    ((((Scaled.rep_const _).add (hL.mul (Scaled.rep_const _))).pow 2).mul
      (((hK.pow 2).add (hL.pow 2)).sub (((Scaled.rep_const _).mul hK).mul hL)))

private theorem r79_lt_div {a A : ℤ} {b B : ℕ} (hb : 0<b) (hB : 0<B) (h : a*B<A*b) :
    (a:ℚ)/b<(A:ℚ)/B := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast hB)]
  exact_mod_cast h

theorem slope_certificate :
    slopePolynomial=C (slopePolynomial.coeff 0)+C (slopePolynomial.coeff 1)*X+
      C (slopePolynomial.coeff 2)*X^2+C (slopePolynomial.coeff 3)*X^3+
        C (slopePolynomial.coeff 4)*X^4 ∧
    (361/5000:ℚ)<slopePolynomial.coeff 0 ∧ (173/1000:ℚ)<slopePolynomial.coeff 1 ∧
    (101/10000:ℚ)<slopePolynomial.coeff 2 ∧ -(91/5000:ℚ)<slopePolynomial.coeff 3 ∧
    -(7/2500:ℚ)<slopePolynomial.coeff 4 := by
  have hs : r79_slopeS.s≠0 := by decide +kernel
  have hc (j : ℕ) := r79_rep_slope.coeff hs j
  have hdeg : slopePolynomial.natDegree<5 :=
    lt_of_le_of_lt (r79_rep_slope.natDegree_le hs) (by decide +kernel)
  have hsp : 0<r79_slopeS.s := Nat.pos_of_ne_zero hs
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · conv_lhs => rw [slopePolynomial.as_sum_range_C_mul_X_pow' hdeg]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]
  · rw [hc,show (361/5000:ℚ)=((361:ℤ):ℚ)/((5000:ℕ):ℚ) by norm_num]
    exact r79_lt_div (by norm_num) hsp (by decide +kernel)
  · rw [hc,show (173/1000:ℚ)=((173:ℤ):ℚ)/((1000:ℕ):ℚ) by norm_num]
    exact r79_lt_div (by norm_num) hsp (by decide +kernel)
  · rw [hc,show (101/10000:ℚ)=((101:ℤ):ℚ)/((10000:ℕ):ℚ) by norm_num]
    exact r79_lt_div (by norm_num) hsp (by decide +kernel)
  · rw [hc,show -(91/5000:ℚ)=((-91:ℤ):ℚ)/((5000:ℕ):ℚ) by norm_num]
    exact r79_lt_div (by norm_num) hsp (by decide +kernel)
  · rw [hc,show -(7/2500:ℚ)=((-7:ℤ):ℚ)/((2500:ℕ):ℚ) by norm_num]
    exact r79_lt_div (by norm_num) hsp (by decide +kernel)

theorem mass_positive (f : Kind) (j : Fin 3) {t E : ℝ} (hd : Domain t E) :
    (18/25:ℝ)<evaluate t E (mass f j) := by
  have hh := positive_on_domain (mass_certificate f j).1 (mass_certificate f j).2 hd
  have hc : ((18/25:ℚ):ℝ)=18/25 := by norm_num
  rwa [hc] at hh

theorem whole_positive (f : Kind) (hf : Whole f) {t E : ℝ} (hd : Domain t E) :
    0<evaluate t E (numerator f) := by
  have hh := positive_on_domain (whole_certificate f hf).1 (whole_certificate f hf).2 hd
  have hv : (0:ℝ)<(wholeReserve f:ℝ) := by
    cases f with
    | negative i => exact hf.elim
    | equal => norm_num [wholeReserve]
    | positive i => fin_cases i <;> norm_num [wholeReserve]
    | diagonal => norm_num [wholeReserve]
  exact hv.trans hh

theorem direct_boundary_positive (b : Boundary) (i : Fin 3) (hdirect : b≠.high ∨ i=2)
    {x : ℝ} (hx : x∈Icc 0 (boundaryLength b:ℝ)) :
    (boundaryReserve b i:ℝ)<aeval x (boundary b (numerator (.negative i))) := by
  have hx' : x∈Icc ((0:ℚ):ℝ) (boundaryLength b:ℝ) := by
    rw [Rat.cast_zero]; exact hx
  exact WholeIntervalPolynomial.positive_on_interval
    (by cases b <;> norm_num [boundaryLength,L,h,d])
    (boundary_certificate b i hdirect).1 (boundary_certificate b i hdirect).2 hx'

theorem high_tail_lower (i : Fin 2) {u : ℝ} (hu : |u|≤7/20) (j : Fin 18) :
    -(|(highCoefficient i.castSucc (j.val+3):ℝ)| *(7/20)^(j.val+1))*u^2≤
      (highCoefficient i.castSucc (j.val+3):ℝ)*u^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg u) hu (j.val+1)
  have hh := mul_le_mul_of_nonneg_left hp (abs_nonneg (highCoefficient i.castSucc (j.val+3):ℝ))
  have hb : |(highCoefficient i.castSucc (j.val+3):ℝ)*u^(j.val+1)|≤
      |(highCoefficient i.castSucc (j.val+3):ℝ)| * (7/20)^(j.val+1) := by
    rw [abs_mul,abs_pow]; exact hh
  have hm := mul_le_mul_of_nonneg_right (abs_le.mp hb).1 (sq_nonneg u)
  rw [show u^(j.val+3)=u^(j.val+1)*u^2 by rw [←pow_add]]
  linarith

theorem high_positive (i : Fin 2) {x : ℝ} (hx : x∈Icc 0 (7/10:ℝ)) :
    (boundaryReserve .high i.castSucc:ℝ)<aeval x (boundary .high (numerator (.negative i.castSucc))) := by
  set u : ℝ := x-7/20 with hu_def
  have hu : |u|≤7/20 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => high_tail_lower i hu j)
  have he : (∑j : Fin 18,-(|(highCoefficient i.castSucc (j.val+3):ℝ)| * (7/20)^(j.val+1))*u^2)=
      -(highTail i.castSucc:ℝ)*u^2 := by simp [highTail,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hsum
  have hid := congrArg (fun p : ℚ[X] => aeval u p) (high_certificate i).1
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at hid
  have hquadratic : (highCoefficient i.castSucc 0:ℝ)+(highCoefficient i.castSucc 1:ℝ)*u+
      (highCurvature i.castSucc:ℝ)*u^2≤aeval u (highCentered i.castSucc) := by
    dsimp only [highCurvature]
    push_cast
    rw [hid]
    linarith
  have hκ : (0:ℝ)<(highCurvature i.castSucc:ℝ) := by exact_mod_cast (high_certificate i).2.1
  have hmin := ChebyshevLeadingBounds.quadratic_min
    (a:=(highCoefficient i.castSucc 0:ℝ)) (b:=(highCoefficient i.castSucc 1:ℝ)) (x:=u) hκ
  have hreserve : (boundaryReserve .high i.castSucc:ℝ)<(highCoefficient i.castSucc 0:ℝ)-
      (highCoefficient i.castSucc 1:ℝ)^2/(4*(highCurvature i.castSucc:ℝ)) := by
    exact_mod_cast (high_certificate i).2.2
  have hvalue : aeval u (highCentered i.castSucc)=
      aeval x (boundary .high (numerator (.negative i.castSucc))) := by
    simp [highCentered,aeval_comp,u]
  rw [hvalue] at hquadratic
  linarith

theorem boundary_positive (b : Boundary) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (boundaryLength b:ℝ)) :
    0<aeval x (boundary b (numerator (.negative i))) := by
  have hr : (0:ℝ)<(boundaryReserve b i:ℝ) := by
    cases b <;> fin_cases i <;> norm_num [boundaryReserve]
  apply hr.trans
  cases b
  · exact direct_boundary_positive .low i (Or.inl (by decide)) hx
  · exact direct_boundary_positive .equal i (Or.inl (by decide)) hx
  · have hx' : x∈Icc 0 (7/10:ℝ) := by
      have hl : ((boundaryLength .high:ℚ):ℝ)=7/10 := by norm_num [boundaryLength,h]
      rw [hl] at hx; exact hx
    fin_cases i
    · exact high_positive 0 hx'
    · exact high_positive 1 hx'
    · exact direct_boundary_positive .high 2 (Or.inr rfl) hx

theorem slope_positive {E : ℝ} (hE : E∈Icc 0 (7/10:ℝ)) :
    (13/200:ℝ)<aeval E slopePolynomial := by
  obtain ⟨hid,h0,h1,h2,h3,h4⟩ := slope_certificate
  have hc0 : (361/5000:ℝ)<(slopePolynomial.coeff 0:ℝ) := by
    rw [show (361/5000:ℝ)=((361/5000:ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr h0
  have hc1 : (173/1000:ℝ)<(slopePolynomial.coeff 1:ℝ) := by
    rw [show (173/1000:ℝ)=((173/1000:ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr h1
  have hc2 : (101/10000:ℝ)<(slopePolynomial.coeff 2:ℝ) := by
    rw [show (101/10000:ℝ)=((101/10000:ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr h2
  have hc3 : -(91/5000:ℝ)<(slopePolynomial.coeff 3:ℝ) := by
    rw [show -(91/5000:ℝ)=((-(91/5000):ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr h3
  have hc4 : -(7/2500:ℝ)<(slopePolynomial.coeff 4:ℝ) := by
    rw [show -(7/2500:ℝ)=((-(7/2500):ℚ):ℝ) by norm_num]; exact Rat.cast_lt.mpr h4
  have hm1 := mul_le_mul_of_nonneg_right hc1.le hE.1
  have hm2 := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg E)
  have hm3 := mul_le_mul_of_nonneg_right hc3.le (pow_nonneg hE.1 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4.le (pow_nonneg hE.1 4)
  have hp3 := pow_le_pow_left₀ hE.1 hE.2 3
  have hp4 := pow_le_pow_left₀ hE.1 hE.2 4
  have heval := congrArg (fun p : ℚ[X] => aeval E p) hid
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at heval
  rw [heval]
  norm_num at hp3 hp4
  linarith only [hc0,hm1,hm2,hm3,hm4,hp3,hp4,hE.1,sq_nonneg E,pow_nonneg hE.1 3,
    pow_nonneg hE.1 4]

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD.Certificate
