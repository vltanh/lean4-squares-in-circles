module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsData
public import SquaresInCircles.Eight.TableFree.CertificateRestrictions
public import SquaresInCircles.Eight.TableFree.NonnegativeTotalsMirrors

/-!
# The twelve literal nonnegative-total polynomial certificates

Uncompiled transcription of Sections 6--7 of
`HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md`.
The triangle and rectangle are each treated as one whole domain. The
only divisions remove an exact edge or endpoint. Every arithmetic
comparison below is a finite rational proposition checked by ordinary
kernel reduction when this draft is eventually elaborated.
-/

@[expose] public section
noncomputable section
open Set Polynomial
/- The declarations are checked one at a time: the exact bivariate checks below hold up to about a
gigabyte each while the kernel evaluates them, and run side by side they would need several. -/
set_option Elab.async false

namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial

abbrev d : ℚ := 8/15

def triangleQuotient (ep : Endpoint) (i : Fin 3) : Bivar :=
  divY (numerator .triangle ep i)
def triangleBase (ep : Endpoint) (i : Fin 3) : ℚ[X] :=
  baseY (numerator .triangle ep i)
def triangleFar (ep : Endpoint) (i : Fin 3) : ℚ[X] :=
  restrict (triangleQuotient ep i) X (C d-X)
def rectangleQuotient (ep : Endpoint) (i : Fin 3) : Bivar :=
  (numerator .rectangle ep i).divX
def rectangleBase (ep : Endpoint) (i : Fin 3) : ℚ[X] :=
  baseX (numerator .rectangle ep i)

/-- Equation (59), with both endpoint values retained. -/
def chordQuotient (p : ℚ[X]) : ℚ[X] :=
  (p-C (p.eval 0)-C ((p.eval d-p.eval 0)/d)*X)/(X*(C d-X))
def chordPolynomial (p : ℚ[X]) : ℚ[X] :=
  C (p.eval 0)+C ((p.eval d-p.eval 0)/d)*X+X*(C d-X)*chordQuotient p

def triangleDerivativeReserve (ep : Endpoint) : Fin 3→ℚ :=
  match ep with
  | .atA => ![-23/100,-43/100,-1/4]
  | .atT => ![-6/25,-21/50,-13/100]
def triangleFarReserve (ep : Endpoint) : Fin 2→ℚ :=
  match ep with
  | .atA => ![13/200,143/1000]
  | .atT => ![31/500,3/20]
def triangleFarDerivative (ep : Endpoint) : ℚ :=
  match ep with | .atA => -4/5 | .atT => -8/5
def triangleFarEndpoint (ep : Endpoint) : ℚ :=
  match ep with | .atA => 213/1000 | .atT => 43/500
def triangleInitialValue (ep : Endpoint) : ℚ :=
  match ep with | .atA => 1727/1000000 | .atT => 893/500000
def triangleInitialSlope (ep : Endpoint) : ℚ :=
  match ep with | .atA => 27/500 | .atT => 57/1000
def chordEndpointReserve (ep : Endpoint) (i : Fin 3) : ℚ :=
  match ep with
  | .atA => 121/1250
  | .atT => if i=1 then 893/500000 else 133/5000
def chordQuotientReserve (ep : Endpoint) (i : Fin 3) : ℚ :=
  match ep with
  | .atA => 21/100
  | .atT => if i=1 then -657/100000 else 5/4

def rectangleQuotientReserve (ep : Endpoint) : Fin 3→ℚ :=
  match ep with
  | .atA => ![13/250,18/125,223/500]
  | .atT => ![23/500,137/1000,259/1000]
def rectangleSlopeReserve (ep : Endpoint) : Fin 3→ℚ :=
  match ep with
  | .atA => ![0,1/10,99/50]
  | .atT => ![29/100000,53/500,21/10]
def massReserve : Region→ℚ | .triangle => 71/100 | .rectangle => 77/100

open CertificateRestrictions

/-- Proves all integer facts of a certificate by one kernel computation: the conjuncts of `P`
are left open and fixed by the goals they close. -/
private theorem h_all {P R : Prop} (hP : P) (h : P → R) : R := h hP

/-- Uses representations of the four masses of a numerator, each built once. -/
private theorem h_withMasses (φ : Bivar →+* ℚ[X]) (p0 p1 p2 p3 : Bivar)
    {a0 a1 a2 a3 : WholeIntervalPolynomial.Certificate.Scaled} {G : Prop}
    (h0 : RepOn φ a0 p0) (h1 : RepOn φ a1 p1) (h2 : RepOn φ a2 p2) (h3 : RepOn φ a3 p3)
    (h : RepOn φ a0 p0 → RepOn φ a1 p1 → RepOn φ a2 p2 → RepOn φ a3 p3 → G) : G :=
  h h0 h1 h2 h3

/-- Unfolds the parts of a numerator into ring expressions in `X`, `C X`, scalars, `lift` and
`cubicMass`. -/
macro "h_nnt_unfold" : tactic => `(tactic| simp only [
    NonnegativeTotals.Certificate.A,NonnegativeTotals.Certificate.P,
    NonnegativeTotals.Certificate.baseNorm,NonnegativeTotals.Certificate.M,
    NonnegativeTotals.Certificate.ABase,NonnegativeTotals.Certificate.qB,
    NonnegativeTotals.Certificate.jTheta,NonnegativeTotals.Certificate.jE,
    NonnegativeTotals.Certificate.J,NonnegativeTotals.Certificate.k,
    NonnegativeTotals.Certificate.l,NonnegativeTotals.Certificate.c,
    NonnegativeTotals.Certificate.theta,NonnegativeTotals.Certificate.e,
    NonnegativeTotals.Certificate.delta,NonnegativeTotals.Certificate.qStar,
    NonnegativeTotals.Certificate.rho,Matrix.cons_val,Fin.isValue,↓reduceIte,Fin.val_two,
    reduceCtorEq,false_and,and_true,true_and,Fin.val_zero,Fin.val_one,Nat.reduceEqDiff,
    Fin.reduceEq,and_false,Fin.coe_ofNat_eq_mod,Nat.reduceMod])

/-! ### Exact bivariate checks

The masses are packed in boxes of `33 × 33` digits of 600 bits, the numerators in boxes of
`41 × 41` digits of 2400 bits (`BivariateCertificate`). Each check is one kernel computation on
natural numbers. -/

section C1Checks
open PackedModels BivariateCertificate NonnegativeTotalsMirrors

/-- The packing of the masses. -/
private def c1_cfgM : Config := ⟨0, 16, 600⟩
/-- The packing of the numerators. -/
private def c1_cfgN : Config := ⟨0, 20, 2400⟩

private theorem c1_massT_atA_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle .atA 0 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atA_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle .atA 0 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atA_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle .atA 1 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atA_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle .atA 1 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atA_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle .atA 2 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atA_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle .atA 2 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atT_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle .atT 0 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atT_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle .atT 0 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atT_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle .atT 1 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atT_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle .atT 1 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atT_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle .atT 2 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atT_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle .atT 2 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_triD_atA_0 : XM.upperCheck c1_cfgN (XM.triangleM c1_cfgN
    (XM.derivYM c1_cfgN (XM.divYM c1_cfgN (numeratorM c1_cfgN .triangle .atA 0))) 8 15)
    (degree .triangle .atA 0) (-23) 100=true := by
  decide +kernel

private theorem c1_triD_atA_1 : XM.upperCheck c1_cfgN (XM.triangleM c1_cfgN
    (XM.derivYM c1_cfgN (XM.divYM c1_cfgN (numeratorM c1_cfgN .triangle .atA 1))) 8 15)
    (degree .triangle .atA 1) (-43) 100=true := by
  decide +kernel

private theorem c1_triD_atA_2 : XM.upperCheck c1_cfgN (XM.triangleM c1_cfgN
    (XM.derivYM c1_cfgN (XM.divYM c1_cfgN (numeratorM c1_cfgN .triangle .atA 2))) 8 15)
    (degree .triangle .atA 2) (-1) 4=true := by
  decide +kernel

private theorem c1_triD_atT_0 : XM.upperCheck c1_cfgN (XM.triangleM c1_cfgN
    (XM.derivYM c1_cfgN (XM.divYM c1_cfgN (numeratorM c1_cfgN .triangle .atT 0))) 8 15)
    (degree .triangle .atT 0) (-6) 25=true := by
  decide +kernel

private theorem c1_triD_atT_1 : XM.upperCheck c1_cfgN (XM.triangleM c1_cfgN
    (XM.derivYM c1_cfgN (XM.divYM c1_cfgN (numeratorM c1_cfgN .triangle .atT 1))) 8 15)
    (degree .triangle .atT 1) (-21) 50=true := by
  decide +kernel

private theorem c1_triD_atT_2 : XM.upperCheck c1_cfgN (XM.triangleM c1_cfgN
    (XM.derivYM c1_cfgN (XM.divYM c1_cfgN (numeratorM c1_cfgN .triangle .atT 2))) 8 15)
    (degree .triangle .atT 2) (-13) 100=true := by
  decide +kernel

private theorem c1_recQ_atA_0 : XM.lowerCheck c1_cfgN (XM.rectangleM c1_cfgN
    (XM.divXM c1_cfgN (numeratorM c1_cfgN .rectangle .atA 0)) 1 6 8 15)
    (degree .rectangle .atA 0) 13 250=true := by
  decide +kernel

private theorem c1_recQ_atA_1 : XM.lowerCheck c1_cfgN (XM.rectangleM c1_cfgN
    (XM.divXM c1_cfgN (numeratorM c1_cfgN .rectangle .atA 1)) 1 6 8 15)
    (degree .rectangle .atA 1) 18 125=true := by
  decide +kernel

private theorem c1_recQ_atA_2 : XM.lowerCheck c1_cfgN (XM.rectangleM c1_cfgN
    (XM.divXM c1_cfgN (numeratorM c1_cfgN .rectangle .atA 2)) 1 6 8 15)
    (degree .rectangle .atA 2) 223 500=true := by
  decide +kernel

private theorem c1_recQ_atT_0 : XM.lowerCheck c1_cfgN (XM.rectangleM c1_cfgN
    (XM.divXM c1_cfgN (numeratorM c1_cfgN .rectangle .atT 0)) 1 6 8 15)
    (degree .rectangle .atT 0) 23 500=true := by
  decide +kernel

private theorem c1_recQ_atT_1 : XM.lowerCheck c1_cfgN (XM.rectangleM c1_cfgN
    (XM.divXM c1_cfgN (numeratorM c1_cfgN .rectangle .atT 1)) 1 6 8 15)
    (degree .rectangle .atT 1) 137 1000=true := by
  decide +kernel

private theorem c1_recQ_atT_2 : XM.lowerCheck c1_cfgN (XM.rectangleM c1_cfgN
    (XM.divXM c1_cfgN (numeratorM c1_cfgN .rectangle .atT 2)) 1 6 8 15)
    (degree .rectangle .atT 2) 259 1000=true := by
  decide +kernel

private theorem c1_massT (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (massM c1_cfgM .triangle ep i j) 8 15) 3 71 100=true := by
  rcases ep with _|_ <;> fin_cases i
  exacts [c1_massT_atA_0 j,c1_massT_atA_1 j,c1_massT_atA_2 j,c1_massT_atT_0 j,c1_massT_atT_1 j,
    c1_massT_atT_2 j]
private theorem c1_massR (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (massM c1_cfgM .rectangle ep i j) 1 6 8 15) 3 77 100=true := by
  rcases ep with _|_ <;> fin_cases i
  exacts [c1_massR_atA_0 j,c1_massR_atA_1 j,c1_massR_atA_2 j,c1_massR_atT_0 j,c1_massR_atT_1 j,
    c1_massR_atT_2 j]

end C1Checks

open BivariateCertificate NonnegativeTotalsMirrors in
theorem mass_certificate (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    transform r (mass r ep i j)=expansion 3 (transform r (mass r ep i j)) ∧
    massReserve r<lowerOn r 3 (mass r ep i j) := by
  cases r
  · exact XM.lower_certificate (XM.rep_triangleM (rep_massM _ .triangle ep i j) (by norm_num))
      (c1_massT ep i j) (by norm_num [massReserve])
  · exact XM.lower_certificate (XM.rep_rectangleM (rep_massM _ .rectangle ep i j) (by norm_num)
      (by norm_num)) (c1_massR ep i j) (by norm_num [massReserve])

open BivariateCertificate NonnegativeTotalsMirrors in
theorem triangle_derivative_certificate (ep : Endpoint) (i : Fin 3) :
    transform .triangle (derivativeY (triangleQuotient ep i))=
      expansion (degree .triangle ep i) (transform .triangle (derivativeY (triangleQuotient ep i))) ∧
    upperOn .triangle (degree .triangle ep i) (derivativeY (triangleQuotient ep i))<
      triangleDerivativeReserve ep i := by
  have h := fun ep i => XM.rep_triangleM (XM.rep_derivYM (XM.rep_divYM
    (rep_numeratorM c1_cfgN .triangle ep i))) (d := 8/15) (dn := 8) (dd := 15) (by norm_num)
  rcases ep with _|_ <;> fin_cases i
  · exact XM.upper_certificate (h _ _) c1_triD_atA_0 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (h _ _) c1_triD_atA_1 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (h _ _) c1_triD_atA_2 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (h _ _) c1_triD_atT_0 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (h _ _) c1_triD_atT_1 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (h _ _) c1_triD_atT_2 (by norm_num [triangleDerivativeReserve])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atA_0 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atA 0)=
      WholeIntervalPolynomial.expansion 25
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atA 0)) ∧
    (13/200:ℚ)<WholeIntervalPolynomial.lowerOn 25 0 d (triangleFar .atA 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 25 (13/200:ℚ) 13 200 (by norm_num)
      (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
          (Scaled.rep_const d).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C d-X)) (mass .triangle .atA 0 0) (mass .triangle .atA 0 1)
          (mass .triangle .atA 0 2) (mass .triangle .atA 0 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .triangle .atA 0 0) (mass .triangle .atA 0 1)
          (mass .triangle .atA 0 2) (mass .triangle .atA 0 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atA_1 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atA 1)=
      WholeIntervalPolynomial.expansion 26
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atA 1)) ∧
    (143/1000:ℚ)<WholeIntervalPolynomial.lowerOn 26 0 d (triangleFar .atA 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 26 (143/1000:ℚ) 143 1000 (by norm_num)
      (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
          (Scaled.rep_const d).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C d-X)) (mass .triangle .atA 1 0) (mass .triangle .atA 1 1)
          (mass .triangle .atA 1 2) (mass .triangle .atA 1 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .triangle .atA 1 0) (mass .triangle .atA 1 1)
          (mass .triangle .atA 1 2) (mass .triangle .atA 1 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atT_0 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atT 0)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atT 0)) ∧
    (31/500:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar .atT 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (31/500:ℚ) 31 500 (by norm_num)
      (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
          (Scaled.rep_const d).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C d-X)) (mass .triangle .atT 0 0) (mass .triangle .atT 0 1)
          (mass .triangle .atT 0 2) (mass .triangle .atT 0 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .triangle .atT 0 0) (mass .triangle .atT 0 1)
          (mass .triangle .atT 0 2) (mass .triangle .atT 0 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atT_1 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atT 1)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atT 1)) ∧
    (3/20:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar .atT 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (3/20:ℚ) 3 20 (by norm_num)
      (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
          (Scaled.rep_const d).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C d-X)) (mass .triangle .atT 1 0) (mass .triangle .atT 1 1)
          (mass .triangle .atT 1 2) (mass .triangle .atT 1 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .triangle .atT 1 0) (mass .triangle .atT 1 1)
          (mass .triangle .atT 1 2) (mass .triangle .atT 1 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_far_certificate (ep : Endpoint) (i : Fin 2) :
    WholeIntervalPolynomial.centered 0 d (triangleFar ep i.castSucc)=
      WholeIntervalPolynomial.expansion (degree .triangle ep i.castSucc)
        (WholeIntervalPolynomial.centered 0 d (triangleFar ep i.castSucc)) ∧
    triangleFarReserve ep i<WholeIntervalPolynomial.lowerOn
      (degree .triangle ep i.castSucc) 0 d (triangleFar ep i.castSucc) := by
  cases ep <;> fin_cases i
  · exact h_triangleFar_atA_0
  · exact h_triangleFar_atA_1
  · exact h_triangleFar_atT_0
  · exact h_triangleFar_atT_1

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFarB_atA :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atA 2).derivative=
      WholeIntervalPolynomial.expansion 26
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atA 2).derivative) ∧
    WholeIntervalPolynomial.upperOn 26 0 d (triangleFar .atA 2).derivative<(-4/5:ℚ) ∧
    (213/1000:ℚ)<(triangleFar .atA 2).eval d := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply far_slope_cert ?ha d 4 15 (by norm_num) (by norm_num) 26 (-4/5:ℚ) (-4) 5 (by norm_num)
      (by norm_num) (213/1000:ℚ) 213 1000 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
          (Scaled.rep_const d).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C d-X)) (mass .triangle .atA 2 0) (mass .triangle .atA 2 1)
          (mass .triangle .atA 2 2) (mass .triangle .atA 2 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .triangle .atA 2 0) (mass .triangle .atA 2 1)
          (mass .triangle .atA 2 2) (mass .triangle .atA 2 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFarB_atT :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atT 2).derivative=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atT 2).derivative) ∧
    WholeIntervalPolynomial.upperOn 39 0 d (triangleFar .atT 2).derivative<(-8/5:ℚ) ∧
    (43/500:ℚ)<(triangleFar .atT 2).eval d := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply far_slope_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (-8/5:ℚ) (-8) 5 (by norm_num)
      (by norm_num) (43/500:ℚ) 43 500 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2.2.2.2.2.2
    case ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB hall.2.2.2.2.2.2.2.2.2.2.2.2.1
      case hΨ =>
        have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
        have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
          (Scaled.rep_const d).sub Scaled.rep_var
        apply h_withMasses (onCurve X (C d-X)) (mass .triangle .atT 2 0) (mass .triangle .atT 2 1)
          (mass .triangle .atT 2 2) (mass .triangle .atT 2 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_curve
          exact hall.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_curve
          all_goals assumption
      case hB =>
        apply h_withMasses (yZero) (mass .triangle .atT 2 0) (mass .triangle .atT 2 1)
          (mass .triangle .atT 2 2) (mass .triangle .atT 2 3)
        case h0 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.1
          exact hall.2.2.2.2.2.1
        case h1 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.1
        case h2 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.1
        case h3 =>
          simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
          exact hall.2.2.2.2.2.2.2.2.2.2.1
          exact hall.2.2.2.2.2.2.2.2.2.2.2.1
        case h =>
          intro hw0 hw1 hw2 hw3
          simp only [NonnegativeTotals.Certificate.numerator]
          h_nnt_unfold
          build_rep_yZero
          all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_far_B_certificate (ep : Endpoint) :
    WholeIntervalPolynomial.centered 0 d (triangleFar ep 2).derivative=
      WholeIntervalPolynomial.expansion (degree .triangle ep 2)
        (WholeIntervalPolynomial.centered 0 d (triangleFar ep 2).derivative) ∧
    WholeIntervalPolynomial.upperOn (degree .triangle ep 2) 0 d
      (triangleFar ep 2).derivative<triangleFarDerivative ep ∧
    triangleFarEndpoint ep<(triangleFar ep 2).eval d := by
  cases ep
  · exact h_triangleFarB_atA
  · exact h_triangleFarB_atT

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleInitial_atA :
    (1727/1000000:ℚ)<(triangleBase .atA 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (triangleBase .atA 0).divX=
      WholeIntervalPolynomial.expansion 25
        (WholeIntervalPolynomial.centered 0 d (triangleBase .atA 0).divX) ∧
    (27/500:ℚ)<WholeIntervalPolynomial.lowerOn 25 0 d (triangleBase .atA 0).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 25 (1727/1000000:ℚ) 1727 1000000
      (by norm_num) (by norm_num) (27/500:ℚ) 27 500 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .triangle .atA 0)
      apply h_withMasses (yZero) (mass .triangle .atA 0 0) (mass .triangle .atA 0 1)
        (mass .triangle .atA 0 2) (mass .triangle .atA 0 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleInitial_atT :
    (893/500000:ℚ)<(triangleBase .atT 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (triangleBase .atT 0).divX=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleBase .atT 0).divX) ∧
    (57/1000:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleBase .atT 0).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (893/500000:ℚ) 893 500000
      (by norm_num) (by norm_num) (57/1000:ℚ) 57 1000 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .triangle .atT 0)
      apply h_withMasses (yZero) (mass .triangle .atT 0 0) (mass .triangle .atT 0 1)
        (mass .triangle .atT 0 2) (mass .triangle .atT 0 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_initial_certificate (ep : Endpoint) :
    triangleInitialValue ep<(triangleBase ep 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (triangleBase ep 0).divX=
      WholeIntervalPolynomial.expansion (degree .triangle ep 0)
        (WholeIntervalPolynomial.centered 0 d (triangleBase ep 0).divX) ∧
    triangleInitialSlope ep<WholeIntervalPolynomial.lowerOn
      (degree .triangle ep 0) 0 d (triangleBase ep 0).divX := by
  cases ep
  · exact h_triangleInitial_atA
  · exact h_triangleInitial_atT

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_AG_certificate :
    WholeIntervalPolynomial.centered 0 d (triangleBase .atA 1)=
      WholeIntervalPolynomial.expansion (degree .triangle .atA 1)
        (WholeIntervalPolynomial.centered 0 d (triangleBase .atA 1)) ∧
    (21/12500:ℚ)<WholeIntervalPolynomial.lowerOn
      (degree .triangle .atA 1) 0 d (triangleBase .atA 1) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 26 (21/12500) 21 12500 (by norm_num)
      (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .triangle .atA 1)
      apply h_withMasses (yZero) (mass .triangle .atA 1 0) (mass .triangle .atA 1 1)
        (mass .triangle .atA 1 2) (mass .triangle .atA 1 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_yZero
        all_goals assumption
  case hP => set_option synthInstance.maxSize 1024 in decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleChord_atA_2 :
    triangleBase .atA 2=chordPolynomial (triangleBase .atA 2) ∧
    (121/1250:ℚ)<(triangleBase .atA 2).eval 0 ∧
    (121/1250:ℚ)<(triangleBase .atA 2).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase .atA 2))=
      WholeIntervalPolynomial.expansion 26
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase .atA 2))) ∧
    (21/100:ℚ)<WholeIntervalPolynomial.lowerOn 26 0 d
      (chordQuotient (triangleBase .atA 2)) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 26 (121/1250:ℚ) 121
      1250 (by norm_num) (by norm_num) (21/100:ℚ) 21 100 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .triangle .atA 2)
      apply h_withMasses (yZero) (mass .triangle .atA 2 0) (mass .triangle .atA 2 1)
        (mass .triangle .atA 2 2) (mass .triangle .atA 2 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleChord_atT_2 :
    triangleBase .atT 2=chordPolynomial (triangleBase .atT 2) ∧
    (133/5000:ℚ)<(triangleBase .atT 2).eval 0 ∧
    (133/5000:ℚ)<(triangleBase .atT 2).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase .atT 2))=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase .atT 2))) ∧
    (5/4:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d
      (chordQuotient (triangleBase .atT 2)) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 39 (133/5000:ℚ) 133
      5000 (by norm_num) (by norm_num) (5/4:ℚ) 5 4 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .triangle .atT 2)
      apply h_withMasses (yZero) (mass .triangle .atT 2 0) (mass .triangle .atT 2 1)
        (mass .triangle .atT 2 2) (mass .triangle .atT 2 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleChord_atT_1 :
    triangleBase .atT 1=chordPolynomial (triangleBase .atT 1) ∧
    (893/500000:ℚ)<(triangleBase .atT 1).eval 0 ∧
    (893/500000:ℚ)<(triangleBase .atT 1).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase .atT 1))=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase .atT 1))) ∧
    (-657/100000:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d
      (chordQuotient (triangleBase .atT 1)) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 39 (893/500000:ℚ) 893
      500000 (by norm_num) (by norm_num) (-657/100000:ℚ) (-657) 100000 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [triangleBase,baseY_eq_yZero]
      change RepOn yZero _ (numerator .triangle .atT 1)
      apply h_withMasses (yZero) (mass .triangle .atT 1 0) (mass .triangle .atT 1 1)
        (mass .triangle .atT 1 2) (mass .triangle .atT 1 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_yZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_yZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_chord_certificate (ep : Endpoint) (i : Fin 3)
    (hi : i=2 ∨ (ep=.atT ∧ i=1)) :
    triangleBase ep i=chordPolynomial (triangleBase ep i) ∧
    chordEndpointReserve ep i<(triangleBase ep i).eval 0 ∧
    chordEndpointReserve ep i<(triangleBase ep i).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase ep i))=
      WholeIntervalPolynomial.expansion (degree .triangle ep i)
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase ep i))) ∧
    chordQuotientReserve ep i<WholeIntervalPolynomial.lowerOn
      (degree .triangle ep i) 0 d (chordQuotient (triangleBase ep i)) := by
  rcases hi with rfl | ⟨rfl,rfl⟩
  · cases ep
    · exact h_triangleChord_atA_2
    · exact h_triangleChord_atT_2
  · exact h_triangleChord_atT_1

open BivariateCertificate NonnegativeTotalsMirrors in
theorem rectangle_quotient_certificate (ep : Endpoint) (i : Fin 3) :
    transform .rectangle (rectangleQuotient ep i)=
      expansion (degree .rectangle ep i) (transform .rectangle (rectangleQuotient ep i)) ∧
    rectangleQuotientReserve ep i<lowerOn .rectangle
      (degree .rectangle ep i) (rectangleQuotient ep i) := by
  have h := fun ep i => XM.rep_rectangleM (XM.rep_divXM (rep_numeratorM c1_cfgN .rectangle ep i))
    (a := 1/6) (b := 8/15) (an := 1) (ad := 6) (bn := 8) (bd := 15) (by norm_num) (by norm_num)
  rcases ep with _|_ <;> fin_cases i
  · exact XM.lower_certificate (h _ _) c1_recQ_atA_0 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (h _ _) c1_recQ_atA_1 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (h _ _) c1_recQ_atA_2 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (h _ _) c1_recQ_atT_0 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (h _ _) c1_recQ_atT_1 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (h _ _) c1_recQ_atT_2 (by norm_num [rectangleQuotientReserve])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem rectangle_AH_certificate :
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 0)=
      WholeIntervalPolynomial.expansion (degree .rectangle .atA 0)
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 0)) ∧
    (1/800:ℚ)<WholeIntervalPolynomial.lowerOn
      (degree .rectangle .atA 0) 0 d (rectangleBase .atA 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 23 (1/800) 1 800 (by norm_num)
      (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle .atA 0)
      apply h_withMasses (xZero) (mass .rectangle .atA 0 0) (mass .rectangle .atA 0 1)
        (mass .rectangle .atA 0 2) (mass .rectangle .atA 0 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_xZero
        all_goals assumption
  case hP => set_option synthInstance.maxSize 1024 in decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_rectangleInitial_atA_1 :
    (17/10000:ℚ)<(rectangleBase .atA 1).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 1).divX=
      WholeIntervalPolynomial.expansion 23
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 1).divX) ∧
    (1/10:ℚ)<WholeIntervalPolynomial.lowerOn 23 0 d (rectangleBase .atA 1).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 23 (17/10000) 17 10000
      (by norm_num) (by norm_num) (1/10:ℚ) 1 10 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle .atA 1)
      apply h_withMasses (xZero) (mass .rectangle .atA 1 0) (mass .rectangle .atA 1 1)
        (mass .rectangle .atA 1 2) (mass .rectangle .atA 1 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_rectangleInitial_atA_2 :
    (17/10000:ℚ)<(rectangleBase .atA 2).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 2).divX=
      WholeIntervalPolynomial.expansion 23
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 2).divX) ∧
    (99/50:ℚ)<WholeIntervalPolynomial.lowerOn 23 0 d (rectangleBase .atA 2).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 23 (17/10000) 17 10000
      (by norm_num) (by norm_num) (99/50:ℚ) 99 50 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle .atA 2)
      apply h_withMasses (xZero) (mass .rectangle .atA 2 0) (mass .rectangle .atA 2 1)
        (mass .rectangle .atA 2 2) (mass .rectangle .atA 2 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_rectangleInitial_atT_0 :
    (17/10000:ℚ)<(rectangleBase .atT 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atT 0).divX=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atT 0).divX) ∧
    (29/100000:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 d (rectangleBase .atT 0).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (17/10000) 17 10000
      (by norm_num) (by norm_num) (29/100000:ℚ) 29 100000 (by norm_num) (by norm_num)
        hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle .atT 0)
      apply h_withMasses (xZero) (mass .rectangle .atT 0 0) (mass .rectangle .atT 0 1)
        (mass .rectangle .atT 0 2) (mass .rectangle .atT 0 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_rectangleInitial_atT_1 :
    (17/10000:ℚ)<(rectangleBase .atT 1).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atT 1).divX=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atT 1).divX) ∧
    (53/500:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 d (rectangleBase .atT 1).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (17/10000) 17 10000
      (by norm_num) (by norm_num) (53/500:ℚ) 53 500 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle .atT 1)
      apply h_withMasses (xZero) (mass .rectangle .atT 1 0) (mass .rectangle .atT 1 1)
        (mass .rectangle .atT 1 2) (mass .rectangle .atT 1 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_rectangleInitial_atT_2 :
    (17/10000:ℚ)<(rectangleBase .atT 2).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atT 2).divX=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atT 2).divX) ∧
    (21/10:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 d (rectangleBase .atT 2).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply h_all (P := _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  case h =>
    intro hall
    apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (17/10000) 17 10000
      (by norm_num) (by norm_num) (21/10:ℚ) 21 10 (by norm_num) (by norm_num) hall.2.2.2.2.2.2.2.2
    case ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle .atT 2)
      apply h_withMasses (xZero) (mass .rectangle .atT 2 0) (mass .rectangle .atT 2 1)
        (mass .rectangle .atT 2 2) (mass .rectangle .atT 2 3)
      case h0 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.1
        exact hall.2.1
      case h1 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.1
        exact hall.2.2.2.1
      case h2 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.1
        exact hall.2.2.2.2.2.1
      case h3 =>
        simp only [NonnegativeTotals.Certificate.mass]; h_nnt_unfold; build_rep_xZero
        exact hall.2.2.2.2.2.2.1
        exact hall.2.2.2.2.2.2.2.1
      case h =>
        intro hw0 hw1 hw2 hw3
        simp only [NonnegativeTotals.Certificate.numerator]
        h_nnt_unfold
        build_rep_xZero
        all_goals assumption
  case hP => decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem rectangle_initial_certificate (ep : Endpoint) (i : Fin 3)
    (hi : ¬(ep=.atA ∧ i=0)) :
    (17/10000:ℚ)<(rectangleBase ep i).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase ep i).divX=
      WholeIntervalPolynomial.expansion (degree .rectangle ep i)
        (WholeIntervalPolynomial.centered 0 d (rectangleBase ep i).divX) ∧
    rectangleSlopeReserve ep i<WholeIntervalPolynomial.lowerOn
      (degree .rectangle ep i) 0 d (rectangleBase ep i).divX := by
  cases ep <;> fin_cases i
  · exact absurd ⟨rfl,rfl⟩ hi
  · exact h_rectangleInitial_atA_1
  · exact h_rectangleInitial_atA_2
  · exact h_rectangleInitial_atT_0
  · exact h_rectangleInitial_atT_1
  · exact h_rectangleInitial_atT_2

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.Certificate
