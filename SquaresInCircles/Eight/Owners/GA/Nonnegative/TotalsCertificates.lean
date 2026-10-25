module

public import SquaresInCircles.Eight.Arithmetic.CertificateRestrictions
public import SquaresInCircles.Eight.Arithmetic.BivariateRounding
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsMirrors

/-!
# Eight squares: the twelve literal nonnegative-total polynomial certificates

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

namespace SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Certificate
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

/-! ### Bivariate checks

`P` is exact (`BivariateCertificate.XM`) in digits of 170 bits, and the masses, from its truncation
to total degree three, in digits of 600 bits; the masses are checked in boxes of `33 × 33` digits.
The numerators are rounded models (`BivariateRounding.XE`) at the scale `2 ^ 60`: their products
use digits of 160 bits, and the quotient, the derivative, the substitution and the final bound
digits of 400 bits, in boxes of `41 × 41` digits at `T` (degree `39`) and `29 × 29` at `A` (degree
at most `26`). The error of the rounding enters the final bounds. -/

section C1Checks
open PackedModels BivariateCertificate BivariateRounding NonnegativeTotalsMirrors

/-- `mass r ep i j`, reduced, in the packing `cM`, from the truncation of `P` to total degree
three in the packing `cP` (the cubic mass reads nothing else). -/
private def c1_massM (cP cM : Config) (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cM (XM.cubicMassRM cM (rhoP ep i j).1 (rhoP ep i j).2
    (repackM cP cM (XM.trunc cP (PM cP r ep i j) 3)))

private theorem c1_rep_massM (cP cM : Config) (r : Region) (ep : Endpoint) (i : Fin 3)
    (j : Fin 4) : (c1_massM cP cM r ep i j).Rep cM (mass r ep i j) := by
  have h := XM.rep_cubicMassRM (rep_repackM (c' := cM) (XM.rep_trunc (rep_PM cP r ep i j) 3))
    (rho_eq ep i j)
  rw [cubicMass_truncTot] at h
  exact XM.rep_reduce h

/-- `numerator r ep i`, rounded to the scale `2 ^ K` in the packing `cE`: `A`, `P` and the masses
are exact in their packings, the products are rounded; the smaller factor is on the right. -/
private def c1_numE (cP cM cE : Config) (K : ℕ) (r : Region) (ep : Endpoint) (i : Fin 3) : XE :=
  let w := fun j => XE.ofXMAt cM cE K (c1_massM cP cM r ep i j)
  let P := fun j => XE.ofXMAt cP cE K (PM cP r ep i j)
  let mr := XE.mulR cE K
  XE.sub cE (mr (mr (mr (mr (mr (XE.ofXMAt cP cE K (AM cP r ep i))
      (XE.ofXMAt cP cE K (XM.ofInt cP 2 1))) (w 0)) (w 1)) (w 2)) (w 3))
    (mr (XE.add cE (XE.add cE (XE.add cE
      (mr (mr (mr (XE.add cE (P 0) (mr (w 0) (w 0))) (w 1)) (w 2)) (w 3))
      (mr (mr (mr (XE.add cE (P 1) (mr (w 1) (w 1))) (w 0)) (w 2)) (w 3)))
      (mr (mr (mr (XE.add cE (P 2) (mr (w 2) (w 2))) (w 0)) (w 1)) (w 3)))
      (mr (mr (mr (XE.add cE (P 3) (mr (w 3) (w 3))) (w 0)) (w 1)) (w 2)))
      (XE.ofXMAt cP cE K (XM.ofInt cP 494696877 250000000)))

private theorem c1_rep_numE (cP cM cE : Config) (K : ℕ) (r : Region) (ep : Endpoint) (i : Fin 3) :
    (c1_numE cP cM cE K r ep i).Rep cE (numerator r ep i) := by
  have hw (j : Fin 4) := XE.rep_ofXMAt (c' := cE) (c1_rep_massM cP cM r ep i j) K
  have hP (j : Fin 4) := XE.rep_ofXMAt (c' := cE) (rep_PM cP r ep i j) K
  have hs (j : Fin 4) : (XE.mulR cE K (XE.ofXMAt cM cE K (c1_massM cP cM r ep i j))
      (XE.ofXMAt cM cE K (c1_massM cP cM r ep i j))).Rep cE (mass r ep i j ^ 2) := by
    rw [pow_two]; exact XE.rep_mulR (hw j) (hw j) K
  exact XE.rep_sub (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR_swap
      (XE.rep_ofXMAt (XM.rep_lit cP (by norm_num)) K) (XE.rep_ofXMAt (rep_AM cP r ep i) K) K)
      (hw 0) K) (hw 1) K) (hw 2) K) (hw 3) K)
    (XE.rep_mulR_swap (XE.rep_ofXMAt (XM.rep_lit cP (by norm_num [Rbar])) K)
      (XE.rep_add (XE.rep_add (XE.rep_add
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 0) (hs 0)) (hw 1) K) (hw 2) K) (hw 3) K)
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 1) (hs 1)) (hw 0) K) (hw 2) K) (hw 3) K))
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 2) (hs 2)) (hw 0) K) (hw 1) K) (hw 3) K))
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 3) (hs 3)) (hw 0) K) (hw 1) K) (hw 2) K))
      K)

/-- The model of the triangle transform of the `y`-derivative of the quotient `i`. -/
private def c1_triE (cP cM cE cT : Config) (ep : Endpoint) (i : Fin 3) : XE :=
  XE.norm cT (XE.toScale cT cT 60 (XE.triangle cT 8 15 (XE.repack cE cT
    (XE.derivY cE (XE.divY cE (c1_numE cP cM cE 60 .triangle ep i))))))

private theorem c1_rep_triE (cP cM cE cT : Config) (ep : Endpoint) (i : Fin 3) :
    (c1_triE cP cM cE cT ep i).Rep cT (transform .triangle (derivativeY (triangleQuotient ep i))) :=
  XE.rep_norm (XE.rep_toScale (XE.rep_triangle (XE.rep_repack (XE.rep_derivY (XE.rep_divY
    (c1_rep_numE cP cM cE 60 .triangle ep i)))) (d := 8/15) (dn := 8) (dd := 15) (by norm_num)
    (by norm_num)) 60)

/-- The model of the rectangle transform of the quotient `i`. -/
private def c1_recE (cP cM cE cT : Config) (ep : Endpoint) (i : Fin 3) : XE :=
  XE.norm cT (XE.toScale cT cT 60 (XE.rectangle cT 1 6 8 15 (XE.repack cE cT
    (XE.divX cE (c1_numE cP cM cE 60 .rectangle ep i)))))

private theorem c1_rep_recE (cP cM cE cT : Config) (ep : Endpoint) (i : Fin 3) :
    (c1_recE cP cM cE cT ep i).Rep cT (transform .rectangle (rectangleQuotient ep i)) :=
  XE.rep_norm (XE.rep_toScale (XE.rep_rectangle (XE.rep_repack (XE.rep_divX
    (c1_rep_numE cP cM cE 60 .rectangle ep i))) (a := 1/6) (b := 8/15) (an := 1) (ad := 6)
    (bn := 8) (bd := 15) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) 60)

/-- The packings of the masses. -/
private def c1_cPM : Config := ⟨0, 16, 170⟩
private def c1_cfgM : Config := ⟨0, 16, 600⟩
/-- The packings of the numerators at `T` (degree `39`). -/
private def c1_cPT : Config := ⟨0, 20, 170⟩
private def c1_cMT : Config := ⟨0, 20, 600⟩
private def c1_cET : Config := ⟨0, 20, 160⟩
private def c1_cTT : Config := ⟨0, 20, 400⟩
/-- The packings of the numerators at `A` (degree at most `26`). -/
private def c1_cPA : Config := ⟨0, 14, 170⟩
private def c1_cMA : Config := ⟨0, 14, 600⟩
private def c1_cEA : Config := ⟨0, 14, 160⟩
private def c1_cTA : Config := ⟨0, 14, 400⟩

private theorem c1_massT_atA_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle .atA 0 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atA_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle .atA 0 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atA_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle .atA 1 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atA_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle .atA 1 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atA_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle .atA 2 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atA_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle .atA 2 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atT_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle .atT 0 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atT_0 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle .atT 0 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atT_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle .atT 1 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atT_1 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle .atT 1 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_massT_atT_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle .atT 2 j) 8 15) 3 71 100=true := by
  decide +kernel
private theorem c1_massR_atT_2 : ∀ j : Fin 4, XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle .atT 2 j) 1 6 8 15) 3 77 100=true := by
  decide +kernel

private theorem c1_triD_atA_0 : XE.upperCheck c1_cTA (c1_triE c1_cPA c1_cMA c1_cEA c1_cTA .atA 0)
    (degree .triangle .atA 0) (-23) 100=true := by
  decide +kernel

private theorem c1_triD_atA_1 : XE.upperCheck c1_cTA (c1_triE c1_cPA c1_cMA c1_cEA c1_cTA .atA 1)
    (degree .triangle .atA 1) (-43) 100=true := by
  decide +kernel

private theorem c1_triD_atA_2 : XE.upperCheck c1_cTA (c1_triE c1_cPA c1_cMA c1_cEA c1_cTA .atA 2)
    (degree .triangle .atA 2) (-1) 4=true := by
  decide +kernel

private theorem c1_triD_atT_0 : XE.upperCheck c1_cTT (c1_triE c1_cPT c1_cMT c1_cET c1_cTT .atT 0)
    (degree .triangle .atT 0) (-6) 25=true := by
  decide +kernel

private theorem c1_triD_atT_1 : XE.upperCheck c1_cTT (c1_triE c1_cPT c1_cMT c1_cET c1_cTT .atT 1)
    (degree .triangle .atT 1) (-21) 50=true := by
  decide +kernel

private theorem c1_triD_atT_2 : XE.upperCheck c1_cTT (c1_triE c1_cPT c1_cMT c1_cET c1_cTT .atT 2)
    (degree .triangle .atT 2) (-13) 100=true := by
  decide +kernel

private theorem c1_recQ_atA_0 : XE.lowerCheck c1_cTA (c1_recE c1_cPA c1_cMA c1_cEA c1_cTA .atA 0)
    (degree .rectangle .atA 0) 13 250=true := by
  decide +kernel

private theorem c1_recQ_atA_1 : XE.lowerCheck c1_cTA (c1_recE c1_cPA c1_cMA c1_cEA c1_cTA .atA 1)
    (degree .rectangle .atA 1) 18 125=true := by
  decide +kernel

private theorem c1_recQ_atA_2 : XE.lowerCheck c1_cTA (c1_recE c1_cPA c1_cMA c1_cEA c1_cTA .atA 2)
    (degree .rectangle .atA 2) 223 500=true := by
  decide +kernel

private theorem c1_recQ_atT_0 : XE.lowerCheck c1_cTT (c1_recE c1_cPT c1_cMT c1_cET c1_cTT .atT 0)
    (degree .rectangle .atT 0) 23 500=true := by
  decide +kernel

private theorem c1_recQ_atT_1 : XE.lowerCheck c1_cTT (c1_recE c1_cPT c1_cMT c1_cET c1_cTT .atT 1)
    (degree .rectangle .atT 1) 137 1000=true := by
  decide +kernel

private theorem c1_recQ_atT_2 : XE.lowerCheck c1_cTT (c1_recE c1_cPT c1_cMT c1_cET c1_cTT .atT 2)
    (degree .rectangle .atT 2) 259 1000=true := by
  decide +kernel

private theorem c1_massT (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM.lowerCheck c1_cfgM
    (XM.triangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .triangle ep i j) 8 15) 3 71 100=true := by
  rcases ep with _|_ <;> fin_cases i
  exacts [c1_massT_atA_0 j,c1_massT_atA_1 j,c1_massT_atA_2 j,c1_massT_atT_0 j,c1_massT_atT_1 j,
    c1_massT_atT_2 j]
private theorem c1_massR (ep : Endpoint) (i : Fin 3) (j : Fin 4) : XM.lowerCheck c1_cfgM
    (XM.rectangleM c1_cfgM (c1_massM c1_cPM c1_cfgM .rectangle ep i j) 1 6 8 15) 3 77 100=true := by
  rcases ep with _|_ <;> fin_cases i
  exacts [c1_massR_atA_0 j,c1_massR_atA_1 j,c1_massR_atA_2 j,c1_massR_atT_0 j,c1_massR_atT_1 j,
    c1_massR_atT_2 j]

end C1Checks

open BivariateCertificate NonnegativeTotalsMirrors in
theorem mass_certificate (r : Region) (ep : Endpoint) (i : Fin 3) (j : Fin 4) :
    transform r (mass r ep i j)=expansion 3 (transform r (mass r ep i j)) ∧
    massReserve r<lowerOn r 3 (mass r ep i j) := by
  cases r
  · exact XM.lower_certificate (XM.rep_triangleM (c1_rep_massM _ _ .triangle ep i j) (by norm_num))
      (c1_massT ep i j) (by norm_num [massReserve])
  · exact XM.lower_certificate (XM.rep_rectangleM (c1_rep_massM _ _ .rectangle ep i j) (by norm_num)
      (by norm_num)) (c1_massR ep i j) (by norm_num [massReserve])

open BivariateRounding in
theorem triangle_derivative_certificate (ep : Endpoint) (i : Fin 3) :
    transform .triangle (derivativeY (triangleQuotient ep i))=
      expansion (degree .triangle ep i) (transform .triangle (derivativeY (triangleQuotient ep i))) ∧
    upperOn .triangle (degree .triangle ep i) (derivativeY (triangleQuotient ep i))<
      triangleDerivativeReserve ep i := by
  rcases ep with _|_ <;> fin_cases i
  · exact XE.upper_certificate (c1_rep_triE _ _ _ _ _ _) c1_triD_atA_0
      (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (c1_rep_triE _ _ _ _ _ _) c1_triD_atA_1
      (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (c1_rep_triE _ _ _ _ _ _) c1_triD_atA_2
      (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (c1_rep_triE _ _ _ _ _ _) c1_triD_atT_0
      (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (c1_rep_triE _ _ _ _ _ _) c1_triD_atT_1
      (by norm_num [triangleDerivativeReserve])
  · exact XE.upper_certificate (c1_rep_triE _ _ _ _ _ _) c1_triD_atT_2
      (by norm_num [triangleDerivativeReserve])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atA_0 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atA 0)=
      WholeIntervalPolynomial.expansion 25
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atA 0)) ∧
    (13/200:ℚ)<WholeIntervalPolynomial.lowerOn 25 0 d (triangleFar .atA 0) := by
  open WholeIntervalPolynomial.Certificate in
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 25 (13/200:ℚ) 13 200 (by norm_num)
    (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
    case' hB =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
  build_rep
  decide_all

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atA_1 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atA 1)=
      WholeIntervalPolynomial.expansion 26
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atA 1)) ∧
    (143/1000:ℚ)<WholeIntervalPolynomial.lowerOn 26 0 d (triangleFar .atA 1) := by
  open WholeIntervalPolynomial.Certificate in
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 26 (143/1000:ℚ) 143 1000 (by norm_num)
    (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
    case' hB =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
  build_rep
  decide_all

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atT_0 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atT 0)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atT 0)) ∧
    (31/500:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar .atT 0) := by
  open WholeIntervalPolynomial.Certificate in
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (31/500:ℚ) 31 500 (by norm_num)
    (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
    case' hB =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
  build_rep
  decide_all

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1024 in
private theorem h_triangleFar_atT_1 :
    WholeIntervalPolynomial.centered 0 d (triangleFar .atT 1)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar .atT 1)) ∧
    (3/20:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar .atT 1) := by
  open WholeIntervalPolynomial.Certificate in
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (3/20:ℚ) 3 20 (by norm_num)
    (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
    case' hB =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
  build_rep
  decide_all

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
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply far_slope_cert ?ha d 4 15 (by norm_num) (by norm_num) 26 (-4/5:ℚ) (-4) 5 (by norm_num)
    (by norm_num) (213/1000:ℚ) 213 1000 (by norm_num) (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
    case' hB =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
  build_rep
  decide_all

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
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply far_slope_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (-8/5:ℚ) (-8) 5 (by norm_num)
    (by norm_num) (43/500:ℚ) 43 500 (by norm_num) (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
    case' hB =>
      simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
      h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 25 (1727/1000000:ℚ) 1727 1000000
    (by norm_num) (by norm_num) (27/500:ℚ) 27 500 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle .atA 0)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (893/500000:ℚ) 893 500000
    (by norm_num) (by norm_num) (57/1000:ℚ) 57 1000 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle .atT 0)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 26 (21/12500) 21 12500 (by norm_num)
    (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle .atA 1)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 26 (121/1250:ℚ) 121
    1250 (by norm_num) (by norm_num) (21/100:ℚ) 21 100 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle .atA 2)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 39 (133/5000:ℚ) 133
    5000 (by norm_num) (by norm_num) (5/4:ℚ) 5 4 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle .atT 2)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 39 (893/500000:ℚ) 893
    500000 (by norm_num) (by norm_num) (-657/100000:ℚ) (-657) 100000 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle .atT 1)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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

open BivariateRounding in
theorem rectangle_quotient_certificate (ep : Endpoint) (i : Fin 3) :
    transform .rectangle (rectangleQuotient ep i)=
      expansion (degree .rectangle ep i) (transform .rectangle (rectangleQuotient ep i)) ∧
    rectangleQuotientReserve ep i<lowerOn .rectangle
      (degree .rectangle ep i) (rectangleQuotient ep i) := by
  rcases ep with _|_ <;> fin_cases i
  · exact XE.lower_certificate (c1_rep_recE _ _ _ _ _ _) c1_recQ_atA_0
      (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (c1_rep_recE _ _ _ _ _ _) c1_recQ_atA_1
      (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (c1_rep_recE _ _ _ _ _ _) c1_recQ_atA_2
      (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (c1_rep_recE _ _ _ _ _ _) c1_recQ_atT_0
      (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (c1_rep_recE _ _ _ _ _ _) c1_recQ_atT_1
      (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (c1_rep_recE _ _ _ _ _ _) c1_recQ_atT_2
      (by norm_num [rectangleQuotientReserve])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem rectangle_AH_certificate :
    WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 0)=
      WholeIntervalPolynomial.expansion (degree .rectangle .atA 0)
        (WholeIntervalPolynomial.centered 0 d (rectangleBase .atA 0)) ∧
    (1/800:ℚ)<WholeIntervalPolynomial.lowerOn
      (degree .rectangle .atA 0) 0 d (rectangleBase .atA 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 23 (1/800) 1 800 (by norm_num)
    (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle .atA 0)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 23 (17/10000) 17 10000
    (by norm_num) (by norm_num) (1/10:ℚ) 1 10 (by norm_num) (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle .atA 1)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 23 (17/10000) 17 10000
    (by norm_num) (by norm_num) (99/50:ℚ) 99 50 (by norm_num) (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle .atA 2)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (17/10000) 17 10000
    (by norm_num) (by norm_num) (29/100000:ℚ) 29 100000 (by norm_num) (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle .atT 0)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (17/10000) 17 10000
    (by norm_num) (by norm_num) (53/500:ℚ) 53 500 (by norm_num) (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle .atT 1)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (17/10000) 17 10000
    (by norm_num) (by norm_num) (21/10:ℚ) 21 10 (by norm_num) (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle .atT 2)
    simp only [NonnegativeTotals.Certificate.numerator,NonnegativeTotals.Certificate.mass]
    h_nnt_unfold
  build_rep
  decide_all

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

end SquaresInCircles.Eight.GlobalGA.NonnegativeTotals.Certificate
