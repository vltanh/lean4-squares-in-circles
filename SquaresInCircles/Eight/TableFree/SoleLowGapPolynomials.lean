module

public import SquaresInCircles.Eight.TableFree.SoleScalarData
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# A whole-interval polynomial gap for the low sole-E family

Uncompiled source. These are the two positive-sided squarings in (55)
of the sole-EH hand proof. The radius parameter is the lower endpoint
qLow, so the later comparison applies to the original common radius.
All three identities and coefficient bounds cover the complete interval
[0,1/5]. The exact reductions below have not been run.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SoleLowGapPolynomials
open Polynomial WholeIntervalPolynomial HighOrderTaylor SoleECoefficients

def sinCap : ℚ := PositiveScalarPolynomials.sine.eval (7/10)
def cosLower : ℚ[X] :=
  PositiveScalarPolynomials.cosine-C (1/20922789888000)*X^16
def cosCap : ℚ := cosLower.eval (7/10)
def sinUpper : ℚ[X] :=
  PositiveScalarPolynomials.sine+C (1/1307674368000)*X^15
def l : ℚ[X] := SoleScalarPolynomials.ell .low
def c : ℚ[X] := SoleScalarPolynomials.c .low
def q : ℚ := 19577/5000
def normSquare : ℚ[X] := l^2+c^2-2*l*c*C sinCap
def squareGap : ℚ[X] := 2*l*c*(C sinCap-sinUpper)
def demand : ℚ[X] := C (43/100)+c*(PositiveScalarPolynomials.cosine-C cosCap)
def firstSquare : ℚ[X] := C q*squareGap-demand^2
def certificate : ℚ[X] := firstSquare^2-4*C q*demand^2*normSquare


/-! ### Kernel certificates

The polynomials are mirrored by scaled integer coefficient lists
(`PolynomialCertificates`); the identities and reserves are integer
computations checked by the kernel. -/

section Certificates
open WholeIntervalPolynomial.Certificate

/-- A rational lower reserve from an integer comparison. -/
private theorem lt_of_int {r : ℚ} {n d s m : ℕ} {Z : ℤ} (hr : r=(n:ℚ)/d) (hd : 0<d)
    (hs : 0<s) (h : (n:ℤ)*(s*2^m)<2*d*Z) : r<(Z:ℚ)/(s*2^m/2) := by
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  have hs' : (0:ℚ)<(s:ℚ)*2^m/2 := by positivity
  rw [hr,div_lt_div_iff₀ hd' hs']
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast at h'
  linarith

private theorem sinCap_val :
    sinCap=1562944261619609101762963/2426112000000000000000000 := by
  simp only [sinCap,PositiveScalarPolynomials.sine,eval_add,eval_sub,eval_mul,eval_pow,
    eval_C,eval_X]
  norm_num

private theorem cosCap_val :
    cosCap=136076805969657256004599/177914880000000000000000 := by
  simp only [cosCap,cosLower,PositiveScalarPolynomials.cosine,eval_add,eval_sub,eval_mul,
    eval_pow,eval_C,eval_X,eval_one]
  norm_num

private def sineS : Scaled :=
  ((((((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))).sub
    ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))).add
    ((Scaled.const (1/6227020800)).mul (Scaled.var.pow 13))).sub
    ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))

private theorem rep_sine : sineS.Rep PositiveScalarPolynomials.sine :=
  ((((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 13))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

private def cosineS : Scaled :=
  (((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))).add
    ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))).sub
    ((Scaled.const (1/87178291200)).mul (Scaled.var.pow 14)) |>.add
    ((Scaled.const (1/20922789888000)).mul (Scaled.var.pow 16))

private theorem rep_cosine : cosineS.Rep PositiveScalarPolynomials.cosine :=
  ((((((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 14))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 16)))

private def sinUpperS : Scaled :=
  sineS.add ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))

private theorem rep_sinUpper : sinUpperS.Rep sinUpper :=
  rep_sine.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

private def lS : Scaled :=
  ((Scaled.const (50521/100000)).add ((Scaled.const (823/1000)).mul Scaled.var)).add
    ((Scaled.const (7/10)).mul (Scaled.var.pow 2))

private theorem rep_l : lS.Rep l :=
  ((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))

private def cS : Scaled :=
  (((Scaled.const (17253/20000)).add ((Scaled.const (11/20)).mul Scaled.var)).add
    ((Scaled.const (3/10)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (3/10)).mul Scaled.var)

private theorem rep_c : cS.Rep c :=
  (((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul Scaled.rep_var)

private def sinCapS : Scaled := Scaled.const (1562944261619609101762963/2426112000000000000000000)

private theorem rep_sinCap : sinCapS.Rep (C sinCap) := by
  rw [sinCap_val]; exact Scaled.rep_const _

private def cosCapS : Scaled := Scaled.const (136076805969657256004599/177914880000000000000000)

private theorem rep_cosCap : cosCapS.Rep (C cosCap) := by
  rw [cosCap_val]; exact Scaled.rep_const _

private def normSquareS : Scaled :=
  ((lS.pow 2).add (cS.pow 2)).sub ((((Scaled.ofNat 2).mul lS).mul cS).mul sinCapS)

private theorem rep_normSquare : normSquareS.Rep normSquare :=
  ((rep_l.pow 2).add (rep_c.pow 2)).sub ((((Scaled.rep_ofNat 2).mul rep_l).mul rep_c).mul rep_sinCap)

private def squareGapS : Scaled := (((Scaled.ofNat 2).mul lS).mul cS).mul (sinCapS.sub sinUpperS)

private theorem rep_squareGap : squareGapS.Rep squareGap :=
  (((Scaled.rep_ofNat 2).mul rep_l).mul rep_c).mul (rep_sinCap.sub rep_sinUpper)

private def demandS : Scaled := (Scaled.const (43/100)).add (cS.mul (cosineS.sub cosCapS))

private theorem rep_demand : demandS.Rep demand :=
  (Scaled.rep_const _).add (rep_c.mul (rep_cosine.sub rep_cosCap))

private def firstSquareS : Scaled := ((Scaled.const (19577/5000)).mul squareGapS).sub (demandS.pow 2)

private theorem rep_firstSquare : firstSquareS.Rep firstSquare :=
  ((Scaled.rep_const _).mul rep_squareGap).sub (rep_demand.pow 2)

private def certificateS : Scaled :=
  (firstSquareS.pow 2).sub ((((Scaled.ofNat 4).mul (Scaled.const (19577/5000))).mul
    (demandS.pow 2)).mul normSquareS)

private theorem rep_certificate : certificateS.Rep certificate :=
  (rep_firstSquare.pow 2).sub ((((Scaled.rep_ofNat 4).mul (Scaled.rep_const _)).mul
    (rep_demand.pow 2)).mul rep_normSquare)

/-- The centered polynomials on `[0,1/5]`: `(0+1/5)/2 = (1/5-0)/2 = 1/10`. -/
private theorem rep_centered {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (a.center 1 10 1 1).Rep (centered 0 (1/5) p) :=
  ha.centered 1 10 1 1 (by norm_num) (by norm_num) (by norm_num)

end Certificates

theorem demand_identity : centered 0 (1/5) demand=
    expansion 18 (centered 0 (1/5) demand) := by
  exact (rep_centered rep_demand).eq_expansion (by decide +kernel) (by decide +kernel)

theorem firstSquare_identity : centered 0 (1/5) firstSquare=
    expansion 36 (centered 0 (1/5) firstSquare) := by
  exact (rep_centered rep_firstSquare).eq_expansion (by decide +kernel) (by decide +kernel)

theorem certificate_identity : centered 0 (1/5) certificate=
    expansion 72 (centered 0 (1/5) certificate) := by
  exact (rep_centered rep_certificate).eq_expansion (by decide +kernel) (by decide +kernel)

theorem demand_reserve : (63/100 : ℚ)<lowerOn 18 0 (1/5) demand := by
  rw [Certificate.lowerOn_eq_of_rep (rep_centered rep_demand) (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 63) (d := 100) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem firstSquare_reserve : (17/10 : ℚ)<lowerOn 36 0 (1/5) firstSquare := by
  rw [Certificate.lowerOn_eq_of_rep (rep_centered rep_firstSquare) (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 17) (d := 10) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem certificate_reserve : (4/25 : ℚ)<lowerOn 72 0 (1/5) certificate := by
  rw [Certificate.lowerOn_eq_of_rep (rep_centered rep_certificate) (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 4) (d := 25) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem reserves {t : ℝ} (ht : t∈domain .low) :
    63/100<aeval t demand ∧ 17/10<aeval t firstSquare ∧
      4/25<aeval t certificate := by
  have ht' : t∈Set.Icc ((0:ℚ):ℝ) ((1/5:ℚ):ℝ) := by
    simpa [domain] using ht
  have h1 := positive_on_interval (by norm_num) demand_identity demand_reserve ht'
  have h2 := positive_on_interval (by norm_num) firstSquare_identity firstSquare_reserve ht'
  have h3 := positive_on_interval (by norm_num) certificate_identity certificate_reserve ht'
  push_cast at h1 h2 h3
  exact ⟨h1,h2,h3⟩

theorem sinCap_eq : (sinCap:ℝ)=S15 frameCap := by
  norm_num [sinCap,PositiveScalarPolynomials.sine,S15,S13,S11,
    Arithmetic.sin9,Arithmetic.sin7,frameCap]

theorem cosCap_eq : (cosCap:ℝ)=C14 frameCap := by
  norm_num [cosCap,cosLower,PositiveScalarPolynomials.cosine,C14,C12,
    Arithmetic.cos10,Arithmetic.cos8,frameCap]

theorem sinUpper_eval (t : ℝ) : aeval t sinUpper=S13 t := by
  simp only [sinUpper,map_add,map_mul,aeval_C,map_pow,aeval_X,eq_ratCast,
    PositiveScalarPolynomials.sine_eval]
  dsimp only [S15]
  push_cast
  ring

theorem coefficients_eval (t : ℝ) :
    aeval t l=ell .low t ∧ aeval t c=SoleECoefficients.c .low t := by
  have hh := SoleScalarData.polynomial_parameters .low t
  simp only [SoleScalarPolynomials.origin,Rat.cast_zero,sub_zero] at hh
  exact ⟨hh.2.1,hh.2.2.1⟩

theorem normSquare_eval (t : ℝ) : aeval t normSquare=
    (ell .low t)^2+(SoleECoefficients.c .low t)^2-
      2*ell .low t*SoleECoefficients.c .low t*S15 frameCap := by
  simp only [normSquare,map_sub,map_add,map_mul,map_pow,map_ofNat,aeval_C,eq_ratCast,
    (coefficients_eval t).1,(coefficients_eval t).2,sinCap_eq]

theorem squareGap_eval (t : ℝ) : aeval t squareGap=
    2*ell .low t*SoleECoefficients.c .low t*(S15 frameCap-S13 t) := by
  simp only [squareGap,map_sub,map_mul,map_ofNat,aeval_C,eq_ratCast,
    (coefficients_eval t).1,(coefficients_eval t).2,sinCap_eq,sinUpper_eval]

theorem demand_eval (t : ℝ) : aeval t demand=
    43/100+SoleECoefficients.c .low t*(C16 t-C14 frameCap) := by
  simp only [demand,map_add,map_mul,map_sub,aeval_C,eq_ratCast,
    (coefficients_eval t).2,PositiveScalarPolynomials.cosine_eval,cosCap_eq]
  push_cast
  ring

theorem firstSquare_eval (t : ℝ) : aeval t firstSquare=
    qLow*aeval t squareGap-(aeval t demand)^2 := by
  simp [firstSquare,q,qLow]

theorem certificate_eval (t : ℝ) : aeval t certificate=
    (aeval t firstSquare)^2-4*qLow*(aeval t demand)^2*aeval t normSquare := by
  simp only [certificate,map_sub,map_mul,map_pow,map_ofNat,aeval_C,eq_ratCast,q,qLow]
  push_cast
  ring

end SquaresInCircles.Eight.TableFree.SoleLowGapPolynomials
