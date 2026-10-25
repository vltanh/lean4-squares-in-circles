module

public import SquaresInCircles.Eight.TableFree.PolynomialCertificates
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor
public import SquaresInCircles.Eight.TableFree.PositiveStressCoefficients

/-!
# The degree-70 whole-interval polynomial for the varying B coefficient

Uncompiled source draft of (15)--(16) in the positive-GA angular envelope.
The exact double zero is removed algebraically by `divX` twice. Every
coefficient calculation is specified from the polynomial formula and uses
kernel reduction, with no native evaluation or external certificate data.
The calculations below have not been executed.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.VaryingBCertificate
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

def r : ℚ[X] := C (117/200)+C (51/200)*X
def S9 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+C (1/362880)*X^9
def S11 : ℚ[X] := S9-C (1/39916800)*X^11
def C10 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+
  C (1/40320)*X^8-C (1/3628800)*X^10
def C12 : ℚ[X] := C10+C (1/479001600)*X^12
def A : ℚ[X] := 1+r^2
def Bminus : ℚ[X] := A-2*r*S9
def Bplus : ℚ[X] := A-2*r*S11
def H : ℚ[X] := C (9789/2500)*r^2*S11*(2*r-A*S9)+(1-C12)^2*A*Bminus
def numerator : ℚ[X] := H^2-C (4*(9789/2500))*((1-C10)^2)*A*Bplus^2
def certificate : ℚ[X] := numerator.divX.divX

/-! The polynomials of this file as scaled integer coefficient lists. -/

private def rS : Scaled := (Scaled.const (117/200)).add ((Scaled.const (51/200)).mul Scaled.var)
private def S9S : Scaled :=
  (((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))
private def S11S : Scaled := S9S.sub ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))
private def C10S : Scaled :=
  ((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8)) |>.sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))
private def C12S : Scaled := C10S.add ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))
private def AS : Scaled := (Scaled.ofNat 1).add (rS.pow 2)
private def BminusS : Scaled := AS.sub (((Scaled.ofNat 2).mul rS).mul S9S)
private def BplusS : Scaled := AS.sub (((Scaled.ofNat 2).mul rS).mul S11S)
private def HS : Scaled :=
  ((((Scaled.const (9789/2500)).mul (rS.pow 2)).mul S11S).mul
    (((Scaled.ofNat 2).mul rS).sub (AS.mul S9S))).add
  ((((Scaled.ofNat 1).sub C12S).pow 2).mul AS |>.mul BminusS)
private def numeratorS : Scaled :=
  (HS.pow 2).sub
    ((((Scaled.const (4*(9789/2500))).mul (((Scaled.ofNat 1).sub C10S).pow 2)).mul
      AS).mul (BplusS.pow 2))
private def certificateS : Scaled := numeratorS.divX.divX
private def sign1S : Scaled := rS.sub S9S
private def sign2S : Scaled := ((Scaled.ofNat 2).mul rS).sub (AS.mul S9S)

private theorem rep_r : rS.Rep r :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)

private theorem rep_S9 : S9S.Rep S9 :=
  ((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9)))

private theorem rep_S11 : S11S.Rep S11 :=
  rep_S9.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))

private theorem rep_C10 : C10S.Rep C10 :=
  ((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))

private theorem rep_C12 : C12S.Rep C12 :=
  rep_C10.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))

private theorem rep_A : AS.Rep A := Scaled.rep_one.add (rep_r.pow 2)

private theorem rep_Bminus : BminusS.Rep Bminus :=
  rep_A.sub (((Scaled.rep_ofNat 2).mul rep_r).mul rep_S9)

private theorem rep_Bplus : BplusS.Rep Bplus :=
  rep_A.sub (((Scaled.rep_ofNat 2).mul rep_r).mul rep_S11)

private theorem rep_sign1 : sign1S.Rep (r-S9) := rep_r.sub rep_S9

private theorem rep_sign2 : sign2S.Rep (2*r-A*S9) :=
  ((Scaled.rep_ofNat 2).mul rep_r).sub (rep_A.mul rep_S9)

private theorem rep_H : HS.Rep H :=
  ((((Scaled.rep_const _).mul (rep_r.pow 2)).mul rep_S11).mul rep_sign2).add
    ((((Scaled.rep_one.sub rep_C12).pow 2).mul rep_A).mul rep_Bminus)

private theorem rep_numerator : numeratorS.Rep numerator :=
  (rep_H.pow 2).sub ((((Scaled.rep_const _).mul ((Scaled.rep_one.sub rep_C10).pow 2)).mul
    rep_A).mul (rep_Bplus.pow 2))

private theorem rep_certificate : certificateS.Rep certificate := rep_numerator.divX.divX

/-- The centered polynomials on `[0,7/10]`: `(0+7/10)/2 = (7/10-0)/2 = 7/20`. -/
private theorem rep_centered {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (c.center 7 20 1 1).Rep (centered 0 (7/10) p) :=
  hc.centered 7 20 1 1 (by norm_num) (by norm_num) (by norm_num)

theorem double_zero_identity : X^2*certificate=numerator := by
  have hs : numeratorS.s≠0 := by decide +kernel
  have hc := rep_numerator.coeff hs
  have h0 : numerator.coeff 0=0 := by
    rw [hc,show numeratorS.l.getD 0 0=0 by decide +kernel]; simp
  have h1 : numerator.coeff 1=0 := by
    rw [hc,show numeratorS.l.getD 1 0=0 by decide +kernel]; simp
  have e1 : X*numerator.divX=numerator := by
    have h := X_mul_divX_add numerator
    rwa [h0,map_zero,add_zero] at h
  have e2 : X*numerator.divX.divX=numerator.divX := by
    have h := X_mul_divX_add numerator.divX
    rwa [coeff_divX,zero_add,h1,map_zero,add_zero] at h
  rw [certificate,pow_two,mul_assoc,e2,e1]

theorem expansion_identity :
    centered 0 (7/10) certificate=expansion 70 (centered 0 (7/10) certificate) :=
  (rep_centered rep_certificate).eq_expansion (by decide +kernel) (by decide +kernel)

theorem coefficient_reserve : (317/4000 : ℚ)<lowerOn 70 0 (7/10) certificate := by
  rw [lowerOn_eq_of_rep (rep_centered rep_certificate) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem sign_expansions :
    centered 0 (7/10) (r-S9)=expansion 9 (centered 0 (7/10) (r-S9)) ∧
    centered 0 (7/10) (2*r-A*S9)=expansion 11 (centered 0 (7/10) (2*r-A*S9)) :=
  ⟨(rep_centered rep_sign1).eq_expansion (by decide +kernel) (by decide +kernel),
    (rep_centered rep_sign2).eq_expansion (by decide +kernel) (by decide +kernel)⟩

theorem sign_reserves :
    (19/200 : ℚ)<lowerOn 9 0 (7/10) (r-S9) ∧
    (2511/5000 : ℚ)<lowerOn 11 0 (7/10) (2*r-A*S9) := by
  rw [lowerOn_eq_of_rep (rep_centered rep_sign1) (by decide +kernel) (by decide +kernel),
    lowerOn_eq_of_rep (rep_centered rep_sign2) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem polynomial_positive {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    (317/4000 : ℝ)<aeval d certificate := by
  have h := positive_on_interval (by norm_num) expansion_identity coefficient_reserve
    (by simpa [frameCap] using hd)
  rwa [show ((317/4000 : ℚ) : ℝ)=317/4000 by norm_num] at h

theorem numerator_positive {d : ℝ} (hd : d∈Set.Ioc 0 frameCap) :
    0<aeval d numerator := by
  have hp := polynomial_positive (Set.Ioc_subset_Icc_self hd)
  have he := congrArg (fun p : ℚ[X] => aeval d p) double_zero_identity
  simp only [map_mul,map_pow,aeval_X] at he
  rw [← he]
  exact mul_pos (sq_pos_of_pos hd.1) (by linarith)

theorem sign_bounds {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    (19/200 : ℝ)<aeval d (r-S9) ∧
    (2511/5000 : ℝ)<aeval d (2*r-A*S9) := by
  have h1 := positive_on_interval (by norm_num) sign_expansions.1 sign_reserves.1
    (by simpa [frameCap] using hd)
  have h2 := positive_on_interval (by norm_num) sign_expansions.2 sign_reserves.2
    (by simpa [frameCap] using hd)
  rw [show ((19/200 : ℚ) : ℝ)=19/200 by norm_num] at h1
  rw [show ((2511/5000 : ℚ) : ℝ)=2511/5000 by norm_num] at h2
  exact ⟨h1,h2⟩

@[simp] theorem r_eval (d : ℝ) : aeval d r=PositiveStressCoefficients.ratio d := by
  simp [r,PositiveStressCoefficients.ratio]

@[simp] theorem S9_eval (d : ℝ) : aeval d S9=Arithmetic.sin9 d := by
  simp [S9,Arithmetic.sin9,Arithmetic.sin7]
  ring

@[simp] theorem S11_eval (d : ℝ) : aeval d S11=HighOrderTaylor.S11 d := by
  simp [S11,HighOrderTaylor.S11]
  ring

@[simp] theorem C10_eval (d : ℝ) : aeval d C10=Arithmetic.cos10 d := by
  simp [C10,Arithmetic.cos10,Arithmetic.cos8]
  ring

@[simp] theorem C12_eval (d : ℝ) : aeval d C12=HighOrderTaylor.C12 d := by
  simp [C12,HighOrderTaylor.C12]
  ring

end SquaresInCircles.Eight.TableFree.VaryingBCertificate
