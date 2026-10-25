module

public import SquaresInCircles.Eight.TableFree.SoleLowGapPolynomials
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Two coefficient comparisons for the middle and high sole-E families

Uncompiled source. The first comparison keeps the correlation between
the two high-family coefficients. The second proves that the actual
middle E-endpoint coefficient is below c, using directed Taylor bounds.
Each is one polynomial inequality on its complete coefficient interval.
The exact reductions have not been run.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SoleBalancedPolynomials
open Polynomial WholeIntervalPolynomial SoleECoefficients HighOrderTaylor

def highNormGap : ℚ[X] := C ((53/50)^2)-
  (SoleScalarPolynomials.k .high)^2*(1+(SoleScalarPolynomials.g .high)^2)

def middleCoefficientGap : ℚ[X] :=
  SoleScalarPolynomials.c .middle-SoleScalarPolynomials.cosine .middle-
    SoleScalarPolynomials.eta .middle*
      SoleLowGapPolynomials.sinUpper.comp (SoleScalarPolynomials.parameter .middle)


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

private theorem rep_sinUpper : sinUpperS.Rep SoleLowGapPolynomials.sinUpper :=
  rep_sine.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

/-- The parameter of the middle family is the affine map of `[-4/5,6/5]`. -/
private theorem middle_shift (p : ℚ[X]) :
    p.comp (SoleScalarPolynomials.parameter .middle)=centered (-4/5) (6/5) p := by
  simp only [SoleScalarPolynomials.parameter,SoleScalarPolynomials.origin,centered,affine]
  norm_num

private def highParameterS : Scaled := (Scaled.const (7/20)).add Scaled.var

private def highNormGapS : Scaled :=
  (Scaled.const ((53/50)^2)).sub
    ((((Scaled.const (1017/1000)).sub ((Scaled.const (1/50)).mul highParameterS)).pow 2).mul
      ((Scaled.ofNat 1).add
        (((Scaled.const (27/100)).add ((Scaled.const (2/25)).mul highParameterS)).pow 2)))

private theorem rep_highNormGap : highNormGapS.Rep highNormGap := by
  have hp : highParameterS.Rep (SoleScalarPolynomials.parameter .high) :=
    (Scaled.rep_const _).add Scaled.rep_var
  exact (Scaled.rep_const _).sub
    ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul hp)).pow 2).mul
      (Scaled.rep_one.add (((Scaled.rep_const _).add ((Scaled.rep_const _).mul hp)).pow 2)))

private def middleCoefficientGapS : Scaled :=
  ((((Scaled.const (209/200)).add ((Scaled.const (13/20)).mul Scaled.var)).sub
    ((Scaled.const (3/2)).mul (Scaled.var.pow 2))).sub (cosineS.center 1 5 1 5)).sub
    (((Scaled.const (319/1000)).add ((Scaled.const (1/5)).mul Scaled.var)).mul
      (sinUpperS.center 1 5 1 5))

private theorem rep_middleCoefficientGap :
    middleCoefficientGapS.Rep middleCoefficientGap := by
  have hc : (cosineS.center 1 5 1 5).Rep (SoleScalarPolynomials.cosine .middle) := by
    rw [SoleScalarPolynomials.cosine,middle_shift]
    exact rep_cosine.centered 1 5 1 5 (by norm_num) (by norm_num) (by norm_num)
  have hs : (sinUpperS.center 1 5 1 5).Rep
      (SoleLowGapPolynomials.sinUpper.comp (SoleScalarPolynomials.parameter .middle)) := by
    rw [middle_shift]
    exact rep_sinUpper.centered 1 5 1 5 (by norm_num) (by norm_num) (by norm_num)
  exact ((((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).sub hc).sub
    (((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).mul hs)

private theorem rep_highNormGap_centered :
    (highNormGapS.center 7 40 1 1).Rep (centered 0 (7/20) highNormGap) :=
  rep_highNormGap.centered 7 40 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem rep_middleCoefficientGap_centered :
    (middleCoefficientGapS.center 3 40 1 1).Rep (centered 0 (3/20) middleCoefficientGap) :=
  rep_middleCoefficientGap.centered 3 40 1 1 (by norm_num) (by norm_num) (by norm_num)

end Certificates

theorem highNormGap_identity : centered 0 (7/20) highNormGap=
    expansion 4 (centered 0 (7/20) highNormGap) := by
  exact rep_highNormGap_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem highNormGap_reserve : (1/200 : ℚ)<lowerOn 4 0 (7/20) highNormGap := by
  rw [Certificate.lowerOn_eq_of_rep rep_highNormGap_centered (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 1) (d := 200) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem middleCoefficientGap_identity : centered 0 (3/20) middleCoefficientGap=
    expansion 16 (centered 0 (3/20) middleCoefficientGap) := by
  exact rep_middleCoefficientGap_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem middleCoefficientGap_reserve :
    (1/10000 : ℚ)<lowerOn 16 0 (3/20) middleCoefficientGap := by
  rw [Certificate.lowerOn_eq_of_rep rep_middleCoefficientGap_centered (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 1) (d := 10000) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem high_norm_square {t : ℝ} (ht : t∈domain .high) :
    (k .high t)^2*(1+(g .high t)^2)<(53/50 : ℝ)^2 := by
  have hz := SoleScalarPolynomials.local_parameter ht
  have hb := positive_on_interval (by norm_num) highNormGap_identity highNormGap_reserve
    (show t-7/20∈Set.Icc ((0:ℚ):ℝ) ((7/20:ℚ):ℝ) by
      simpa [SoleScalarPolynomials.origin,SoleScalarPolynomials.length] using hz)
  have hc := SoleScalarData.polynomial_parameters .high t
  norm_num [SoleScalarPolynomials.origin] at hc
  simp only [highNormGap,map_sub,map_mul,map_pow,map_add,map_one,aeval_C,hc.1,hc.2.2.2.1] at hb
  norm_num at hb
  linarith

theorem middle_p_lt_c {t : ℝ} (ht : t∈domain .middle) :
    p .middle t t<c .middle t := by
  have hz := SoleScalarPolynomials.local_parameter ht
  have hb := positive_on_interval (by norm_num) middleCoefficientGap_identity
    middleCoefficientGap_reserve
    (show t-1/5∈Set.Icc ((0:ℚ):ℝ) ((3/20:ℚ):ℝ) by
      simpa [SoleScalarPolynomials.origin,SoleScalarPolynomials.length] using hz)
  have hc := SoleScalarData.polynomial_parameters .middle t
  have htrig := SoleScalarData.polynomial_trig .middle t
  have hpar : aeval (t-1/5) (SoleScalarPolynomials.parameter .middle)=t := by
    simp [SoleScalarPolynomials.parameter,SoleScalarPolynomials.origin]
  norm_num [SoleScalarPolynomials.origin] at hc htrig
  simp only [middleCoefficientGap,map_sub,map_mul,aeval_comp,hpar,
    SoleLowGapPolynomials.sinUpper_eval,hc.2.2.1,hc.2.2.2.2,htrig.2.1] at hb
  have hs := sin_le_S13 (angle ht).1
  have hcos := cos_le_C16 (angle ht).1
  have heta := (positive ht).2.2.2.2
  have hm := mul_le_mul_of_nonneg_left hs heta
  simp only [p,show Band.middle≠Band.high by decide,if_false]
  norm_num at hb
  linarith

end SquaresInCircles.Eight.TableFree.SoleBalancedPolynomials
