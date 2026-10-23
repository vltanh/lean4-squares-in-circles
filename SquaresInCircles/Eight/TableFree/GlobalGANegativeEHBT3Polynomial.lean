module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3PolynomialData

/-!
# Whole-interval positivity of all EH1/BT3 endpoint numerators

Uncompiled Section 8, equations (55)--(58). Each exact finite transform
covers its full native interval. The two small-high H/G alternatives
retain their constant and first quotient. Every other numerator uses
its stated coefficient-norm reserve directly, with no angular mesh.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Certificate
open WholeIntervalPolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seed_certificate : ∀r : Row,∀ep : Split,∀i : Fin 4,active r i →
    0<rho r ep i ∧ (rho r ep i-1/2000000000000)^2≤(P r ep i).eval 0 ∧
      (P r ep i).eval 0<(rho r ep i+1/2000000000000)^2 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate : ∀r : Row,∀ep : Split,∀i : Fin 4,
    centered 0 (width r) (mass r ep i)=expansion 3 (centered 0 (width r) (mass r ep i)) ∧
    (if active r i then massReserve r else 0)<lowerOn 3 0 (width r) (mass r ep i) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem direct_certificate : ∀r : Row,∀ep : Split,affineCertificate r=false →
    centered 0 (width r) (numerator r ep)=
      expansion 39 (centered 0 (width r) (numerator r ep)) ∧
    reserve r<lowerOn 39 0 (width r) (numerator r ep) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem affine_certificate : ∀r : Row,∀ep : Split,affineCertificate r=true →
    numerator r ep=C ((numerator r ep).coeff 0)+X*quotient r ep ∧
    (13/2000:ℚ)<(numerator r ep).coeff 0 ∧
    centered 0 (width r) (quotient r ep)=
      expansion 38 (centered 0 (width r) (quotient r ep)) ∧
    (1/250:ℚ)<lowerOn 38 0 (width r) (quotient r ep) := by decide

theorem mass_positive (r : Row) (ep : Split) (i : Fin 4) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (mass r ep i) := by
  have hc := mass_certificate r ep i
  have hh := positive_on_interval (interval_positive r) hc.1 hc.2 hx
  have hreserve : (0:ℝ)≤((if active r i then massReserve r else 0:ℚ):ℝ) := by
    split_ifs
    · cases r <;> norm_num [massReserve,family]
    · norm_num
  exact hreserve.trans_lt hh

theorem numerator_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (numerator r ep) := by
  cases ha : affineCertificate r
  · have hc := direct_certificate r ep ha
    have hh := positive_on_interval (interval_positive r) hc.1 hc.2 hx
    have hr : (0:ℝ)<(reserve r:ℝ) := by cases r <;> norm_num [reserve,family]
    exact hr.trans hh
  · have hc := affine_certificate r ep ha
    have hq := positive_on_interval (interval_positive r) hc.2.2.1 hc.2.2.2 hx
    have hconst : (13/2000:ℝ)<((numerator r ep).coeff 0:ℝ) := by exact_mod_cast hc.2.1
    have he := congrArg (fun p : ℚ[X] => aeval x p) hc.1
    simp only [map_add,map_mul,aeval_C,aeval_X] at he
    have hm := mul_nonneg hx.1 (show 0≤aeval x (quotient r ep) by linarith)
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Certificate
