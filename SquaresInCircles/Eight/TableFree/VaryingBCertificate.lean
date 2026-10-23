module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
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
namespace SquaresInCircles.Eight.TableFree.VaryingBCertificate
open Polynomial WholeIntervalPolynomial

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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem double_zero_identity : X^2*certificate=numerator := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem expansion_identity :
    centered 0 (7/10) certificate=expansion 70 (centered 0 (7/10) certificate) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserve : (317/4000 : ℚ)<lowerOn 70 0 (7/10) certificate := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sign_expansions :
    centered 0 (7/10) (r-S9)=expansion 9 (centered 0 (7/10) (r-S9)) ∧
    centered 0 (7/10) (2*r-A*S9)=expansion 11 (centered 0 (7/10) (2*r-A*S9)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sign_reserves :
    (19/200 : ℚ)<lowerOn 9 0 (7/10) (r-S9) ∧
    (2511/5000 : ℚ)<lowerOn 11 0 (7/10) (2*r-A*S9) := by decide

theorem polynomial_positive {d : ℝ} (hd : d∈Set.Icc 0 frameCap) :
    (317/4000 : ℝ)<aeval d certificate := by
  exact positive_on_interval (by norm_num) expansion_identity coefficient_reserve
    (by simpa [frameCap] using hd)

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
  exact ⟨positive_on_interval (by norm_num) sign_expansions.1 sign_reserves.1
      (by simpa [frameCap] using hd),
    positive_on_interval (by norm_num) sign_expansions.2 sign_reserves.2
      (by simpa [frameCap] using hd)⟩

@[simp] theorem r_eval (d : ℝ) : aeval d r=PositiveStressCoefficients.ratio d := by
  simp [r,PositiveStressCoefficients.ratio]

@[simp] theorem S9_eval (d : ℝ) : aeval d S9=Arithmetic.sin9 d := by
  simp [S9,Arithmetic.sin9,Arithmetic.sin7]
  ring

@[simp] theorem S11_eval (d : ℝ) : aeval d S11=HighOrderTaylor.S11 d := by
  simp [S11,HighOrderTaylor.S11]

@[simp] theorem C10_eval (d : ℝ) : aeval d C10=Arithmetic.cos10 d := by
  simp [C10,Arithmetic.cos10,Arithmetic.cos8]
  ring

@[simp] theorem C12_eval (d : ℝ) : aeval d C12=HighOrderTaylor.C12 d := by
  simp [C12,HighOrderTaylor.C12]

end SquaresInCircles.Eight.TableFree.VaryingBCertificate
