module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeMinimumCalculus
public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# Whole-height polynomial signs for the negative-core minimum

The degree-eight denominator difference has one coefficient-norm bound
on [1.68,1.915]. The first stationary numerator uses its exact endpoint
quotient on that same interval; the second uses [1.68,1.74]. Each input
is the displayed symbolic polynomial. No target subdivision, sampled
values, or supplied coefficient table is used. Uncompiled source draft.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
open Polynomial WholeIntervalPolynomial

def q : ℚ := 9789/2500
def t : ℚ[X] := C (q+1)-C 2*X
def w : ℚ[X] := C q-X^2
def b : ℚ[X] := C 2*X^2-C (4*q)*X+C (q*(q+1))
def bd : ℚ[X] := C 4*X-C (4*q)
def a : ℚ[X] := b*X^2*t-w*(bd*X*t-b*(C 3*t-C 4*X))
def d : ℚ[X] := X^5*t^3-a
def c (h : ℚ) : ℚ[X] :=
  let s := C (h^2)*t-1
  C (3*h^2*q)*X*t^2*s-C (h^4)*w*X^2*t^2-C (4*h^2)*w*X^2*t*s+
    C (3*q)*t^2*s^2-C (6*q)*X*t*s^2+C 8*w*X^2*s^2
def cg : ℚ[X] := c (98439/100000)
def endpointQuotient : ℚ[X] :=
  -∑ n∈Finset.range 6,C (cg.coeff (n+1))*
    ∑ i∈Finset.range (n+1),C ((383/200:ℚ)^(n-i))*X^i

lemma d_evaluation (u : ℝ) : aeval u d=D0 u := by
  simp [d,a,b,bd,t,w,q,D0,A0,baseE,baseEd,Q0]
  ring

lemma c_evaluation (h : ℚ) (u : ℝ) : aeval u (c h)=Ch (h:ℝ) u := by
  simp [c,t,w,q,Ch,Q0]
  push_cast
  ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem d_expansion : centered (42/25) (383/200) d=
    expansion 8 (centered (42/25) (383/200) d) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem d_reserve : (27:ℚ)<lowerOn 8 (42/25) (383/200) d := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_identity : (C (383/200)-X)*endpointQuotient=cg-C (cg.eval (383/200)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_expansion : centered (42/25) (383/200) endpointQuotient=
    expansion 5 (centered (42/25) (383/200) endpointQuotient) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_reserve : (14:ℚ)<lowerOn 5 (42/25) (383/200) endpointQuotient := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem endpoint_reserve : (1/20:ℚ)<cg.eval (383/200) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem second_expansion : centered (42/25) (87/50) (c (39/40))=
    expansion 6 (centered (42/25) (87/50) (c (39/40))) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem second_reserve : (2:ℚ)<lowerOn 6 (42/25) (87/50) (c (39/40)) := by decide

theorem D0_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<D0 u := by
  have hh := positive_on_interval (by norm_num) d_expansion d_reserve hu
  rw [d_evaluation] at hh
  linarith

theorem Ch_first_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<Ch g u := by
  have hq := positive_on_interval (by norm_num) quotient_expansion quotient_reserve hu
  have hp := mul_nonneg (show 0≤(383/200:ℝ)-u by linarith [hu.2])
    (show 0≤aeval u endpointQuotient by linarith)
  have hid := congrArg (fun p : ℚ[X] => aeval u p) quotient_identity
  simp only [map_mul,map_sub,aeval_C,aeval_X] at hid
  have he : (1/20:ℝ)<(cg.eval (383/200):ℝ) := by exact_mod_cast endpoint_reserve
  have hc : aeval u cg=Ch g u := by
    simpa [cg,g,EdgeThreeAligned.gn] using c_evaluation (98439/100000) u
  rw [hc] at hid
  linarith

theorem Ch_second_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (87/50)) : 0<Ch (39/40) u := by
  have hh := positive_on_interval (by norm_num) second_expansion second_reserve hu
  rw [c_evaluation] at hh
  norm_num at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
