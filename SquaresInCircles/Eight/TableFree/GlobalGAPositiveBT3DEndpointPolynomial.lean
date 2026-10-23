module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3Data
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# The three independent sorted-D endpoint certificates

Uncompiled transcription of the complete positive-BT3 sorted-D endpoint
note. The two degree-eighteen polynomials retain the specified whole
interval coefficient bounds. The degree-twenty-four axis polynomial
retains its single translated quadratic and complete higher-order tail.
The exact rational reductions below are proof terms, not evaluations.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.DEndpoint
open Polynomial WholeIntervalPolynomial
open PositiveTD.Certificate (S9 S11 C10 C12)

inductive End where | one | upper
  deriving DecidableEq, Fintype
def coefficient : End→ℚ | .one=>1 | .upper=>5821/5000
abbrev Q : ℚ := 9789/2500
abbrev kstar : ℚ := 1673/2500
abbrev h : ℚ := 7/10
abbrev cut : ℚ := 3/8
abbrev cLower : ℚ := 449607/500000
abbrev aUpper : ℚ := 1414575672/1000000000
abbrev Tzero : ℚ := 2380990934/1000000000
def phiLower : ℚ := C10.eval h+S11.eval h
def constant (e : End) : ℚ :=
  coefficient e*phiLower+1+(coefficient e+1)*(cLower-1/2)+(13/20)*h-Tzero
def P (e : End) : ℚ[X] :=
  C (1+(coefficient e)^2)+C (2*coefficient e)*S9.comp (C h-X)
def H : ℚ[X] := C (1+kstar^2)-C (2*kstar)*S9
def Z (e : End) : ℚ[X] :=
  C (4*(constant e)^2*Q)*H-(C Q*(P e-H)-C ((constant e)^2))^2
def axisConstant : ℚ :=
  (phiLower-1)/2-aUpper*S9.eval h+2*cLower+(13/20)*h+1/2-Tzero
def axisA : ℚ[X] := C axisConstant-C (aUpper+1/2)*C12+C (1/2)*S11
def Y : ℚ[X] := C Q*H-axisA^2
def shiftedY : ℚ[X] := Y.comp (C (9/20)+X)
def y (j : ℕ) : ℚ := shiftedY.coeff j
def tailBudget : ℚ := ∑ j : Fin 22,|y (j.val+3)|*(1/4)^(j.val+1)
def quadratic : ℚ := y 2-tailBudget
def monomialExpansion : ℚ[X] := C (y 0)+C (y 1)*X+C (y 2)*X^2+
  ∑ j : Fin 22,C (y (j.val+3))*X^(j.val+3)

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=(p.eval r:ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem positive_constants (e : End) : (32/25:ℚ)<constant e := by
  cases e <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_expansion : centered 0 h (Z .upper)=expansion 18 (centered 0 h (Z .upper)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem upper_reserve : (139/1000:ℚ)<lowerOn 18 0 h (Z .upper) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem one_derivative_expansion : centered 0 cut (Z .one).derivative=
    expansion 17 (centered 0 cut (Z .one).derivative) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem one_derivative_reserve : upperOn 17 0 cut (Z .one).derivative<-(623/100:ℚ) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem one_endpoint : (57/250:ℚ)<(Z .one).eval cut := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem axis_expansion : shiftedY=monomialExpansion := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem axis_reserve : (877/500:ℚ)<quadratic ∧
    (1/1000:ℚ)<y 0-(y 1)^2/(4*quadratic) := by decide

theorem upper_positive {n : ℝ} (hn : n∈Icc 0 (7/10:ℝ)) :
    (139/1000:ℝ)<aeval n (Z .upper) :=
  positive_on_interval (by norm_num [h]) upper_expansion upper_reserve hn

theorem one_derivative_negative {n : ℝ} (hn : n∈Icc 0 (3/8:ℝ)) :
    aeval n (Z .one).derivative<-(623/100:ℝ) := by
  have hb := (interval_bounds (by norm_num [cut] : (0:ℚ)<cut) one_derivative_expansion hn).2
  have hr : (upperOn 17 0 cut (Z .one).derivative:ℝ)<-(623/100:ℝ) := by
    exact_mod_cast one_derivative_reserve
  exact hb.trans_lt hr

theorem one_positive {n : ℝ} (hn : n∈Icc 0 (3/8:ℝ)) :
    (57/250:ℝ)<aeval n (Z .one) := by
  have ha : AntitoneOn (fun n : ℝ => aeval n (Z .one)) (Icc (0:ℝ) (3/8)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun n _ => (CenteredMonomialBounds.aeval_hasDerivAt (Z .one) n).continuousAt.continuousWithinAt)
      (fun n _ => CenteredMonomialBounds.aeval_hasDerivAt (Z .one) n)
    intro n hn
    linarith [one_derivative_negative (Ioo_subset_Icc_self hn)]
  have hh := ha hn (show (3/8:ℝ)∈Icc 0 (3/8) by norm_num) hn.2
  have he : (57/250:ℝ)<aeval (3/8:ℝ) (Z .one) := by
    have hr : (57/250:ℝ)<((Z .one).eval cut:ℝ) := by exact_mod_cast one_endpoint
    simpa only [← rational_aeval,cut] using hr
  exact he.trans_le hh

theorem axis_tail {z : ℝ} (hz : |z|≤1/4) (j : Fin 22) :
    -(|(y (j.val+3):ℝ)|*(1/4)^(j.val+1))*z^2≤
      (y (j.val+3):ℝ)*z^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (y (j.val+3):ℝ))
  have hh : |(y (j.val+3):ℝ)*z^(j.val+1)|≤
      |(y (j.val+3):ℝ)|*(1/4)^(j.val+1) := by simpa [abs_mul,abs_pow] using hm
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hh).1 (sq_nonneg z)
  have he : z^(j.val+3)=z^(j.val+1)*z^2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  nlinarith

theorem axis_quadratic_lower {z : ℝ} (hz : |z|≤1/4) :
    (y 0:ℝ)+(y 1:ℝ)*z+(quadratic:ℝ)*z^2≤aeval z shiftedY := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => axis_tail hz j)
  have he : ∑j:Fin 22,-(|(y (j.val+3):ℝ)|*(1/4)^(j.val+1))*z^2=
      -(tailBudget:ℝ)*z^2 := by
    simp [tailBudget,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hs
  rw [axis_expansion]
  simp only [monomialExpansion,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X]
  dsimp [quadratic]
  push_cast
  linarith

theorem axis_positive {n : ℝ} (hn : n∈Icc (3/8:ℝ) (7/10:ℝ)) :
    (1/1000:ℝ)<aeval n Y := by
  let z : ℝ := n-9/20
  have hz : |z|≤1/4 := by
    dsimp [z]
    apply abs_le.mpr
    constructor <;> linarith [hn.1,hn.2]
  have hq : (0:ℝ)<(quadratic:ℝ) := by
    have hh : (877/500:ℝ)<(quadratic:ℝ) := by exact_mod_cast axis_reserve.1
    linarith
  have hr : (1/1000:ℝ)<(y 0:ℝ)-(y 1:ℝ)^2/(4*(quadratic:ℝ)) := by
    exact_mod_cast axis_reserve.2
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(y 0:ℝ)) (b:=(y 1:ℝ)) (x:=z) hq
  have hh := axis_quadratic_lower hz
  have he : aeval z shiftedY=aeval n Y := by
    rw [shiftedY,aeval_comp]
    congr 1
    simp [z]
    ring
  rw [he] at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3.DEndpoint
