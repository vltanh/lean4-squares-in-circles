module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2PolynomialData
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3DEnvelopeGeometry

/-!
# Eight squares: two whole-interval slope reserves for negative EH

The first quartic uses
the prescribed centered quadratic completion. The second uses its
displayed coefficients at the intrinsic ratio endpoint `3/5`.
-/

section
/-!
## The three independent sorted-D endpoint certificates

The two degree-eighteen polynomials retain the specified whole
interval coefficient bounds. The degree-twenty-four axis polynomial
retains its single translated quadratic and complete higher-order tail.
The exact rational reductions below are proof terms, not evaluations.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
open Polynomial WholeIntervalPolynomial
open PositiveBT3
open PositiveTD.Certificate (S9 S11 C10 C12)

inductive End where | one | upper
  deriving DecidableEq

instance : Fintype End where
  elems := {.one, .upper}
  complete x := by cases x <;> decide
def coefficient : End→ℚ | .one=>1 | .upper=>6/5
abbrev Q : ℚ := 9789/2500
abbrev kstar : ℚ := 17/25
abbrev h : ℚ := 7/10
abbrev cut : ℚ := 3/8
abbrev cLower : ℚ := 449607/500000
abbrev aUpper : ℚ := 1414575672/1000000000
abbrev Tzero : ℚ := 2392942424/1000000000
def phiLower : ℚ := C10.eval h+S11.eval h
def constant (e : End) : ℚ :=
  coefficient e*phiLower+1+(coefficient e+1)*(cLower-1/2)+(67/100)*h-Tzero
def P (e : End) : ℚ[X] :=
  C (1+(coefficient e)^2)+C (2*coefficient e)*S9.comp (C h-X)
def H : ℚ[X] := C (1+kstar^2)-C (2*kstar)*S9
def Z (e : End) : ℚ[X] :=
  C (4*(constant e)^2*Q)*H-(C Q*(P e-H)-C ((constant e)^2))^2
def axisConstant : ℚ :=
  (phiLower-1)/2-aUpper*S9.eval h+2*cLower+(67/100)*h+1/2-Tzero
def axisA : ℚ[X] := C axisConstant-C (aUpper+1/2)*C12+C (1/2)*S11
def Y : ℚ[X] := C Q*H-axisA^2
def shiftedY : ℚ[X] := Y.comp (C (9/20)+X)
def y (j : ℕ) : ℚ := shiftedY.coeff j
def tailBudget : ℚ := ∑ j : Fin 22,|y (j.val+3)| *(1/4)^(j.val+1)
def quadratic : ℚ := y 2-tailBudget
def monomialExpansion : ℚ[X] := C (y 0)+C (y 1)*X+C (y 2)*X^2+
  ∑ j : Fin 22,C (y (j.val+3))*X^(j.val+3)

theorem rational_aeval (p : ℚ[X]) (r : ℚ) : aeval (r:ℝ) p=((p.eval r:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp


/-! ### Kernel certificates for the three polynomials

The polynomials are represented as scaled integer coefficient lists
(`WholeIntervalPolynomial.Certificate`), mirroring their definitions. -/

open WholeIntervalPolynomial.Certificate in
/-- The degree-nine sine polynomial composed with a represented polynomial. -/
private def r40_S9of (v : Scaled) : Scaled :=
  (((v.sub ((Scaled.const (1/6)).mul (v.pow 3))).add
    ((Scaled.const (1/120)).mul (v.pow 5))).sub
    ((Scaled.const (1/5040)).mul (v.pow 7))).add
    ((Scaled.const (1/362880)).mul (v.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_S9of {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r40_S9of v).Rep (S9.comp q) := by
  have e : S9.comp q=q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,PositiveTD.Certificate.S5,sub_comp,add_comp,mul_comp,C_comp,X_comp,
      pow_comp]
  rw [e]
  exact (((hv.sub ((Scaled.rep_const _).mul (hv.pow 3))).add
    ((Scaled.rep_const _).mul (hv.pow 5))).sub
    ((Scaled.rep_const _).mul (hv.pow 7))).add
    ((Scaled.rep_const _).mul (hv.pow 9))

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_S9 : (r40_S9of Scaled.var).Rep S9 := by
  simpa only [comp_X] using r40_rep_S9of Scaled.rep_var

open WholeIntervalPolynomial.Certificate in
private def r40_S11S : Scaled :=
  (r40_S9of Scaled.var).sub ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_S11 : r40_S11S.Rep S11 :=
  r40_rep_S9.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))

open WholeIntervalPolynomial.Certificate in
private def r40_C12S : Scaled :=
  ((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))).add
    ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_C12 : r40_C12S.Rep C12 :=
  (((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))

open WholeIntervalPolynomial.Certificate in
private def r40_HS : Scaled :=
  (Scaled.const (1+kstar^2)).sub ((Scaled.const (2*kstar)).mul (r40_S9of Scaled.var))

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_H : r40_HS.Rep H :=
  (Scaled.rep_const _).sub ((Scaled.rep_const _).mul r40_rep_S9)

open WholeIntervalPolynomial.Certificate in
private def r40_PS (c : ℚ) : Scaled :=
  (Scaled.const (1+c^2)).add
    ((Scaled.const (2*c)).mul (r40_S9of ((Scaled.const h).sub Scaled.var)))

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_P (e : End) : (r40_PS (coefficient e)).Rep (P e) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul
    (r40_rep_S9of ((Scaled.rep_const _).sub Scaled.rep_var)))

open WholeIntervalPolynomial.Certificate in
private def r40_ZS (c k : ℚ) : Scaled :=
  ((Scaled.const (4*k^2*Q)).mul r40_HS).sub
    ((((Scaled.const Q).mul ((r40_PS c).sub r40_HS)).sub (Scaled.const (k^2))).pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_Z (e : End) {k : ℚ} (hk : constant e=k) :
    (r40_ZS (coefficient e) k).Rep (Z e) := by
  rw [Z,hk]
  exact ((Scaled.rep_const _).mul r40_rep_H).sub
    ((((Scaled.rep_const _).mul ((r40_rep_P e).sub r40_rep_H)).sub
      (Scaled.rep_const _)).pow 2)

private theorem r40_constant_one :
    constant .one=731928957688448981/570240000000000000 := by
  norm_num [constant,coefficient,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
    PositiveTD.Certificate.S5,h,cLower,Tzero]

private theorem r40_constant_upper :
    constant .upper=781799147105408981/475200000000000000 := by
  norm_num [constant,coefficient,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
    PositiveTD.Certificate.S5,h,cLower,Tzero]

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_upper_centered :
    ((r40_ZS (6/5) (781799147105408981/475200000000000000)).center 7 20 1 1).Rep
      (centered 0 h (Z .upper)) :=
  (r40_rep_Z .upper r40_constant_upper).centered 7 20 1 1 (by norm_num) (by norm_num [h])
    (by norm_num [h])


open WholeIntervalPolynomial.Certificate in
/-- The coefficient list of the derivative. -/
private def r40_derivL : List ℤ → List ℤ
  | [] => []
  | [_] => []
  | _ :: b :: l => Certificate.add (b :: l) (0 :: r40_derivL (b :: l))

open WholeIntervalPolynomial.Certificate in
private theorem r40_toPoly_derivL : ∀ l : List ℤ,toPoly (r40_derivL l)=derivative (toPoly l)
  | [] => by simp [r40_derivL,toPoly]
  | [a] => by simp [r40_derivL,toPoly]
  | a :: b :: l => by
    rw [r40_derivL,toPoly_add]
    have ih := r40_toPoly_derivL (b :: l)
    simp only [toPoly] at ih ⊢
    rw [ih]
    simp only [Int.cast_zero,map_zero,zero_add,derivative_add,derivative_C,derivative_mul,
      derivative_X,one_mul]

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_derivative {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (⟨r40_derivL c.l,c.s⟩ : Scaled).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [r40_toPoly_derivL,hc,derivative_C_mul]

/-- Horner evaluation of a coefficient list. -/
private def r40_evalL (r : ℚ) : List ℤ → ℚ
  | [] => 0
  | a :: l => a+r*r40_evalL r l

open WholeIntervalPolynomial.Certificate in
private theorem r40_eval_toPoly (r : ℚ) : ∀ l : List ℤ,(toPoly l).eval r=r40_evalL r l
  | [] => by simp [toPoly,r40_evalL]
  | a :: l => by simp [toPoly,r40_evalL,r40_eval_toPoly r l]

open WholeIntervalPolynomial.Certificate in
private theorem r40_eval_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) (r : ℚ) :
    p.eval r=r40_evalL r c.l/c.s := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have he := congrArg (eval r) hc
  rw [r40_eval_toPoly,eval_mul,eval_C] at he
  rw [he]
  field_simp

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_one_derivative_centered :
    ((⟨r40_derivL (r40_ZS 1 (731928957688448981/570240000000000000)).l,
      (r40_ZS 1 (731928957688448981/570240000000000000)).s⟩ : Scaled).center 3 16 1 1).Rep
      (centered 0 cut (Z .one).derivative) :=
  (r40_rep_derivative (r40_rep_Z .one r40_constant_one)).centered 3 16 1 1 (by norm_num)
    (by norm_num [cut]) (by norm_num [cut])

private theorem r40_axisConstant :
    axisConstant=-23684858189154563397049/71280000000000000000000 := by
  norm_num [axisConstant,phiLower,C10,PositiveTD.Certificate.C4,S11,S9,
    PositiveTD.Certificate.S5,h,cLower,aUpper,Tzero]

open WholeIntervalPolynomial.Certificate in
private def r40_YS : Scaled :=
  ((Scaled.const Q).mul r40_HS).sub
    ((((Scaled.const (-23684858189154563397049/71280000000000000000000)).sub
      ((Scaled.const (aUpper+1/2)).mul r40_C12S)).add
      ((Scaled.const (1/2)).mul r40_S11S)).pow 2)

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_Y : r40_YS.Rep Y := by
  rw [Y,axisA,r40_axisConstant]
  exact ((Scaled.rep_const _).mul r40_rep_H).sub
    ((((Scaled.rep_const _).sub ((Scaled.rep_const _).mul r40_rep_C12)).add
      ((Scaled.rep_const _).mul r40_rep_S11)).pow 2)

private theorem r40_shifted : shiftedY=centered (-11/20) (29/20) Y := by
  rw [shiftedY,centered,affine]
  congr 1
  norm_num

open WholeIntervalPolynomial.Certificate in
private theorem r40_rep_shiftedY : (r40_YS.center 1 20 9 20).Rep shiftedY := by
  rw [r40_shifted]
  exact r40_rep_Y.centered 1 20 9 20 (by norm_num) (by norm_num) (by norm_num)

theorem positive_constants (e : End) : (32/25:ℚ)<constant e := by
  cases e
  · rw [r40_constant_one]; norm_num
  · rw [r40_constant_upper]; norm_num

theorem upper_expansion : centered 0 h (Z .upper)=expansion 18 (centered 0 h (Z .upper)) :=
  r40_rep_upper_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem upper_reserve : (97/100:ℚ)<lowerOn 18 0 h (Z .upper) := by
  rw [Certificate.lowerOn_eq_of_rep r40_rep_upper_centered (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

theorem one_derivative_expansion : centered 0 cut (Z .one).derivative=
    expansion 17 (centered 0 cut (Z .one).derivative) :=
  r40_rep_one_derivative_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem one_derivative_reserve : upperOn 17 0 cut (Z .one).derivative< -(157/20:ℚ) := by
  rw [Certificate.upperOn_eq_of_rep r40_rep_one_derivative_centered (by decide +kernel)
    (by decide +kernel)]
  decide +kernel

theorem one_endpoint : (787/1000:ℚ)<(Z .one).eval cut := by
  rw [r40_eval_rep (r40_rep_Z .one r40_constant_one) (by decide +kernel)]
  decide +kernel

theorem axis_expansion : shiftedY=monomialExpansion := by
  have hdeg : shiftedY.natDegree<25 :=
    lt_of_le_of_lt (r40_rep_shiftedY.natDegree_le (by decide +kernel)) (by decide +kernel)
  rw [monomialExpansion,Fin.sum_univ_eq_sum_range (fun j => C (y (j+3))*X^(j+3)) 22]
  conv_lhs => rw [shiftedY.as_sum_range_C_mul_X_pow' hdeg]
  rw [Finset.sum_range_succ',Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [y,add_assoc,Nat.reduceAdd,zero_add,pow_zero,mul_one,pow_one]
  ring

theorem axis_reserve : (443/250:ℚ)<quadratic ∧
    (279/10000:ℚ)<y 0-(y 1)^2/(4*quadratic) := by
  simp only [quadratic,tailBudget,y,r40_rep_shiftedY.coeff (by decide +kernel)]
  decide +kernel

theorem upper_positive {n : ℝ} (hn : n∈Icc 0 (7/10:ℝ)) :
    (97/100:ℝ)<aeval n (Z .upper) := by
  have hn' : n∈Icc ((0:ℚ):ℝ) ((h:ℚ):ℝ) := by
    norm_num [h]
    exact hn
  have hh := positive_on_interval (by norm_num [h]) upper_expansion upper_reserve hn'
  norm_num at hh
  exact hh

theorem one_derivative_negative {n : ℝ} (hn : n∈Icc 0 (3/8:ℝ)) :
    aeval n (Z .one).derivative< -(157/20:ℝ) := by
  have hn' : n∈Icc ((0:ℚ):ℝ) ((cut:ℚ):ℝ) := by
    norm_num [cut]
    exact hn
  have hb := (interval_bounds (by norm_num [cut] : (0:ℚ)<cut) one_derivative_expansion hn').2
  have hr : (upperOn 17 0 cut (Z .one).derivative:ℝ)< -(157/20:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr one_derivative_reserve
    norm_num at hh
    exact hh
  exact hb.trans_lt hr

theorem one_positive {n : ℝ} (hn : n∈Icc 0 (3/8:ℝ)) :
    (787/1000:ℝ)<aeval n (Z .one) := by
  have ha : AntitoneOn (fun n : ℝ => aeval n (Z .one)) (Icc (0:ℝ) (3/8)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun n _ => (CenteredMonomialBounds.aeval_hasDerivAt (Z .one) n).continuousAt.continuousWithinAt)
      (fun n _ => CenteredMonomialBounds.aeval_hasDerivAt (Z .one) n)
    intro n hn
    linarith [one_derivative_negative (Ioo_subset_Icc_self hn)]
  have hh := ha hn (show (3/8:ℝ)∈Icc 0 (3/8) by norm_num) hn.2
  have he : (787/1000:ℝ)<aeval (3/8:ℝ) (Z .one) := by
    have hr : (787/1000:ℝ)<(((Z .one).eval cut:ℚ):ℝ) := by
      have hh := (Rat.cast_lt (K:=ℝ)).mpr one_endpoint
      norm_num at hh
      exact hh
    have hc : ((3/8:ℚ):ℝ)=(3/8:ℝ) := by norm_num
    rw [← rational_aeval,cut,hc] at hr
    exact hr
  exact he.trans_le hh

theorem axis_tail {z : ℝ} (hz : |z|≤1/4) (j : Fin 22) :
    -(|(y (j.val+3):ℝ)| *(1/4)^(j.val+1))*z^2≤
      (y (j.val+3):ℝ)*z^(j.val+3) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz (j.val+1)
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (y (j.val+3):ℝ))
  have hh : |(y (j.val+3):ℝ)*z^(j.val+1)|≤
      |(y (j.val+3):ℝ)| *(1/4)^(j.val+1) := by simpa [abs_mul,abs_pow] using hm
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hh).1 (sq_nonneg z)
  have he : z^(j.val+3)=z^(j.val+1)*z^2 := by ring
  rw [he]
  nlinarith

theorem axis_quadratic_lower {z : ℝ} (hz : |z|≤1/4) :
    (y 0:ℝ)+(y 1:ℝ)*z+(quadratic:ℝ)*z^2≤aeval z shiftedY := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => axis_tail hz j)
  have he : ∑j:Fin 22,-(|(y (j.val+3):ℝ)| *(1/4)^(j.val+1))*z^2=
      -(tailBudget:ℝ)*z^2 := by
    simp [tailBudget,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [he] at hs
  rw [axis_expansion]
  simp only [monomialExpansion,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  dsimp [quadratic]
  push_cast
  linarith

theorem axis_positive {n : ℝ} (hn : n∈Icc (3/8:ℝ) (7/10:ℝ)) :
    (279/10000:ℝ)<aeval n Y := by
  let z : ℝ := n-9/20
  have hz : |z|≤1/4 := by
    dsimp [z]
    apply abs_le.mpr
    constructor <;> linarith [hn.1,hn.2]
  have hq : (0:ℝ)<(quadratic:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr axis_reserve.1
    norm_num at hh
    linarith
  have hr : (279/10000:ℝ)<(y 0:ℝ)-(y 1:ℝ)^2/(4*(quadratic:ℝ)) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr axis_reserve.2
    push_cast at hh
    exact hh
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(y 0:ℝ)) (b:=(y 1:ℝ)) (x:=z) hq
  have hh := axis_quadratic_lower hz
  have he : aeval z shiftedY=aeval n Y := by
    rw [shiftedY,aeval_comp]
    congr 1
    simp [z]
  rw [he] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
end
end
end

section
/-!
## Whole-domain ranges of the negative-DE weight families

The ranges are polynomial bounds in the angle, of degree at most four. The low tilted ratio and
the two high ratios are cubics with positive Bernstein coefficients on their intervals; the high
l/c lower bounds add the square of `t - 19/20`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD
open Candidate Secondary PositiveAngularEnvelope

namespace Explicit

theorem low_ranges {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (2/3:ℝ)<k .low θ ∧ k .low θ<757/1000 ∧
      1<l .low θ ∧ l .low θ<1352/1000 ∧
      (10389/10000:ℝ)≤c .low θ ∧ c .low θ<1864/1000 ∧
      l .low θ≤c .low θ ∧ l .low θ<2*k .low θ := by
  let x : ℝ := 1/6-θ
  have hx : x∈Icc (0:ℝ) (1/6) := ⟨by dsimp [x]; linarith [hθ.2],by dsimp [x]; linarith [hθ.1]⟩
  have hx2 : x^2≤x/6 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hk : k .low θ=6708/10000-(3/20)*x+4*x^2 := by dsimp [k,L,x]; ring
  have hl : l .low θ=10073/10000+(17/10)*x+(11/5)*x^2 := by dsimp [l,L,x]; ring
  have hc : c .low θ=10389/10000+(69/20)*x+9*x^2 := by dsimp [c,L,x]; ring
  have hratio : 2*k .low θ-l .low θ=72935/450000+θ/15+(29/5)*θ^2 := by
    dsimp [k,l,L]
    ring
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith [sq_nonneg (x-3/160)]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hx.1,hx.2]
  · nlinarith [hx.1,sq_nonneg x]
  · nlinarith [hθ.1,sq_nonneg θ]

theorem high_parameter {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : t θ∈Icc (0:ℝ) 1 := by
  dsimp [t,L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem high_ranges {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (670158/1000000:ℝ)≤k .high θ ∧ k .high θ≤800408/1000000 ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ≤1005069/1000000 ∧
      (862/1000:ℝ)<c .high θ ∧ c .high θ≤1021248/1000000 ∧
      l .high θ<(3/2)*k .high θ ∧ c .high θ≤1073/1000-(3/10)*θ := by
  have ht := high_parameter hθ
  have hpow (n : ℕ) : 0≤(t θ)^n ∧ (t θ)^n≤1 :=
    ⟨pow_nonneg ht.1 n,by simpa using pow_le_pow_left₀ ht.1 ht.2 n⟩
  have h2 : (t θ)^2≤t θ := by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hu := sub_nonneg.2 ht.2
  have hs := mul_nonneg (sq_nonneg (t θ-19/20)) ht.1
  have hl : (863/1000:ℝ)<1005069/1000000-146411/1000000*t θ-
      157739/1000000*(t θ)^2+162815/1000000*(t θ)^3 := by
    linarith [pow_nonneg hu 2,pow_nonneg hu 3]
  have hc : (862/1000:ℝ)<1021248/1000000-168873/1000000*t θ-
      165381/1000000*(t θ)^2+175944/1000000*(t θ)^3 := by
    linarith [pow_nonneg hu 2,pow_nonneg hu 3]
  have hratio : (3/2)*k .high θ-l .high θ=
      168/1000000+(316988/1000000)*t θ+(167498/1000000)*(t θ)^2-
        (149276/1000000)*(t θ)^3+(15/10000)*(t θ)^4 := by dsimp [k,l]; ring
  have hcorrelation : 1073/1000-(3/10)*θ-c .high θ=
      (1752/1000000)*(1-t θ)+(62/1000000)*t θ+
        t θ*(1-t θ)*(10563/1000000+(175944/1000000)*t θ) := by
    dsimp [c,t,L]
    ring
  have hlast := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    (show 0≤10563/1000000+(175944/1000000)*t θ by linarith [ht.1])
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [k]; nlinarith [(hpow 1).1,(hpow 2).1,(hpow 3).1,(hpow 4).1]
  · dsimp [k]; nlinarith [(hpow 1).2,(hpow 2).2,(hpow 3).2,(hpow 4).2]
  · dsimp [l]; linarith
  · dsimp [l]; nlinarith [ht.1]
  · dsimp [c]; linarith
  · dsimp [c]; nlinarith [ht.1]
  · nlinarith [ht.1,(hpow 2).1,(hpow 4).1]
  · nlinarith [ht.1,ht.2]

theorem low_tilted {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    c .low θ≤ m .low θ z ∧ m .low θ z<(69/50)*l .low θ := by
  have hr := low_ranges hθ
  have hc : 0<c .low θ := by linarith [hr.2.2.2.2.1]
  have hz' : z∈Icc 0 PositiveTD.Explicit.split := ⟨hz.1,hz.2.trans hθ.2⟩
  have hf := PositiveTD.Explicit.low_factor hz'
  have hlow := mul_le_mul_of_nonneg_left hf.1 hc.le
  have hupper := mul_le_mul_of_nonneg_left
    (show Real.cos z+eta*Real.sin z≤1+eta*θ by
      have he : PositiveTD.eta=eta := rfl
      rw [he] at hf
      dsimp [eta] at *
      linarith [hz.2,hf.2]) hc.le
  have hcert : (11909/16000000:ℝ)≤69/50*l .low θ-c .low θ*(1+293/1000*θ) := by
    have h2 : 0≤1/6-θ := sub_nonneg.2 hθ.2
    simp only [l,c,L]
    linarith [pow_nonneg hθ.1 3,mul_nonneg (pow_nonneg hθ.1 2) h2,
      mul_nonneg hθ.1 (pow_nonneg h2 2),pow_nonneg h2 3]
  refine ⟨by simpa [m,eta,PositiveTD.eta] using hlow,?_⟩
  dsimp [m,eta]
  dsimp [eta] at hupper
  nlinarith

theorem high_ratios {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (9/10)*l .high θ<c .high θ ∧ c .high θ<(1017/1000)*l .high θ := by
  have ht := high_parameter hθ
  have hu := sub_nonneg.2 ht.2
  simp only [l,c]
  constructor <;> linarith [pow_nonneg ht.1 3,mul_nonneg (pow_nonneg ht.1 2) hu,
    mul_nonneg ht.1 (pow_nonneg hu 2),pow_nonneg hu 3]

theorem high_tilted {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    k .high θ< m .high θ z ∧ m .high θ z<(1061/1000)*l .high θ ∧
      m .high θ z<(1066/1000:ℝ) ∧ (2/3)*l .high θ< m .high θ z := by
  have hr := high_ranges hθ
  have hrat := high_ratios hθ
  have hc : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2,hθ.2]⟩
  have hlow₀ := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_lower hz') hc
  have hupper := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hc
  have hlow : (19/20)*c .high θ< m .high θ z := by
    simpa [m,eta,PositiveTD.eta,mul_comm] using hlow₀
  change m .high θ z<c .high θ*(1043/1000) at hupper
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.1,
      hr.2.2.2.2.2.1,hrat.1,hrat.2]

theorem family_positive (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left f) (right f)) (hz : z∈Icc 0 θ) :
    0<k f θ ∧ 0<l f θ ∧ 0<c f θ ∧ 0< m f θ z := by
  cases f
  · have hr := low_ranges hθ
    have hm := low_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.2.2.2.2.1,hm.1]⟩
  · have hr := high_ranges hθ
    have hm := high_tilted hθ hz
    exact ⟨by linarith [hr.1],by linarith [hr.2.2.1],
      by linarith [hr.2.2.2.2.1],by linarith [hr.1,hm.1]⟩

theorem high_pairs {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i : Fin 3) : 0<p .high θ z i ∧ p .high θ z i≤q .high θ z i ∧
      (2/3)*q .high θ z i<p .high θ z i ∧
      (863/1000:ℝ)<q .high θ z i ∧ q .high θ z i<(1066/1000:ℝ) := by
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hk : 0<k .high θ := by linarith [hr.1]
  have hl : 0<l .high θ := by linarith [hr.2.2.1]
  have hm0 : 0< m .high θ z := hk.trans hm.1
  have hkl : k .high θ<l .high θ := by linarith [hr.2.1,hr.2.2.1]
  fin_cases i
  · show 0<k .high θ ∧ k .high θ≤1 ∧ (2/3)*1<k .high θ ∧ (863/1000:ℝ)<1 ∧ (1:ℝ)<1066/1000
    exact ⟨hk,by linarith [hr.2.1],by linarith [hr.1],by norm_num,by norm_num⟩
  · show 0<k .high θ ∧ k .high θ≤l .high θ ∧ (2/3)*l .high θ<k .high θ ∧
      (863/1000:ℝ)<l .high θ ∧ l .high θ<1066/1000
    exact ⟨hk,hkl.le,by linarith [hr.2.2.2.2.2.2.1],hr.2.2.1,
      by linarith [hr.2.2.2.1]⟩
  · show 0 < min (l .high θ) (m .high θ z) ∧
      min (l .high θ) (m .high θ z) ≤ max (l .high θ) (m .high θ z) ∧
      (2/3)*max (l .high θ) (m .high θ z) < min (l .high θ) (m .high θ z) ∧
      (863/1000:ℝ) < max (l .high θ) (m .high θ z) ∧
      max (l .high θ) (m .high θ z) < 1066/1000
    refine ⟨lt_min hl hm0,min_le_max,?_,?_,?_⟩
    · rcases le_total (l .high θ) (m .high θ z) with hh | hh
      · rw [min_eq_left hh,max_eq_right hh]
        nlinarith [hm.2.1]
      · rw [min_eq_right hh,max_eq_left hh]
        exact hm.2.2.2
    · exact hr.2.2.1.trans_le (le_max_left _ _)
    · exact max_lt (by linarith [hr.2.2.2.1]) hm.2.2.1

theorem high_q_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ)
    (i j : Fin 3) : q .high θ z i<(29/25)*q .high θ z j := by
  have hi := high_pairs hθ hz i
  have hj := high_pairs hθ hz j
  have hr := high_ranges hθ
  have hm := high_tilted hθ hz
  have hq (n : Fin 3) : q .high θ z n=1 ∨ q .high θ z n=l .high θ ∨
      q .high θ z n=max (l .high θ) (m .high θ z) := by
    fin_cases n
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  by_cases hl : 1≤l .high θ
  · have hj1 : 1≤q .high θ z j := by
      rcases hq j with h|h|h <;> rw [h]
      · exact hl
      · exact hl.trans (le_max_left _ _)
    nlinarith [hi.2.2.2.2]
  · by_cases hm1 : m .high θ z≤1
    · have hi1 : q .high θ z i≤1 := by
        rcases hq i with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hl).le
        · exact max_le (lt_of_not_ge hl).le hm1
      nlinarith [hj.2.2.2.1]
    · have hiM : q .high θ z i≤ m .high θ z := by
        rcases hq i with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hm1).le
        · linarith [lt_of_not_ge hl,lt_of_not_ge hm1]
        · exact max_le (by linarith [lt_of_not_ge hl,lt_of_not_ge hm1]) le_rfl
      have hjL : l .high θ≤q .high θ z j := by
        rcases hq j with h|h|h <;> rw [h]
        · exact (lt_of_not_ge hl).le
        · exact le_max_left _ _
      nlinarith [hm.2.1,hr.2.2.1]

/-- The late interval used by the shared secant-coordinate shape proof.
The cubic upper estimate for l and the affine c/theta correlation are
kept before taking the maximum in the original B pair. -/
theorem high_late_q_le_one {θ z : ℝ}
    (hθ : θ∈Icc (1/6:ℝ) (7/10)) (_hz : z∈Icc 0 θ)
    (hlate : (11/20:ℝ)≤θ) (i : Fin 3) : q .high θ z i≤1 := by
  have ht := high_parameter hθ
  have htlate : (23/32:ℝ)≤t θ := by dsimp [t,L]; linarith
  have h2 : (t θ)^2≤t θ := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have h3 : (t θ)^3≤(t θ)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (t θ)) (sub_nonneg.mpr ht.2)]
  have hl : l .high θ≤1005069/1000000-(141335/1000000)*t θ := by
    dsimp [l]
    nlinarith
  have hl1 : l .high θ≤1 := by linarith
  have hr := high_ranges hθ
  have hc : c .high θ≤227/250 := by linarith [hr.2.2.2.2.2.2.2]
  have hcpos : 0<c .high θ := by linarith [hr.2.2.2.2.1]
  have hm := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hcpos
  have hm1 : m .high θ z≤1 := by
    change c .high θ*(Real.cos z+PositiveTD.eta*Real.sin z)<
      c .high θ*(1043/1000) at hm
    dsimp [m,eta,PositiveTD.eta]
    dsimp [PositiveTD.eta] at hm
    nlinarith
  fin_cases i <;> simp only [q]
  · exact le_rfl
  · exact hl1
  · exact max_le hl1 hm1

end Explicit
end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH.Slopes
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open NegativeAPositiveTD.PositiveSlope OrdinaryNegativeSlope
open PowerTailBounds DirectedPowerBounds

def smallPoly : ℚ[X] := (C (1/2)+C (179/200)*X)^2*
  (1+X^2+C (499/2500)*X)-C (9789/2500)*X^2
def smallCentered : ℚ[X] := shift (3/4) smallPoly
def smallQuadratic : ℚ := smallCentered.coeff 2-PowerTailBounds.norm smallCentered 3 2 (1/4)

theorem small_certificate :
    smallCentered=C (smallCentered.coeff 0)+C (smallCentered.coeff 1)*X+
      C (smallCentered.coeff 2)*X^2+tail smallCentered 3 2 ∧
    (3691/2500:ℚ)<smallQuadratic ∧
    (1459/10000:ℚ)<smallCentered.coeff 0-
      (smallCentered.coeff 1)^2/(4*smallQuadratic) := by
  have hE : smallCentered=C (468212609/3200000000)+C (76556693/1600000000)*X+
      C (956406681/400000000)*X^2+C (345795959/100000000)*X^3+C (32041/40000)*X^4 := by
    apply Polynomial.funext
    intro x
    simp only [smallCentered,shift,smallPoly,eval_comp,eval_add,eval_mul,eval_pow,eval_sub,
      eval_C,eval_X,eval_one]
    ring
  have h0 : smallCentered.coeff 0=468212609/3200000000 := by rw [hE]; simp
  have h1 : smallCentered.coeff 1=76556693/1600000000 := by rw [hE]; simp
  have h2 : smallCentered.coeff 2=956406681/400000000 := by rw [hE]; simp
  have h3 : smallCentered.coeff 3=345795959/100000000 := by rw [hE]; simp
  have h4 : smallCentered.coeff 4=32041/40000 := by rw [hE]; simp
  have htail : tail smallCentered 3 2=C (smallCentered.coeff 3)*X^3+
      C (smallCentered.coeff 4)*X^4 := by
    simp [tail,Fin.sum_univ_two]
  have hQ : smallQuadratic=590585097/400000000 := by
    simp only [smallQuadratic,PowerTailBounds.norm,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
      zero_add,Nat.reduceAdd,h2,h3,h4]
    norm_num
  refine ⟨?_,?_,?_⟩
  · rw [htail,h0,h1,h2,h3,h4,← add_assoc]
    exact hE
  · rw [hQ]; norm_num
  · rw [hQ,h0,h1]; norm_num

theorem small_polynomial_positive {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    0<(1/2+(179/200)*r)^2*(1+r^2+(499/2500)*r)-qCap*r^2 := by
  have hx : |r-(3/4:ℝ)|≤((1/4:ℚ):ℝ) := by
    rw [abs_le]; push_cast; exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hh := PowerTailBounds.quadratic_lower small_certificate.1 (by norm_num : (0:ℚ)≤1/4) hx
  have hA : (0:ℝ)<(smallQuadratic:ℝ) := by
    have hn : (0:ℚ)<smallQuadratic := by linarith [small_certificate.2.1]
    exact_mod_cast hn
  have hc : (0:ℝ)<(smallCentered.coeff 0:ℝ)-
      (smallCentered.coeff 1:ℝ)^2/(4*(smallQuadratic:ℝ)) := by
    have hn : (0:ℚ)<smallCentered.coeff 0-
        (smallCentered.coeff 1)^2/(4*smallQuadratic) := by
      linarith [small_certificate.2.2]
    exact_mod_cast hn
  have hq (x : ℝ) : 0<(smallCentered.coeff 0:ℝ)+
      (smallCentered.coeff 1:ℝ)*x+(smallQuadratic:ℝ)*x^2 := by
    have hs := mul_nonneg hA.le (sq_nonneg (x+(smallCentered.coeff 1:ℝ)/(2*(smallQuadratic:ℝ))))
    have he : (smallQuadratic:ℝ)*(x+(smallCentered.coeff 1:ℝ)/(2*(smallQuadratic:ℝ)))^2+
        (smallCentered.coeff 0:ℝ)-(smallCentered.coeff 1:ℝ)^2/(4*(smallQuadratic:ℝ))=
        (smallCentered.coeff 0:ℝ)+(smallCentered.coeff 1:ℝ)*x+(smallQuadratic:ℝ)*x^2 := by
      field_simp [hA.ne']
      ring
    linarith
  have he : aeval (r-(3/4:ℝ)) smallCentered=
      (1/2+(179/200)*r)^2*(1+r^2+(499/2500)*r)-qCap*r^2 := by
    norm_num [smallCentered,shift_eval,smallPoly,qCap]
  rw [he] at hh
  have hAeq : (smallQuadratic:ℝ)=(smallCentered.coeff 2:ℝ)-
      (PowerTailBounds.norm smallCentered 3 2 (1/4):ℝ) := by simp [smallQuadratic]
  rw [← hAeq] at hh
  exact (hq _).trans_le hh

theorem small_endpoint_trig :
    (179/200:ℝ)<Real.cos v-Real.sin v ∧
      (499/5000:ℝ)<Real.sin v := by
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤v by norm_num [v])
  have hl := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤v by norm_num [v])
  have hu := Arithmetic.sin_le_sin9 (show (0:ℝ)≤v by norm_num [v])
  norm_num [v,Arithmetic.cos10,Arithmetic.cos8,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7] at hc hl hu ⊢
  exact ⟨by linarith,by linarith⟩

theorem small_normalized {r : ℝ} (hr : r∈Icc (1/2:ℝ) 1) :
    -(1/2:ℝ)<r*(Real.cos v-Real.sin v)-R*r*Real.cos v/pairNorm r 1 v := by
  have hr0 : 0<r := by linarith [hr.1]
  have hv : |v|≤frameCap := by norm_num [v,frameCap]
  have hn := pairNorm_pos hr0 (by norm_num : (0:ℝ)<1) hv
  have hn2 := pairNorm_sq hr0 (by norm_num : (0:ℝ)<1) hv
  norm_num only [pairEnergy,pairProduct,one_pow,mul_one] at hn2
  obtain ⟨hc,hs⟩ := small_endpoint_trig
  have hlow : 1+r^2+(499/2500)*r≤(pairNorm r 1 v)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hs.le hr0.le]
  have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg (1/2+(179/200)*r))
  have hpoly := small_polynomial_positive hr
  have hR2 : (R*r)^2=qCap*r^2 := by rw [mul_pow,radius_sq]
  have hcross : R*r<(1/2+(179/200)*r)*pairNorm r 1 v := by
    have hright : 0≤(1/2+(179/200)*r)*pairNorm r 1 v := by positivity
    have hsq : (R*r)^2<((1/2+(179/200)*r)*pairNorm r 1 v)^2 := by
      rw [hR2,mul_pow]
      linarith [hmul,hpoly]
    exact lt_of_pow_lt_pow_left₀ 2 hright hsq
  have hnum := mul_le_mul_of_nonneg_left (Real.cos_le_one v)
    (show 0≤R*r by exact mul_nonneg (Real.sqrt_nonneg _) hr0.le)
  have hquot : R*r*Real.cos v/pairNorm r 1 v<1/2+(179/200)*r := by
    apply (div_lt_iff₀ hn).2
    nlinarith only [hcross,hnum]
  have hlinear := mul_lt_mul_of_pos_left hc hr0
  linarith

theorem small_positive {a b t : ℝ} (ha : 0<a) (hab : a≤b) (hba : b≤2*a)
    (ht : t∈Icc 0 v) : -(1/2)*b<Ud a b t := by
  have hb := ha.trans_le hab
  have hr : a/b∈Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hb).2 (by linarith),(div_le_one hb).2 hab⟩
  have he : -(1/2)*b<Ud a b v := by
    rw [Ud_normalized hb]
    nlinarith only [mul_lt_mul_of_pos_left (small_normalized hr) hb]
  exact he.trans_le (Ud_antitone ha hab hba
    ⟨ht.1,by dsimp [v,frameCap] at *; linarith [ht.2]⟩
    (by norm_num [v,frameCap]) ht.2)

end SquaresInCircles.Eight.GlobalGA.NegativeEH.Slopes
end
end
end
