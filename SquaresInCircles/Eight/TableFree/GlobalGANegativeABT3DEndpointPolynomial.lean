module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3DData
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

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
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.DEnvelope.DEndpoint
