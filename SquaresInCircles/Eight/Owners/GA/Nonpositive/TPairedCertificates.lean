module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedMassCertificate
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedWholeCertificate

/-!
# Eight squares: exact whole-domain coefficients for paired nonpositive T

The finite rational identities below
use the stated tensor Chebyshev bound once on each native trapezoid;
the nine V boundaries use their full intervals.  No state subdivision
or sampled lower bound enters the certificate.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Certificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial
open CertificateRestrictions

/-- Unfolds a numerator into a ring expression in `X`, `C X`, scalars, `lift` and `cubicMass`. -/
macro "r80p_unfold" : tactic => `(tactic| simp only [numerator,mass,rho,rhoBase,P,P0,
    Paired.Certificate.p,Paired.Certificate.q,Paired.Certificate.k,Paired.Certificate.l,
    Paired.Certificate.e,Paired.Certificate.delta,origin,A,A0,gain,
    NonnegativeTotals.NegativeTD.Certificate.J,Matrix.cons_val,Fin.isValue,↓reduceIte,
    Fin.reduceEq,true_and,and_true,false_and,and_false])

/-! ### Building the restrictions

`build_rep` proves the goals `RepOn φ ?a p` along the syntax of `p`, like `build_rep_yZero`,
`build_rep_xZero` and `build_rep_curve`, but it picks the lemma from the head of `p` and the
restriction `φ` instead of trying the lemmas in turn, and it proves a repeated `(φ, p)` (a mass
occurs several times in a numerator) only once. It leaves the side conditions as goals;
`decide_all` proves all goals by one kernel computation, so that the scaled lists they share are
computed once. -/

open Lean Meta in
/-- Proves `RepOn φ ?a p` along the syntax of `p`; returns the side conditions. -/
private meta partial def repBuild (seen : IO.Ref (Std.HashMap (Expr × Expr) Expr))
    (g : MVarId) : MetaM (Array MVarId) := do
  if ← g.isAssigned then return #[]
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``WholeIntervalPolynomial.Certificate.Scaled.Rep 2 then
    g.assumption
    return #[]
  let_expr RepOn φ _ p := ty | return #[g]
  if let some pf := (← seen.get)[(φ, p)]? then
    if ← isDefEq ty (← inferType pf) then
      g.assign pf
      return #[]
  let leaf (s : String) : Option Name :=
    (match φ.getAppFn.constName? with
      | some ``yZero => some "yZero" | some ``xZero => some "xZero"
      | some ``onLine => some "line" | some ``onCurve => some "curve" | _ => none).map
      fun r => .str ``RepOn (r ++ "_" ++ s)
  let lem? : Option Name := match p.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, _, _]) => some ``RepOn.add
    | (``HSub.hSub, #[_, _, _, _, _, _]) => some ``RepOn.sub
    | (``HMul.hMul, #[_, _, _, _, _, _]) => some ``RepOn.mul
    | (``HPow.hPow, #[_, _, _, _, _, _]) => some ``RepOn.pow
    | (``Neg.neg, #[_, _, _]) => some ``RepOn.neg
    | (``OfNat.ofNat, #[_, n, _]) =>
      match n.rawNatLit? with
      | some 0 => some ``RepOn.zero
      | some 1 => some ``RepOn.one
      | _ => none
    | (``TensorWholeIntervalPolynomial.scalar, #[_]) => leaf "scalar"
    | (``Polynomial.X, #[_, _]) => leaf "X"
    | (``TwoVariablePolynomial.cubicMass, #[_, _]) => leaf "cubicMass"
    | (``DFunLike.coe, #[_, _, _, _, f, q]) =>
      match f.getAppFn.constName?, q.constName? with
      | some ``Polynomial.C, _ => leaf "CX"
      | some ``TwoVariablePolynomial.lift, some ``GlobalGA.PositiveTD.Certificate.C10 =>
        leaf "liftC10"
      | some ``TwoVariablePolynomial.lift, some ``GlobalGA.PositiveTD.Certificate.C12 =>
        leaf "liftC12"
      | some ``TwoVariablePolynomial.lift, some ``GlobalGA.PositiveTD.Certificate.S9 =>
        leaf "liftS9"
      | some ``TwoVariablePolynomial.lift, some ``GlobalGA.PositiveTD.Certificate.S11 =>
        leaf "liftS11"
      | _, _ => none
    | _ => none
  let some lem := lem? | return #[g]
  seen.modify (·.insert (φ, p) (.mvar g))
  let mut side := #[]
  for g' in ← withReducible (g.apply (← mkConstWithFreshMVarLevels lem)) do
    side := side ++ (← repBuild seen g')
  return side

open Lean Elab Tactic in
/-- Proves the goals `RepOn φ ?a p` along the syntax of `p`, leaving the side conditions. -/
local elab "build_rep" : tactic => do
  let seen ← IO.mkRef {}
  let mut side := #[]
  for g in ← getGoals do
    side := side ++ (← repBuild seen g)
  setGoals side.toList

open Lean Meta Elab Tactic in
/-- Proves all goals by one `decide +kernel` on their conjunction. -/
local elab "decide_all" : tactic => do
  let gs ← getUnsolvedGoals
  let some last := gs.getLast? | return
  let tys ← gs.mapM fun g => do instantiateMVars (← g.getType)
  let conj (ts : List Expr) : Expr := ts.dropLast.foldr mkAnd ts.getLast!
  let pf ← last.withContext (mkFreshExprMVar (conj tys))
  setGoals [pf.mvarId!]
  evalTactic (← `(tactic| set_option synthInstance.maxSize 4096 in decide +kernel))
  let mut p := pf
  let mut rest := tys
  for g in gs do
    match rest with
    | a :: ts@(_ :: _) =>
      g.assign (mkApp3 (mkConst ``And.left) a (conj ts) p)
      p := mkApp3 (mkConst ``And.right) a (conj ts) p
      rest := ts
    | _ => g.assign p
  setGoals []

theorem boundary_certificate (b : Boundary) (i : Fin 3) :
    WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))=
      WholeIntervalPolynomial.expansion 20
        (WholeIntervalPolynomial.centered 0 (boundaryLength b) (boundary b (numerator (.negative i)))) ∧
    boundaryReserve b i<WholeIntervalPolynomial.lowerOn 20 0 (boundaryLength b)
      (boundary b (numerator (.negative i))) := by
  open WholeIntervalPolynomial.Certificate in
  cases b <;> fin_cases i <;> simp only [Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk]
  · apply lower_cert ?ha (boundaryLength .low) 41 200 (by norm_num) (by norm_num [boundaryLength,M]) 20 _ 101 500
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (⟨[],1⟩ : Scaled).Rep (0 : ℚ[X]) := Scaled.rep_zero
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .low) 41 200 (by norm_num) (by norm_num [boundaryLength,M]) 20 _ 101 500
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (⟨[],1⟩ : Scaled).Rep (0 : ℚ[X]) := Scaled.rep_zero
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .low) 41 200 (by norm_num) (by norm_num [boundaryLength,M]) 20 _ 101 500
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (⟨[],1⟩ : Scaled).Rep (0 : ℚ[X]) := Scaled.rep_zero
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .equal) 29 200 (by norm_num) (by norm_num [boundaryLength,M,h]) 20 _ 23 100
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const M).add Scaled.var).Rep (C M+X : ℚ[X]) := (Scaled.rep_const M).add Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .equal) 29 200 (by norm_num) (by norm_num [boundaryLength,M,h]) 20 _ 57 250
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const M).add Scaled.var).Rep (C M+X : ℚ[X]) := (Scaled.rep_const M).add Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .equal) 29 200 (by norm_num) (by norm_num [boundaryLength,M,h]) 20 _ 57 250
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      have hV : ((Scaled.const M).add Scaled.var).Rep (C M+X : ℚ[X]) := (Scaled.rep_const M).add Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .high) 7 20 (by norm_num) (by norm_num [boundaryLength,h]) 20 _ 11 50
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (Scaled.const (h-M)).Rep (C (h-M) : ℚ[X]) := Scaled.rep_const (h-M)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .high) 7 20 (by norm_num) (by norm_num [boundaryLength,h]) 20 _ 187 1000
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (Scaled.const (h-M)).Rep (C (h-M) : ℚ[X]) := Scaled.rep_const (h-M)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all
  · apply lower_cert ?ha (boundaryLength .high) 7 20 (by norm_num) (by norm_num [boundaryLength,h]) 20 _ 119 200
      (by norm_num [boundaryReserve]) (by norm_num)
    case' ha =>
      simp only [boundary,restrict_eq_onCurve]
      have hU : (Scaled.const (h-M)).Rep (C (h-M) : ℚ[X]) := Scaled.rep_const (h-M)
      have hV : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
      change RepOn _ _ _
      r80p_unfold
      build_rep
    decide_all


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem slope_certificate :
    slopePolynomial=C (slopePolynomial.coeff 0)+C (slopePolynomial.coeff 1)*X+
      C (slopePolynomial.coeff 2)*X^2+C (slopePolynomial.coeff 3)*X^3+
        C (slopePolynomial.coeff 4)*X^4 ∧
    (411/10000:ℚ)<slopePolynomial.coeff 0 ∧ (1407/10000:ℚ)<slopePolynomial.coeff 1 ∧
    -(2/625:ℚ)<slopePolynomial.coeff 2 ∧ -(99/5000:ℚ)<slopePolynomial.coeff 3 ∧
    -(7/2500:ℚ)<slopePolynomial.coeff 4 := by
  have hid : slopePolynomial=C (336180235729387729037217947677980044421080892109/8173092077568000000000000000000000000000000000000:ℚ)+C (86285019579264538360763637019577511367531385464301/612981905817600000000000000000000000000000000000000:ℚ)*X+C (-(72429737070424857367307171845879834633093851871/22703033548800000000000000000000000000000000000000):ℚ)*X^2+C (-(49884442509327839927110205109687697420792722259/2522559283200000000000000000000000000000000000000):ℚ)*X^3+C (-(1157244337369165398949386648136600021950201743/420426547200000000000000000000000000000000000000):ℚ)*X^4 := by
    apply Polynomial.funext
    intro t
    simp only [slopePolynomial,slopeK,slopeL,C6,NonnegativeTotals.NegativeTD.Certificate.slopeK,
      NonnegativeTotals.NegativeTD.Certificate.slopeL,NonnegativeTotals.NegativeTD.Certificate.C6,
      PositiveTD.Certificate.S9,
      PositiveTD.Certificate.S11,PositiveTD.Certificate.S5,h,eval_add,eval_sub,eval_mul,
      eval_C,eval_X,eval_pow,eval_one]
    ring
  have hc : ∀ i : ℕ,slopePolynomial.coeff i=
      (C (336180235729387729037217947677980044421080892109/8173092077568000000000000000000000000000000000000:ℚ)+C (86285019579264538360763637019577511367531385464301/612981905817600000000000000000000000000000000000000:ℚ)*X+C (-(72429737070424857367307171845879834633093851871/22703033548800000000000000000000000000000000000000):ℚ)*X^2+C (-(49884442509327839927110205109687697420792722259/2522559283200000000000000000000000000000000000000):ℚ)*X^3+C (-(1157244337369165398949386648136600021950201743/420426547200000000000000000000000000000000000000):ℚ)*X^4 : ℚ[X]).coeff i := fun i => by rw [← hid]
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  simp only [coeff_add,coeff_C,coeff_C_mul,coeff_X_pow,coeff_X,Nat.reduceEqDiff,
    one_ne_zero,OfNat.ofNat_ne_zero,OfNat.zero_ne_ofNat,
    OfNat.one_ne_ofNat,↓reduceIte,mul_one,mul_zero,add_zero,zero_add] at h0 h1 h2 h3 h4
  rw [h0,h1,h2,h3,h4]
  refine ⟨hid,?_,?_,?_,?_,?_⟩ <;> norm_num

theorem mass_positive (f : Kind) (j : Fin 3) {x E : ℝ} (hd : Domain f x E) :
    (1:ℝ)<evaluate x E (mass f j) := by
  have hh := positive_on_domain (mass_certificate f j).1 (mass_certificate f j).2 hd
  exact_mod_cast hh

theorem whole_positive (f : Kind) (hf : Whole f) {x E : ℝ} (hd : Domain f x E) :
    0<evaluate x E (numerator f) := by
  have hh := positive_on_domain (whole_certificate f hf).1 (whole_certificate f hf).2 hd
  have hv : (0:ℝ)<(wholeReserve f:ℝ) := by
    cases f with
    | equal => norm_num [wholeReserve]
    | positive i => fin_cases i <;> norm_num [wholeReserve]
    | diagonal => norm_num [wholeReserve]
    | negative i => exact hf.elim
  exact hv.trans hh

theorem boundary_positive (b : Boundary) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (boundaryLength b:ℝ)) :
    0<aeval x (boundary b (numerator (.negative i))) := by
  have hh := WholeIntervalPolynomial.positive_on_interval
    (by cases b <;> norm_num [boundaryLength,L,M,h])
    (boundary_certificate b i).1 (boundary_certificate b i).2 (by simpa using hx)
  have hr : (0:ℝ)<(boundaryReserve b i:ℝ) := by
    cases b <;> fin_cases i <;> norm_num [boundaryReserve]
  exact hr.trans hh

theorem slope_positive {E : ℝ} (hE : E∈Icc 0 (7/10:ℝ)) :
    (4/125:ℝ)<aeval E slopePolynomial := by
  obtain ⟨hid,h0,h1,h2,h3,h4⟩ := slope_certificate
  have hc0 := (Rat.cast_lt (K:=ℝ)).mpr h0
  have hc1 := (Rat.cast_lt (K:=ℝ)).mpr h1
  have hc2 := (Rat.cast_lt (K:=ℝ)).mpr h2
  have hc3 := (Rat.cast_lt (K:=ℝ)).mpr h3
  have hc4 := (Rat.cast_lt (K:=ℝ)).mpr h4
  push_cast at hc0 hc1 hc2 hc3 hc4
  have hm1 := mul_le_mul_of_nonneg_right hc1.le hE.1
  have hm2 := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg E)
  have hm3 := mul_le_mul_of_nonneg_right hc3.le (pow_nonneg hE.1 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4.le (pow_nonneg hE.1 4)
  have hp2 := pow_le_pow_left₀ hE.1 hE.2 2
  have hp3 := pow_le_pow_left₀ hE.1 hE.2 3
  have hp4 := pow_le_pow_left₀ hE.1 hE.2 4
  have heval := congrArg (fun P : ℚ[X] => aeval E P) hid
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at heval
  rw [heval]
  norm_num at hp2 hp3 hp4
  linarith [hE.1]

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired.Certificate
