module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData

/-!
# Eight squares: literal whole-domain certificates for the six BT3 endpoint numerators

Each transform covers its entire native triangle, rectangle, or edge.
The only polynomial divisions remove an exactly vanishing base edge
or the two endpoints of the displayed chord.
-/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals
open CertificateRestrictions

/-- Unfolds a numerator into a ring expression in `X`, `C X`, scalars, `lift` and `cubicMass`. -/
macro "r80_unfold" : tactic => `(tactic| simp only [numerator,mass,LargeCertificate.A,
    LargeCertificate.P,LargeCertificate.baseNorm,
    LargeCertificate.rotation,LargeCertificate.qB,NonnegativeTotals.Certificate.ABase,
    NonnegativeTotals.Certificate.jE,NonnegativeTotals.Certificate.J,
    NonnegativeTotals.Certificate.k,NonnegativeTotals.Certificate.l,
    NonnegativeTotals.Certificate.c,NonnegativeTotals.Certificate.theta,
    NonnegativeTotals.Certificate.e,NonnegativeTotals.Certificate.delta,
    NonnegativeTotals.Certificate.qStar,LargeCertificate.rho,Matrix.cons_val,Fin.isValue,
    ↓reduceIte,Fin.val_two,reduceCtorEq,false_and,and_true,true_and,Fin.val_zero,Fin.val_one,
    Nat.reduceEqDiff,Fin.reduceEq,and_false,Fin.coe_ofNat_eq_mod,Nat.reduceMod])

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

theorem triangle_far_certificate (i : Fin 2) :
    WholeIntervalPolynomial.centered 0 d (triangleFar i.castSucc)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar i.castSucc)) ∧
    triangleFarReserve i<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar i.castSucc) := by
  open WholeIntervalPolynomial.Certificate in
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  fin_cases i
  · show WholeIntervalPolynomial.centered 0 d (triangleFar 0)=
        WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 d (triangleFar 0)) ∧
      (41/1000:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar 0)
    apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (41/1000) 41 1000 (by norm_num)
      (by norm_num)
    case' ha =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
      case' hΨ => r80_unfold
      case' hB => r80_unfold
    build_rep
    decide_all
  · show WholeIntervalPolynomial.centered 0 d (triangleFar 1)=
        WholeIntervalPolynomial.expansion 39 (WholeIntervalPolynomial.centered 0 d (triangleFar 1)) ∧
      (29/250:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleFar 1)
    apply lower_cert ?ha₁ d 4 15 (by norm_num) (by norm_num) 39 (29/250) 29 250 (by norm_num)
      (by norm_num)
    case' ha₁ =>
      unfold triangleFar triangleQuotient
      apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ₁ ?hB₁ ?hc₁
      case' hΨ₁ => r80_unfold
      case' hB₁ => r80_unfold
    build_rep
    decide_all

theorem triangle_far_B_certificate :
    WholeIntervalPolynomial.centered 0 d (triangleFar 2).derivative=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleFar 2).derivative) ∧
    WholeIntervalPolynomial.upperOn 39 0 d (triangleFar 2).derivative< -(583/1000:ℚ) ∧
    (113/500:ℚ)<(triangleFar 2).eval d := by
  open WholeIntervalPolynomial.Certificate in
  have hU : Scaled.var.Rep (X : ℚ[X]) := Scaled.rep_var
  have hV : ((Scaled.const d).sub Scaled.var).Rep (C d-X : ℚ[X]) :=
    (Scaled.rep_const d).sub Scaled.rep_var
  apply far_slope_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (-(583/1000)) (-583) 1000
    (by norm_num) (by norm_num) (113/500) 113 500 (by norm_num) (by norm_num)
  case' ha =>
    unfold triangleFar triangleQuotient
    apply far_rep d 4 15 (by norm_num) (by norm_num) ?hΨ ?hB ?hc
    case' hΨ => r80_unfold
    case' hB => r80_unfold
  build_rep
  decide_all

theorem triangle_initial_certificate :
    (893/500000:ℚ)<(triangleBase 0).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (triangleBase 0).divX=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleBase 0).divX) ∧
    (8/125:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleBase 0).divX := by
  open WholeIntervalPolynomial.Certificate in
  apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (893/500000) 893 500000
    (by norm_num) (by norm_num) (8/125) 8 125 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle 0)
    r80_unfold
    build_rep
  decide_all

theorem triangle_chord_certificate :
    triangleBase 1=chordPolynomial (triangleBase 1) ∧
    (893/500000:ℚ)<(triangleBase 1).eval 0 ∧
    (893/500000:ℚ)<(triangleBase 1).eval d ∧
    WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase 1))=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (chordQuotient (triangleBase 1))) ∧
    (17/200:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (chordQuotient (triangleBase 1)) := by
  open WholeIntervalPolynomial.Certificate in
  apply chord_cert ?ha d 4 15 (by norm_num) (by norm_num) (by norm_num) 39
    (893/500000) 893 500000 (by norm_num) (by norm_num) (17/200) 17 200 (by norm_num) (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle 1)
    r80_unfold
    build_rep
  decide_all

theorem triangle_B_certificate :
    WholeIntervalPolynomial.centered 0 d (triangleBase 2)=
      WholeIntervalPolynomial.expansion 39
        (WholeIntervalPolynomial.centered 0 d (triangleBase 2)) ∧
    (3/100:ℚ)<WholeIntervalPolynomial.lowerOn 39 0 d (triangleBase 2) := by
  open WholeIntervalPolynomial.Certificate in
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 39 (3/100) 3 100 (by norm_num)
    (by norm_num)
  case' ha =>
    simp only [triangleBase,baseY_eq_yZero]
    change RepOn yZero _ (numerator .triangle 2)
    r80_unfold
    build_rep
  decide_all

theorem rectangle_H_certificate :
    WholeIntervalPolynomial.centered 0 d (rectangleBase 0)=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase 0)) ∧
    (4/3125:ℚ)<WholeIntervalPolynomial.lowerOn 35 0 d (rectangleBase 0) := by
  open WholeIntervalPolynomial.Certificate in
  apply lower_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (4/3125) 4 3125 (by norm_num)
    (by norm_num)
  case' ha =>
    simp only [rectangleBase,baseX_eq_xZero]
    change RepOn xZero _ (numerator .rectangle 0)
    r80_unfold
    build_rep
  decide_all

theorem rectangle_initial_certificate (i : Fin 2) :
    rectangleInitialReserve i<(rectangleBase i.succ).eval 0 ∧
    WholeIntervalPolynomial.centered 0 d (rectangleBase i.succ).divX=
      WholeIntervalPolynomial.expansion 35
        (WholeIntervalPolynomial.centered 0 d (rectangleBase i.succ).divX) ∧
    rectangleSlopeReserve i<WholeIntervalPolynomial.lowerOn 35 0 d
      (rectangleBase i.succ).divX := by
  open WholeIntervalPolynomial.Certificate in
  fin_cases i
  · apply initial_cert ?ha d 4 15 (by norm_num) (by norm_num) 35 (893/500000) 893 500000
      (by norm_num [rectangleInitialReserve]) (by norm_num) (7/100) 7 100
      (by norm_num [rectangleSlopeReserve]) (by norm_num)
    case' ha =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle 1)
      r80_unfold
      build_rep
    decide_all
  · apply initial_cert ?ha₁ d 4 15 (by norm_num) (by norm_num) 35 (149/500) 149 500
      (by norm_num [rectangleInitialReserve]) (by norm_num) (199/100) 199 100
      (by norm_num [rectangleSlopeReserve]) (by norm_num)
    case' ha₁ =>
      simp only [rectangleBase,baseX_eq_xZero]
      change RepOn xZero _ (numerator .rectangle 2)
      r80_unfold
      build_rep
    decide_all

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
