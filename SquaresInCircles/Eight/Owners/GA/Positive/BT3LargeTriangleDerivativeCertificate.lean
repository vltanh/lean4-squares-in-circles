module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData

/-! # Eight squares: `triangle_derivative_certificate`: the three triangle `y`-derivatives, by exact packed models -/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals
open CertificateRestrictions

/-! ### Exact models of the triangle numerators

On the triangle, `A` is the nonnegative-total `A .triangle .atT` (both endpoints have
`qB .triangle = qStar .triangle`). `baseNorm`, `P`, `rho` and `mass` differ from the
nonnegative-total ones (the rotating coefficient sits at `D`, `B` keeps the fixed `m`, and the
G curve carries opposite cubic corrections), so they are mirrored here from the shared mirrors
of `k`, `l`, `m`, `delta` and `rotation` (`M .atT`). -/

section Mirrors
open PackedModels BivariateCertificate NonnegativeTotalsMirrors

/-- `A .triangle i`, reduced. -/
private def bd_AM (c : Config) (i : Fin 3) : XM := XM.reduce c (AM c .triangle .atT i)

private theorem bd_rep_AM (c : Config) (i : Fin 3) : (bd_AM c i).Rep c (A .triangle i) :=
  XM.rep_reduce (rep_AM c .triangle .atT i)

/-- `baseNorm .triangle`; `rotation .triangle` is `M .triangle .atT`. -/
private def bd_baseNormM (c : Config) : Fin 4 → XM :=
  ![XM.add c (XM.ofInt c 1 1) (XM.pow c (kM c .triangle) 2),
    XM.add c (XM.pow c (kM c .triangle) 2) (XM.pow c (lM c .triangle) 2),
    XM.add c (XM.pow c (lM c .triangle) 2) (XM.pow c (cM c .triangle) 2),
    XM.add c (XM.ofInt c 1 1) (XM.pow c (MM c .triangle .atT) 2)]

/-- `P .triangle i j`, reduced. -/
private def bd_PM (c : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c <| XM.sub c (bd_baseNormM c j)
    (if j.val = i.val then XM.mul c (XM.mul c (XM.ofInt c 2 1)
        (![kM c .triangle, XM.mul c (kM c .triangle) (lM c .triangle),
          XM.mul c (lM c .triangle) (cM c .triangle), XM.ofInt c 0 1] j))
        (XM.liftM c (deltaM c .triangle) XM.S11L)
      else XM.ofInt c 0 1)

private theorem bd_rep_PM (c : Config) (i : Fin 3) (j : Fin 4) :
    (bd_PM c i j).Rep c (P .triangle i j) := by
  have hb : (bd_baseNormM c j).Rep c (baseNorm .triangle j) := by
    fin_cases j
    · exact XM.rep_add (XM.rep_one c) (XM.rep_pow (rep_kM c .triangle) 2)
    · exact XM.rep_add (XM.rep_pow (rep_kM c .triangle) 2) (XM.rep_pow (rep_lM c .triangle) 2)
    · exact XM.rep_add (XM.rep_pow (rep_lM c .triangle) 2) (XM.rep_pow (rep_cM c .triangle) 2)
    · exact XM.rep_add (XM.rep_one c) (XM.rep_pow (rep_MM c .triangle .atT) 2)
  have hf : (![kM c .triangle, XM.mul c (kM c .triangle) (lM c .triangle),
      XM.mul c (lM c .triangle) (cM c .triangle), XM.ofInt c 0 1] j).Rep c
      (![k .triangle, k .triangle * l .triangle, l .triangle * m .triangle, 0] j) := by
    fin_cases j
    · exact rep_kM c .triangle
    · exact XM.rep_mul (rep_kM c .triangle) (rep_lM c .triangle)
    · exact XM.rep_mul (rep_lM c .triangle) (rep_cM c .triangle)
    · exact XM.rep_zero c
  unfold bd_PM P
  apply XM.rep_reduce
  split_ifs
  · exact XM.rep_sub hb (XM.rep_mul (XM.rep_mul (XM.rep_lit c (by norm_num)) hf)
      (XM.rep_liftS11 (rep_deltaM c .triangle)))
  · exact XM.rep_sub hb (XM.rep_zero c)

/-- `rho i j` as a numerator and a denominator. -/
private def bd_rhoP (i : Fin 3) (j : Fin 4) : ℤ × ℕ :=
  if j.val = i.val then
    if j = 2 then (81386069, 62500000) else (27678887, 25000000)
  else if j = 2 then (142578599, 100000000)
  else if j = 3 then (1451171531, 1000000000)
  else (150407189, 125000000)

private theorem bd_rho_eq (i : Fin 3) (j : Fin 4) :
    rho i j = ((bd_rhoP i j).1 : ℚ) / (bd_rhoP i j).2 := by
  unfold rho bd_rhoP
  split_ifs <;> norm_num

/-- The opposite cubic corrections of `mass` on the triangle G curve. -/
private def bd_corrM (c : Config) (r : Region) (i : Fin 3) (j : Fin 4) : XM :=
  if r = .triangle ∧ i = 1 then
    if j = 1 then XM.mul c (XM.neg (XM.ofInt c 1 4)) (XM.pow c (XM.varX c) 3)
    else if j = 3 then XM.mul c (XM.ofInt c 1 4) (XM.pow c (XM.varX c) 3) else XM.ofInt c 0 1
  else XM.ofInt c 0 1

/-- `mass .triangle i j`, reduced. -/
private def bd_massM (c : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c (XM.add c (XM.cubicMassRM c (bd_rhoP i j).1 (bd_rhoP i j).2 (bd_PM c i j))
    (bd_corrM c .triangle i j))

private theorem bd_rep_massM (c : Config) (i : Fin 3) (j : Fin 4) :
    (bd_massM c i j).Rep c (mass .triangle i j) :=
  XM.rep_reduce (XM.rep_add (XM.rep_cubicMassRM (bd_rep_PM c i j) (bd_rho_eq i j))
    (XM.rep_ite (XM.rep_ite (XM.rep_mul (XM.rep_neg (XM.rep_lit c (by norm_num)))
      (XM.rep_pow (XM.rep_X c) 3)) (XM.rep_ite (XM.rep_mul (XM.rep_lit c (by norm_num))
      (XM.rep_pow (XM.rep_X c) 3)) (XM.rep_zero c))) (XM.rep_zero c)))

/-- `numerator .triangle i`, reduced. -/
private def bd_numM (c : Config) (i : Fin 3) : XM :=
  let w := bd_massM c i
  XM.reduce c <| XM.sub c (XM.mul c (XM.mul c (XM.mul c (XM.mul c (XM.mul c (XM.ofInt c 2 1)
      (bd_AM c i)) (w 0)) (w 1)) (w 2)) (w 3))
    (XM.mul c (XM.ofInt c 494696877 250000000) (XM.add c (XM.add c (XM.add c
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bd_PM c i 0) (XM.pow c (w 0) 2)) (w 1))
        (w 2)) (w 3))
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bd_PM c i 1) (XM.pow c (w 1) 2)) (w 0))
        (w 2)) (w 3)))
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bd_PM c i 2) (XM.pow c (w 2) 2)) (w 0))
        (w 1)) (w 3)))
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bd_PM c i 3) (XM.pow c (w 3) 2)) (w 0))
        (w 1)) (w 2))))

private theorem bd_rep_numM (c : Config) (i : Fin 3) :
    (bd_numM c i).Rep c (numerator .triangle i) := by
  have hw (j : Fin 4) := bd_rep_massM c i j
  have hP (j : Fin 4) := bd_rep_PM c i j
  exact XM.rep_reduce <| XM.rep_sub (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul
      (XM.rep_lit c (by norm_num)) (bd_rep_AM c i)) (hw 0)) (hw 1)) (hw 2)) (hw 3))
    (XM.rep_mul (XM.rep_lit c (by norm_num [NonnegativeTotals.Certificate.Rbar]))
      (XM.rep_add (XM.rep_add (XM.rep_add
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 0) (XM.rep_pow (hw 0) 2)) (hw 1))
        (hw 2)) (hw 3))
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 1) (XM.rep_pow (hw 1) 2)) (hw 0))
        (hw 2)) (hw 3)))
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 2) (XM.rep_pow (hw 2) 2)) (hw 0))
        (hw 1)) (hw 3)))
      (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_add (hP 3) (XM.rep_pow (hw 3) 2)) (hw 0))
        (hw 1)) (hw 2))))

end Mirrors

/-! ### The three checks

All models are packed in boxes of `41 × 41` digits (the numerators have degree `39` in `x`) of
`2208` bits. The largest digit-sum bound on the way has `2191` bits, in the last substitution
`y ↦ (1 + y) / 2` of `triangleM`; the reduced final model has a digit sum of `1994` bits, so
`16 ^ 40` times it stays below `2 ^ 2206`. -/

section Checks
open PackedModels BivariateCertificate

private def bd_cfg : Config := ⟨0, 20, 2208⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bd_check_0 : XM.upperCheck bd_cfg (XM.reduce bd_cfg (XM.triangleM bd_cfg
    (XM.reduce bd_cfg (XM.derivYM bd_cfg (XM.divYM bd_cfg (bd_numM bd_cfg 0)))) 8 15))
    39 (-231) 1000 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bd_check_1 : XM.upperCheck bd_cfg (XM.reduce bd_cfg (XM.triangleM bd_cfg
    (XM.reduce bd_cfg (XM.derivYM bd_cfg (XM.divYM bd_cfg (bd_numM bd_cfg 1)))) 8 15))
    39 (-21) 50 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bd_check_2 : XM.upperCheck bd_cfg (XM.reduce bd_cfg (XM.triangleM bd_cfg
    (XM.reduce bd_cfg (XM.derivYM bd_cfg (XM.divYM bd_cfg (bd_numM bd_cfg 2)))) 8 15))
    39 (-119) 500 = true := by
  decide +kernel

end Checks

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem triangle_derivative_certificate (i : Fin 3) :
    transform .triangle (derivativeY (triangleQuotient i))=
      expansion 39 (transform .triangle (derivativeY (triangleQuotient i))) ∧
    upperOn .triangle 39 (derivativeY (triangleQuotient i))<triangleDerivativeReserve i := by
  open BivariateCertificate in
  have hm (i : Fin 3) := XM.rep_reduce (XM.rep_triangleM (XM.rep_reduce (XM.rep_derivYM
    (XM.rep_divYM (bd_rep_numM bd_cfg i)))) (d := 8/15) (dn := 8) (dd := 15) (by norm_num))
  fin_cases i
  · exact XM.upper_certificate (hm 0) bd_check_0 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (hm 1) bd_check_1 (by norm_num [triangleDerivativeReserve])
  · exact XM.upper_certificate (hm 2) bd_check_2 (by norm_num [triangleDerivativeReserve])

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
