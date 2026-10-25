module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData

/-! # Eight squares: the three BT3 rectangle-quotient certificates, by exact packed models of the numerators -/

@[expose] public section
noncomputable section
open Polynomial
namespace SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
open TensorWholeIntervalPolynomial TwoVariablePolynomial NonnegativeTotals
open CertificateRestrictions

/-! ### Exact models of the rectangle numerators

`A`, `baseNorm`, `P`, `rho` and `mass` differ from the nonnegative-total ones (the rotating
coefficient sits at `D`, and `B` keeps the fixed `m`), so they are mirrored here; their parts
`k`, `l`, `m`, `delta`, `rotation` (`M .atT`) and `ABase .atT` are the shared mirrors. -/

section Mirrors
open PackedModels BivariateCertificate NonnegativeTotalsMirrors

/-- `A .rectangle i`, reduced. -/
private def bq_AM (c : Config) (i : Fin 3) : XM :=
  XM.reduce c <| XM.add c (ABaseM c .rectangle .atT)
    (XM.mul c (![XM.ofInt c 1 1, lM c .rectangle, cM c .rectangle] i)
      (XM.sub c (XM.liftM c (deltaM c .rectangle) XM.C10L) (XM.ofInt c 1 1)))

private theorem bq_rep_AM (c : Config) (i : Fin 3) : (bq_AM c i).Rep c (A .rectangle i) := by
  have h1 : (![XM.ofInt c 1 1, lM c .rectangle, cM c .rectangle] i).Rep c
      (![1, l .rectangle, qB .rectangle] i) := by
    fin_cases i
    · exact XM.rep_one c
    · exact rep_lM c .rectangle
    · exact rep_cM c .rectangle
  exact XM.rep_reduce <| XM.rep_add (rep_ABaseM c .rectangle .atT)
    (XM.rep_mul h1 (XM.rep_sub (XM.rep_liftC10 (rep_deltaM c .rectangle)) (XM.rep_one c)))

/-- `baseNorm .rectangle`; `rotation .rectangle` is `M .rectangle .atT`. -/
private def bq_baseNormM (c : Config) : Fin 4 → XM :=
  ![XM.add c (XM.ofInt c 1 1) (XM.pow c (kM c .rectangle) 2),
    XM.add c (XM.pow c (kM c .rectangle) 2) (XM.pow c (lM c .rectangle) 2),
    XM.add c (XM.pow c (lM c .rectangle) 2) (XM.pow c (cM c .rectangle) 2),
    XM.add c (XM.ofInt c 1 1) (XM.pow c (MM c .rectangle .atT) 2)]

/-- `P .rectangle i j`, reduced. -/
private def bq_PM (c : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c <| XM.sub c (bq_baseNormM c j)
    (if j.val = i.val then XM.mul c (XM.mul c (XM.ofInt c 2 1)
        (![kM c .rectangle, XM.mul c (kM c .rectangle) (lM c .rectangle),
          XM.mul c (lM c .rectangle) (cM c .rectangle), XM.ofInt c 0 1] j))
        (XM.liftM c (deltaM c .rectangle) XM.S11L)
      else XM.ofInt c 0 1)

private theorem bq_rep_PM (c : Config) (i : Fin 3) (j : Fin 4) :
    (bq_PM c i j).Rep c (P .rectangle i j) := by
  have hb : (bq_baseNormM c j).Rep c (baseNorm .rectangle j) := by
    fin_cases j
    · exact XM.rep_add (XM.rep_one c) (XM.rep_pow (rep_kM c .rectangle) 2)
    · exact XM.rep_add (XM.rep_pow (rep_kM c .rectangle) 2) (XM.rep_pow (rep_lM c .rectangle) 2)
    · exact XM.rep_add (XM.rep_pow (rep_lM c .rectangle) 2) (XM.rep_pow (rep_cM c .rectangle) 2)
    · exact XM.rep_add (XM.rep_one c) (XM.rep_pow (rep_MM c .rectangle .atT) 2)
  have hf : (![kM c .rectangle, XM.mul c (kM c .rectangle) (lM c .rectangle),
      XM.mul c (lM c .rectangle) (cM c .rectangle), XM.ofInt c 0 1] j).Rep c
      (![k .rectangle, k .rectangle * l .rectangle, l .rectangle * m .rectangle, 0] j) := by
    fin_cases j
    · exact rep_kM c .rectangle
    · exact XM.rep_mul (rep_kM c .rectangle) (rep_lM c .rectangle)
    · exact XM.rep_mul (rep_lM c .rectangle) (rep_cM c .rectangle)
    · exact XM.rep_zero c
  unfold bq_PM P
  apply XM.rep_reduce
  split_ifs
  · exact XM.rep_sub hb (XM.rep_mul (XM.rep_mul (XM.rep_lit c (by norm_num)) hf)
      (XM.rep_liftS11 (rep_deltaM c .rectangle)))
  · exact XM.rep_sub hb (XM.rep_zero c)

/-- `rho i j` as a numerator and a denominator. -/
private def bq_rhoP (i : Fin 3) (j : Fin 4) : ℤ × ℕ :=
  if j.val = i.val then
    if j = 2 then (81386069, 62500000) else (27678887, 25000000)
  else if j = 2 then (142578599, 100000000)
  else if j = 3 then (1451171531, 1000000000)
  else (150407189, 125000000)

private theorem bq_rho_eq (i : Fin 3) (j : Fin 4) :
    rho i j = ((bq_rhoP i j).1 : ℚ) / (bq_rhoP i j).2 := by
  unfold rho bq_rhoP
  split_ifs <;> norm_num

/-- `mass .rectangle i j`, reduced. -/
private def bq_massM (c : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce c (XM.cubicMassRM c (bq_rhoP i j).1 (bq_rhoP i j).2 (bq_PM c i j))

private theorem bq_rep_massM (c : Config) (i : Fin 3) (j : Fin 4) :
    (bq_massM c i j).Rep c (mass .rectangle i j) := by
  have e : mass .rectangle i j = cubicMass (rho i j) (P .rectangle i j) := by simp [mass]
  rw [e]
  exact XM.rep_reduce (XM.rep_cubicMassRM (bq_rep_PM c i j) (bq_rho_eq i j))

/-- `numerator .rectangle i`, reduced. -/
private def bq_numM (c : Config) (i : Fin 3) : XM :=
  let w := bq_massM c i
  XM.reduce c <| XM.sub c (XM.mul c (XM.mul c (XM.mul c (XM.mul c (XM.mul c (XM.ofInt c 2 1)
      (bq_AM c i)) (w 0)) (w 1)) (w 2)) (w 3))
    (XM.mul c (XM.ofInt c 494696877 250000000) (XM.add c (XM.add c (XM.add c
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bq_PM c i 0) (XM.pow c (w 0) 2)) (w 1))
        (w 2)) (w 3))
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bq_PM c i 1) (XM.pow c (w 1) 2)) (w 0))
        (w 2)) (w 3)))
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bq_PM c i 2) (XM.pow c (w 2) 2)) (w 0))
        (w 1)) (w 3)))
      (XM.mul c (XM.mul c (XM.mul c (XM.add c (bq_PM c i 3) (XM.pow c (w 3) 2)) (w 0))
        (w 1)) (w 2))))

private theorem bq_rep_numM (c : Config) (i : Fin 3) :
    (bq_numM c i).Rep c (numerator .rectangle i) := by
  have hw (j : Fin 4) := bq_rep_massM c i j
  have hP (j : Fin 4) := bq_rep_PM c i j
  exact XM.rep_reduce <| XM.rep_sub (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul (XM.rep_mul
      (XM.rep_lit c (by norm_num)) (bq_rep_AM c i)) (hw 0)) (hw 1)) (hw 2)) (hw 3))
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

The rectangle transform of the quotient by `x` is packed in a box of `37 × 37` digits of
`2160` bits (the largest digit sum on the way has `2143` bits). -/

section Checks
open PackedModels BivariateCertificate

private def bq_cfg : Config := ⟨0, 18, 2160⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bq_check_0 : XM.lowerCheck bq_cfg (XM.reduce bq_cfg (XM.rectangleM bq_cfg
    (XM.divXM bq_cfg (bq_numM bq_cfg 0)) 1 6 8 15)) 35 23 500 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bq_check_1 : XM.lowerCheck bq_cfg (XM.reduce bq_cfg (XM.rectangleM bq_cfg
    (XM.divXM bq_cfg (bq_numM bq_cfg 1)) 1 6 8 15)) 35 17 125 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bq_check_2 : XM.lowerCheck bq_cfg (XM.reduce bq_cfg (XM.rectangleM bq_cfg
    (XM.divXM bq_cfg (bq_numM bq_cfg 2)) 1 6 8 15)) 35 411 1000 = true := by
  decide +kernel

end Checks

theorem rectangle_quotient_certificate (i : Fin 3) :
    transform .rectangle (rectangleQuotient i)=expansion 35
      (transform .rectangle (rectangleQuotient i)) ∧
    rectangleQuotientReserve i<lowerOn .rectangle 35 (rectangleQuotient i) := by
  open BivariateCertificate in
  have hm (i : Fin 3) := XM.rep_reduce (XM.rep_rectangleM (XM.rep_divXM (bq_rep_numM bq_cfg i))
    (a := 1/6) (b := 8/15) (an := 1) (ad := 6) (bn := 8) (bd := 15) (by norm_num) (by norm_num))
  fin_cases i
  · exact XM.lower_certificate (hm 0) bq_check_0 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (hm 1) bq_check_1 (by norm_num [rectangleQuotientReserve])
  · exact XM.lower_certificate (hm 2) bq_check_2 (by norm_num [rectangleQuotientReserve])

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
