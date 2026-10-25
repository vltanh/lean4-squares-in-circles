module

public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeData
public import SquaresInCircles.Eight.Arithmetic.BivariateRounding

/-! # Eight squares: the three BT3 rectangle-quotient certificates, by rounded packed models of the numerators -/

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

/-- `mass .rectangle i j`, reduced, in the packing `cM`: the cubic mass reads only the truncation
of `P` to total degree three, which is carried over from the packing `cP`. -/
private def bq_massM (cP cM : Config) (i : Fin 3) (j : Fin 4) : XM :=
  XM.reduce cM (XM.cubicMassRM cM (bq_rhoP i j).1 (bq_rhoP i j).2
    (BivariateRounding.repackM cP cM (XM.trunc cP (bq_PM cP i j) 3)))

private theorem bq_rep_massM (cP cM : Config) (i : Fin 3) (j : Fin 4) :
    (bq_massM cP cM i j).Rep cM (mass .rectangle i j) := by
  have e : mass .rectangle i j = cubicMass (rho i j) (P .rectangle i j) := by simp [mass]
  have h := XM.rep_cubicMassRM (BivariateRounding.rep_repackM (c' := cM)
    (XM.rep_trunc (bq_rep_PM cP i j) 3)) (bq_rho_eq i j)
  rw [BivariateRounding.cubicMass_truncTot] at h
  rw [e]
  exact XM.rep_reduce h

open BivariateRounding in
/-- `numerator .rectangle i`, rounded to the scale `2 ^ K` in the packing `cE`: `A`, `P` and the
masses are exact in their packings, the products are rounded; the smaller factor is on the right. -/
private def bq_numE (cP cM cE : Config) (K : ℕ) (i : Fin 3) : XE :=
  let w := fun j => XE.ofXMAt cM cE K (bq_massM cP cM i j)
  let P := fun j => XE.ofXMAt cP cE K (bq_PM cP i j)
  let mr := XE.mulR cE K
  XE.sub cE (mr (mr (mr (mr (mr (XE.ofXMAt cP cE K (bq_AM cP i))
      (XE.ofXMAt cP cE K (XM.ofInt cP 2 1))) (w 0)) (w 1)) (w 2)) (w 3))
    (mr (XE.add cE (XE.add cE (XE.add cE
      (mr (mr (mr (XE.add cE (P 0) (mr (w 0) (w 0))) (w 1)) (w 2)) (w 3))
      (mr (mr (mr (XE.add cE (P 1) (mr (w 1) (w 1))) (w 0)) (w 2)) (w 3)))
      (mr (mr (mr (XE.add cE (P 2) (mr (w 2) (w 2))) (w 0)) (w 1)) (w 3)))
      (mr (mr (mr (XE.add cE (P 3) (mr (w 3) (w 3))) (w 0)) (w 1)) (w 2)))
      (XE.ofXMAt cP cE K (XM.ofInt cP 494696877 250000000)))

open BivariateRounding in
private theorem bq_rep_numE (cP cM cE : Config) (K : ℕ) (i : Fin 3) :
    (bq_numE cP cM cE K i).Rep cE (numerator .rectangle i) := by
  have hw (j : Fin 4) := XE.rep_ofXMAt (c' := cE) (bq_rep_massM cP cM i j) K
  have hP (j : Fin 4) := XE.rep_ofXMAt (c' := cE) (bq_rep_PM cP i j) K
  have hs (j : Fin 4) : (XE.mulR cE K (XE.ofXMAt cM cE K (bq_massM cP cM i j))
      (XE.ofXMAt cM cE K (bq_massM cP cM i j))).Rep cE (mass .rectangle i j ^ 2) := by
    rw [pow_two]; exact XE.rep_mulR (hw j) (hw j) K
  exact XE.rep_sub (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR_swap
      (XE.rep_ofXMAt (XM.rep_lit cP (by norm_num)) K) (XE.rep_ofXMAt (bq_rep_AM cP i) K) K)
      (hw 0) K) (hw 1) K) (hw 2) K) (hw 3) K)
    (XE.rep_mulR_swap (XE.rep_ofXMAt (XM.rep_lit cP (by norm_num [NonnegativeTotals.Certificate.Rbar])) K)
      (XE.rep_add (XE.rep_add (XE.rep_add
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 0) (hs 0)) (hw 1) K) (hw 2) K) (hw 3) K)
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 1) (hs 1)) (hw 0) K) (hw 2) K) (hw 3) K))
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 2) (hs 2)) (hw 0) K) (hw 1) K) (hw 3) K))
      (XE.rep_mulR (XE.rep_mulR (XE.rep_mulR (XE.rep_add (hP 3) (hs 3)) (hw 0) K) (hw 1) K) (hw 2) K))
      K)

end Mirrors

/-! ### The three checks

`A` and `P` are exact in boxes of `37 × 37` digits of 170 bits, the masses in digits of 600 bits.
The numerators are rounded models (`BivariateRounding.XE`) at the scale `2 ^ 60` in digits of
160 bits; the quotient by `x`, the substitution onto the rectangle and the final bound use digits
of 400 bits. The error of the rounding enters the final bounds. -/

section Checks
open PackedModels BivariateCertificate BivariateRounding

private def bq_cP : Config := ⟨0, 18, 170⟩
private def bq_cM : Config := ⟨0, 18, 600⟩
private def bq_cE : Config := ⟨0, 18, 160⟩
private def bq_cT : Config := ⟨0, 18, 400⟩

/-- The model of the rectangle transform of the quotient `i`. -/
private def bq_finalE (i : Fin 3) : XE :=
  XE.norm bq_cT (XE.toScale bq_cT bq_cT 60 (XE.rectangle bq_cT 1 6 8 15 (XE.repack bq_cE bq_cT
    (XE.divX bq_cE (bq_numE bq_cP bq_cM bq_cE 60 i)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bq_check_0 : XE.lowerCheck bq_cT (bq_finalE 0) 35 23 500 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bq_check_1 : XE.lowerCheck bq_cT (bq_finalE 1) 35 17 125 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
set_option Elab.async false in
private theorem bq_check_2 : XE.lowerCheck bq_cT (bq_finalE 2) 35 411 1000 = true := by
  decide +kernel

end Checks

theorem rectangle_quotient_certificate (i : Fin 3) :
    transform .rectangle (rectangleQuotient i)=expansion 35
      (transform .rectangle (rectangleQuotient i)) ∧
    rectangleQuotientReserve i<lowerOn .rectangle 35 (rectangleQuotient i) := by
  open BivariateRounding in
  have hm (i : Fin 3) := XE.rep_norm (XE.rep_toScale (c' := bq_cT) (XE.rep_rectangle
    (XE.rep_repack (c' := bq_cT) (XE.rep_divX (bq_rep_numE bq_cP bq_cM bq_cE 60 i)))
    (a := 1/6) (b := 8/15) (an := 1) (ad := 6) (bn := 8) (bd := 15) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)) 60)
  fin_cases i
  · exact XE.lower_certificate (hm 0) bq_check_0 (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (hm 1) bq_check_1 (by norm_num [rectangleQuotientReserve])
  · exact XE.lower_certificate (hm 2) bq_check_2 (by norm_num [rectangleQuotientReserve])

end SquaresInCircles.Eight.GlobalGA.PositiveBT3.LargeCertificate
